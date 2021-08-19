From mathcomp Require Import all_ssreflect all_algebra.
Require Import definitions.

Set Implicit Arguments.
Unset Strict Implicit.

(* As in insertion sort, the add_event function assumes that event are
  sorted in evs (lexicographically, first coordinate, then second coordinate
  of the point.  On the other hand, no effort is made to sort the various
  edges in each list.  *)
  Fixpoint add_event (p : pt) (e : edge) (inc : bool) (evs : seq event) :
  seq event :=
  match evs with
  | nil => if inc then [:: Bevent p [::]]
           else [:: Bevent p [:: e]]
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if p == p1 then
      if inc then Bevent p1 (outgoing ev1) :: evs'
      else Bevent p1 (e :: outgoing ev1) :: evs' else
    if p_x p < p_x p1 then
      if inc then
        Bevent p [::] :: evs else
        Bevent p [:: e] :: evs
    else if (p_x p == p_x p1) && (p_y p < p_y p1) then
       if inc then
         Bevent p [::] :: evs else
         Bevent p [:: e] :: evs else
    ev1 :: add_event p e inc evs'
  end.

(* We should be able to prove that the sequence of events produced by
  edges to events is sorted lexicographically on the coordinates of
  the points. *)
Fixpoint edges_to_events (s : seq edge) : seq event :=
  match s with
  | nil => nil
  | e :: s' =>
    add_event (left_pt e) e false
      (add_event (right_pt e) e true (edges_to_events s'))
  end.
Definition vertical_intersection_point (p : pt) (e : edge) : option pt :=

    if valid_edge e p then Some(Bpt (p_x p) (((p_x p) - p_x (left_pt e))
     * (((p_y (right_pt e)) - p_y (left_pt e)) /
      ((p_x (right_pt e)) - p_x (left_pt e))) + p_y (left_pt e)))
      else None.

      
(* this function removes consecutives duplicates, meaning the seq needs to be sorted first if we want to remove all duplicates *)
Fixpoint no_dup_seq (A : eqType) (s : seq A) : (seq A) :=
  match s with
  | [::] => [::]
  | a::q => match q with
            | [::] => s
            | b::r => if a == b then no_dup_seq q else a::(no_dup_seq q)
            end
    end.

Fixpoint closing_rest (p: pt) (rest : seq cell) : (seq cell) :=
    match rest with
       | [::] => [::]
       | [:: c] => let op1 := vertical_intersection_point p (high c) in
                    match op1 with
                       | None => [::]
                       | Some(p1) =>
                        Bcell  (left_pts c) (no_dup_seq [:: p; p1]) (low c) (high c)::[::]
                    end
       | c::q =>  Bcell  (left_pts c) [::p] (low c) (high c)::closing_rest p q
    end.


Definition closing_cells (p : pt) (contact_cells: seq cell) : (seq cell) :=
    match contact_cells with
      | [::] => [::]
      | [:: only_cell] =>
                      let op0 := vertical_intersection_point p (low only_cell) in
                      let op1 := vertical_intersection_point p (high only_cell) in
                      match (op0,op1) with
                          |(None,_) |(_,None)=> [::]
                          |(Some(p0),Some(p1)) =>
                              Bcell  (left_pts only_cell) (no_dup_seq [:: p0; p; p1])(low only_cell) (high only_cell)::[::]
                      end
      | c::q => let op0 := vertical_intersection_point p (low c) in
                    match op0 with
                       | None => [::]
                       | Some(p0) =>
                        Bcell  (left_pts c) (no_dup_seq [:: p0; p]) (low c) (high c) :: (closing_rest p q)
                    end
    end.


Fixpoint open_cells_decomposition_contact open_cells pt contact high_e : seq cell * seq cell * edge :=
match open_cells with
        | [::] => (contact, [::], high_e)
        | Bcell lpt rpt low high :: q  =>
                if (contains_point pt (Bcell lpt rpt low high)) then
                    open_cells_decomposition_contact q pt (rcons contact (Bcell lpt rpt low high)) high
                else (contact, open_cells, high_e)
        end.

Fixpoint open_cells_decomposition_fix open_cells pt first_cells : seq cell * seq cell * seq cell * edge * edge :=

match open_cells with
        | [::] => (first_cells, [::], [::], dummy_edge, dummy_edge)
        | Bcell lpt rpt low high :: q  =>
            if (contains_point pt (Bcell lpt rpt low high)) then
                   let '(contact, last_cells, high_e) := open_cells_decomposition_contact q pt [::] high in
                   (first_cells, (Bcell lpt rpt low high)::contact,last_cells, low, high_e)
            else open_cells_decomposition_fix q pt (rcons first_cells ( Bcell lpt rpt low high))
end.

(* only works if cells are sorted *)
Definition open_cells_decomposition (open_cells : seq cell) (p : pt) : seq cell * seq cell * seq cell * edge * edge :=
  match open_cells with
    | [::] => ([::],[::],[::], dummy_edge, dummy_edge)
    | _  => open_cells_decomposition_fix open_cells p [::]
  end.

(* at each step we create the cell under the first outgoing edge and when there's only one left,
we create the two last cells *)
Fixpoint opening_cells (p : pt) (out : seq edge) (low_e : edge) (high_e : edge) : (seq cell) :=

    match out with
  | [::] => let op0 := vertical_intersection_point p low_e in
            let op1 := vertical_intersection_point p high_e in
                    match (op0,op1) with
                        |(None,_) |(_,None)=> [::]
                        |(Some(p0),Some(p1)) =>
                            (Bcell  (no_dup_seq ([:: p1; p; p0])) [::] low_e high_e) ::[::]
                    end
  | c::q => let op0 := vertical_intersection_point p low_e in
                  match op0 with
                     | None => [::]
                     | Some(p0) =>
                      (Bcell  (no_dup_seq([:: p; p0])) [::] low_e c) :: opening_cells p q c high_e
                  end
end.

Definition step (e : event) (open_cells : seq cell) (closed_cells : seq cell) : (seq cell) * (seq cell) :=
   let p := point e in
   let '(first_cells, contact_cells, last_cells, lower_edge, higher_edge) := open_cells_decomposition open_cells p in
  (* let (lower_edge, higher_edge) := extract_l_h_edges contact_cells in *)
   let closed := closing_cells p contact_cells in
   let closed_cells := closed_cells++closed in
   let new_open_cells :=
     opening_cells p (sort edge_below (outgoing e)) lower_edge higher_edge in
   (first_cells++new_open_cells++last_cells, closed_cells).

Fixpoint scan (events : seq event) (open_cells : seq cell) (closed_cells : seq cell) : seq cell :=
    match events with
       | [::] => closed_cells
       | e::q => let (open, closed) := (step e open_cells closed_cells) in  scan q open closed
  end.

Definition start (events : seq event) (bottom : edge) (top : edge) : seq cell :=
match events with
| [::] => [::]
| e :: q =>
    let p := point e in let out := outgoing e in
    scan q (opening_cells p out bottom top) [::]
end.