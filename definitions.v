From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Record pt := Bpt {p_x : rat; p_y : rat}.

Definition pt_eqb (a b : pt) : bool :=
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
     (a_x == b_x) && (a_y == b_y).

Lemma pt_eqP : Equality.axiom pt_eqb.
Proof.
rewrite /Equality.axiom.
move=> [a_x a_y] [b_x b_y] /=.
have [/eqP <-|/eqP anb] := boolP(a_x == b_x).

  have [/eqP <- | /eqP anb] := boolP(a_y == b_y).
    by apply: ReflectT.
  by apply : ReflectF => [][].
by apply: ReflectF=> [][].
Qed.

Canonical pt_eqType := EqType pt (EqMixin pt_eqP).

Record edge := Bedge {left_pt : pt; right_pt : pt;
    _ : p_x left_pt < p_x right_pt}.

Definition edge_eqb (e1 e2 : edge) : bool :=
   let: Bedge a1 b1 p1 := e1 in
   let: Bedge a2 b2 p2 := e2 in
   (a1 == a2) && (b1 == b2).

Lemma edge_cond (e : edge) : p_x (left_pt e) < p_x (right_pt e).
Proof.  by move: e => [l r c]. Qed.

Lemma edge_eqP : Equality.axiom edge_eqb.
Proof.
move=> [a1 b1 p1] [a2 b2 p2] /=.
have [/eqP a1a2 | /eqP a1na2] := boolP(a1 == a2).
  have [/eqP b1b2 | /eqP b1nb2] := boolP(b1 == b2).
     move: p1 p2. rewrite -a1a2 -b1b2 => p1 p2.
     rewrite (eqtype.bool_irrelevance p1 p2).
     by apply: ReflectT.
   by apply: ReflectF=> [][].
by apply: ReflectF=>[][].
Qed.

Canonical edge_eqType := EqType edge (EqMixin edge_eqP).

Record cell := Bcell  {left_pts : list pt; right_pts : list pt; low : edge; high : edge}.

Definition cell_eqb (ca cb : cell) : bool :=
  let: Bcell lptsa rptsa lowa higha := ca in
  let: Bcell lptsb rptsb lowb highb:= cb in
  (lptsa == lptsb) && (rptsa == rptsb) && (lowa == lowb) && (higha == highb).


Lemma cell_eqP : Equality.axiom cell_eqb.
Proof.
rewrite /Equality.axiom.
move => [lptsa rptsa lowa higha] [lptsb rptsb lowb highb] /=.
have [/eqP <-|/eqP anb] := boolP(lptsa == lptsb).
  have [/eqP <-|/eqP anb] := boolP(rptsa == rptsb).
    have [/eqP <-|/eqP anb] := boolP(lowa == lowb).
      have [/eqP <-|/eqP anb] := boolP(higha == highb).
        by apply:ReflectT.
      by apply : ReflectF => [][].
    by apply : ReflectF => [][].
  by apply: ReflectF=> [][].
by apply: ReflectF=> [][].
Qed.

Canonical cell_eqType := EqType cell (EqMixin cell_eqP).

Record event := Bevent {point : pt; outgoing : seq edge}.

Definition event_eqb (ea eb : event) : bool :=
  let: Bevent pta outa := ea in
  let: Bevent ptb outb := eb in
  (pta == ptb) && (outa == outb).

Lemma event_eqP : Equality.axiom event_eqb.
Proof.
rewrite /Equality.axiom.
move => [pta outa] [ptb outb] /=.
have [/eqP <-|/eqP anb] := boolP(pta == ptb).
  have [/eqP <-|/eqP anb] := boolP(outa == outb).
    by apply:ReflectT.
  by apply : ReflectF => [][].
by apply: ReflectF=> [][].
Qed.

Canonical event_eqType := EqType event (EqMixin event_eqP).


Definition dummy_pt := Bpt 0%:Q 0%:Q.
Definition dummy_event := Bevent dummy_pt [::].
Definition dummy_edge : edge := (@Bedge  dummy_pt (Bpt 1%:Q 0%:Q) isT).
Definition dummy_cell : cell := (@Bcell  (dummy_pt::[::]) (dummy_pt::[::]) dummy_edge dummy_edge).


(* returns true if p is under A B *)
Definition pue_formula (p : pt) (a : pt) (b : pt) : rat :=
  let: Bpt p_x p_y := p in
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
     (b_x * p_y - p_x * b_y - (a_x * p_y - p_x * a_y) + a_x * b_y - b_x * a_y).


(* returns true if p is under e *)
Definition point_under_edge (p : pt) (e : edge) : bool :=
  pue_formula p (left_pt e) (right_pt e) <= 0.

  (* returns true if p is strictly under e *)
Definition point_strictly_under_edge (p : pt) (e : edge) : bool :=
  pue_formula p (left_pt e) (right_pt e) < 0.

Notation "p '<<=' e" := (point_under_edge p e)( at level 70, no associativity).
Notation "p '<<<' e" := (point_strictly_under_edge p e)(at level 70, no associativity).


Definition subpoint (p : pt) :=
  {| p_x := p_x p; p_y := p_y p - 1 |}.

Definition valid_edge e p := (p_x (left_pt e) <= p_x p) && (p_x p <= p_x (right_pt e)).

Definition valid_cell c x := (valid_edge (low c) x) /\ (valid_edge (high c) x).



Definition point_on_edge (p: pt) (e :edge) : bool :=
  (pue_formula p (left_pt e) (right_pt e) == 0) && (valid_edge e p).

Notation "p '===' e" := (point_on_edge p e)( at level 70, no associativity).

Definition edge_below (e1 : edge) (e2 : edge) : bool :=
((left_pt e1 <<= e2) && (right_pt e1 <<= e2))
|| (~~  (left_pt e2 <<< e1) && ~~ (right_pt e2<<< e1)).

Definition below_alt (e1 : edge) (e2 : edge) :=
  edge_below e1 e2 \/ edge_below e2 e1.

Definition no_crossing := forall e1 e2, below_alt e1 e2.

Notation "e1 '<|' e2" := (edge_below e1 e2)( at level 70, no associativity).

Definition right_form (c : cell) : bool :=
  (low c) <| (high c).

  (* if a cell doesn't contain a point, then either both edges are strictly under p or strictly over p *)

Definition contains_point (p : pt) (c : cell)  : bool :=
   ~~  (p <<< low c) && (p <<= (high c)).

Definition inside_open_cell p c :=
  contains_point p c && (p_x (last dummy_pt (left_pts c)) <= p_x p).

Definition inside_closed_cell p c :=
  contains_point p c && (p_x (last dummy_pt (left_pts c)) <= p_x p) && ( p_x p <= p_x (last dummy_pt (right_pts c))).


Definition lexPt (p1 p2 : pt) : bool :=
  (p_x p1 < p_x p2) || ((p_x p1 == p_x p2) && (p_y p1 < p_y p2)).

Definition lexePt (p1 p2 : pt) : bool :=
    (p_x p1 < p_x p2) || ((p_x p1 == p_x p2) && (p_y p1 <= p_y p2)).

Definition lexPtEv (e1 e2 : event) : bool :=
  lexPt (point e1) (point e2).

  Definition event_close_edge ed ev : bool :=
  right_pt ed == point ev.

Definition s_right_form (s : seq cell)  : bool :=
    all (fun c => right_form c ) s.
  
Definition seq_valid (s : seq cell) (p : pt) : bool :=
      all (fun c => (valid_edge (low c) p) && (valid_edge (high c) p)) s.
  

Definition out_left_event ev :=
    forall e,
    e \in (outgoing ev) -> left_pt e == point(ev).

Definition adj_rel := [rel x y : cell | high x == low y].

Fixpoint adjacent_cells_aux open e : bool :=
  match open with
  | [::] => true
  | a::q => (e == low a) && adjacent_cells_aux q (high a)
  end.

Definition adjacent_cells open : bool :=
  match open with
  | [::] => true
  | b::q => adjacent_cells_aux q (high b)
  end.

Lemma adj_aux_path (x : cell) s :
    adjacent_cells_aux s (high x) = path adj_rel x s.
Proof.
by elim: s x => [// | y s Ih] x /=; rewrite Ih.
Qed.

Definition adjacent_cells' open : bool :=
    sorted adj_rel open.


Definition no_crossing'  : Prop:=
 forall e e',
 valid_edge e (left_pt e') ->
(left_pt e' <<< e  -> e' <| e)  /\
(~ (left_pt e' <<= e)  -> e <| e').