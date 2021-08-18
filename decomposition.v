From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Import GRing.Theory Num.Theory.
Require Import cells.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.
Section proof_environment.
Variable bottom top : edge.

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


Lemma h_c_contact open_cells pt high_e contact_cells :
forall contact last_c high_c,
open_cells_decomposition_contact open_cells pt contact_cells high_e =(contact,last_c, high_c) ->
((high (last dummy_cell contact) == high_c) && (contact != nil)) || ((contact == contact_cells) && (high_e == high_c)).
Proof.
elim : open_cells contact_cells high_e => [//= | c open Ih] contact_cells high_e contact_c last_c high_c.
  move => H.
  inversion H.
  by rewrite ! eqxx orbT.
rewrite /=.
case : c => [lpts rpts lowc highc].
case : ifP => [contain| notcontain].
  case h : (open_cells_decomposition_contact _ _ _ _) => [[contact lc]high_final].
  move : (Ih _ _ _ _ _ h).
  move =>  /orP [ /andP [] /eqP <-// cnnil|].
    move => [] <- Hlc -> .
    by rewrite eqxx cnnil.
  move  => /andP [/eqP tmp2 /eqP tmp3].
  move => [] <- Hlc Hhc .
  rewrite tmp2 .
  rewrite last_rcons /=  tmp3 Hhc eqxx andTb .
  apply /orP; left.
  apply /eqP /rcons_neq0.
move => [] -> _ -> .
by rewrite !eqxx orbT.
Qed.

Lemma l_h_c_fix open_cells pt fc:
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition_fix open_cells pt fc = (first_cells, contact, last_cells, low_f, high_f)   ->
(exists c, (c \in open_cells) /\ (contains_point pt c)) ->
(low (head dummy_cell contact) == low_f) /\ (high (last dummy_cell contact) == high_f) /\ contact != nil.
Proof.
  move => f_c c_c l_c lowf highf.
rewrite /=.
elim : open_cells fc => [/= | c q IH] fc.
  move =>   _ /= [] x.
   rewrite in_nil.
   move => /andP.
   by rewrite andFb.

rewrite /=.
case : c => [lpts rpts lowfi highfi].
case : ifP => [contain |notcontain].

  case h : (open_cells_decomposition_contact _ _ _ _) => [[contact last_c] high_c].
  move => [] _ <- _ <- <- /= exi.
  rewrite eqxx.
  have tmp := h_c_contact h.
  move : tmp => /orP [/andP [/eqP higheq cnnil]| /andP [/eqP cnil /eqP higheq]].
    rewrite -higheq /=.

     case : contact h higheq cnnil.
        by [].
        rewrite //=.

  rewrite cnil higheq.

  by rewrite eqxx.
move /IH.
move => IH' exi.
apply IH'.
move : exi => [] x [xin xcontains].
rewrite inE in xin .
move : xin => /orP [ /eqP xeqp | xinq2].
  rewrite -xeqp in notcontain.
  by rewrite notcontain in xcontains.
by exists x.
Qed.

Lemma l_h_c_decomposition open_cells pt :
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition open_cells pt  = (first_cells, contact, last_cells, low_f, high_f)   ->
(exists c, (c \in open_cells) /\ (contains_point pt c)) ->
(low (head dummy_cell contact) == low_f) /\ (high (last dummy_cell contact) == high_f) /\ contact != nil .
Proof.
rewrite /=.
case :  open_cells  => [/= | c q] fc c_c lc low_f high_f.
move => [] _ <- _ _ _ []x.
rewrite in_nil.
  move => /andP.
  by rewrite andFb.

rewrite /open_cells_decomposition .
move => h.
by have  := (l_h_c_fix h).
Qed.


Lemma contact_preserve_cells open_cells pt high_e contact_cells :
forall contact last_c high_c,
open_cells_decomposition_contact open_cells pt contact_cells high_e = (contact, last_c, high_c) ->
contact_cells ++ open_cells == contact ++ last_c.
Proof.
elim : open_cells contact_cells high_e => [/=| c q  IH] contact_cells high_e contact last_c high_c.
  move =>  [] -> <- _.
  by rewrite eqxx.
case : c => [lpts rpts lowc highc].
rewrite /=.
case : ifP => [contain| notcontain].
  case h : (open_cells_decomposition_contact _ _ _ _)=> [[contact1 last_c1] high_c1].
  move =>  [] <- <- _.
  have h2: ((rcons contact_cells {| left_pts := lpts; right_pts := rpts;low := lowc; high := highc |}) ++ q == contact1 ++ last_c1) .
    apply (IH _ highc _ _ high_c1).
    by rewrite h.
  move : h2 => /eqP  h2.
  rewrite -h2.
  by rewrite cat_rcons eqxx.
move =>  [] -> -> _.
by rewrite eqxx.
Qed.

Lemma fix_preserve_cells open_cells pt fc :
forall first_cells contact last_cells low high_f,
open_cells_decomposition_fix open_cells pt fc = (first_cells, contact, last_cells, low, high_f) ->
fc ++ open_cells == first_cells ++ contact ++ last_cells.
Proof.
elim : open_cells fc => [/=| c q IH] fc first_cells contact last_cells low_f high_f.
  move =>  [] <- <- <- _ _ .
  by [].
case : c => [lpts rpts lowc highc].
rewrite /=.
case : ifP => [contain| notcontain].
  case h : (open_cells_decomposition_contact _ _ _ _) => [[contact0 last_c0] high_c0].
  move =>  [] -> <- <- -> _.
  by have /= /eqP -> := (contact_preserve_cells h) .
move => h.
have /eqP <- := (IH _ _ _ _ _ _ h).
by rewrite cat_rcons.
Qed.

Lemma decomposition_preserve_cells open_cells pt :
forall first_cells contact last_cells low high_f,
open_cells_decomposition open_cells pt  = (first_cells, contact, last_cells, low, high_f) ->
open_cells = first_cells ++ contact ++ last_cells .
Proof.
case :  open_cells  => [/= | c q] fc c_c lc low_f high_f.
  by move => [] <- <- <- _ _.
rewrite /open_cells_decomposition.
move => h.
by have /= /eqP <- := (fix_preserve_cells h).
Qed.


Lemma contact_last_not_contain open_cells p high_e contact_cells :
bottom_edge_seq_above open_cells p ->
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
forall contact last_c high_c, 
open_cells_decomposition_contact open_cells p contact_cells high_e =
   (contact, last_c, high_c) ->
forall c, (c \in last_c) -> ~ contains_point p c.
Proof.
move => ba oprf opvalid  adj_op c_c last_cells highc.
elim op : open_cells ba oprf opvalid adj_op last_cells contact_cells high_e => [/= | c q  IH] ba op_rf opvalid adj_op last_c contact high_e.
  by move =>  [] _ <-  _  .
move => op_c.
have c_eq := (contact_preserve_cells op_c).
move : op_c.
case ceq : c => [lpts rpts lowc high_c].
rewrite /=.
case : ifP => [contain | /negbT notcontain].
  case h : (open_cells_decomposition_contact _ _ _ _)=> [[contact1 last_c1] high_c1].
  move =>  [] a  <- b.
  rewrite a b in h.
  have q_rf: s_right_form q.
    move : op_rf.
    by rewrite /s_right_form /all => /andP [] _.
  have qval : (seq_valid q p).
    move : opvalid.
    by rewrite /s_right_form /all => /andP [] _.
  have adjq : adjacent_cells q by apply: (adjacent_cons adj_op).
  have baq : bottom_edge_seq_above q p.
    move: contain; rewrite /contains_point /= => /andP[] _.
    rewrite /bottom_edge_seq_above; move: adj_op.
    by case: (q)=> //= a' q' => /andP[/eqP <- _]; rewrite ceq.
  by apply : (IH baq q_rf qval adjq last_c1 (rcons contact {| left_pts := lpts; right_pts := rpts;low := lowc; high := high_c |})  high_c h).
move =>  [] conteq lc heq {IH}.
rewrite -lc.
move => c1.
rewrite inE => /orP[ | c1inq].
  by move : notcontain => /negP notcontain /eqP  -> .
have rfc1 : (right_form c1).
  move : op_rf.
  rewrite /s_right_form .
  move =>  /allP /= incq /=.
  have := (incq c1).
  by rewrite inE c1inq orbT => // /(_ isT).
have valc1 : valid_edge (low c1) p /\ valid_edge (high c1) p.
  move : opvalid.
  rewrite /seq_valid.
  move =>  /allP /= valcq /=.
  have := (valcq c1).
  rewrite inE c1inq orbT.
  move =>  a.
  apply /andP.
by apply a. 
have [vallc valhc] : valid_edge (low c) p /\ valid_edge (high c) p.
  by move: opvalid => /allP /= /(_ c); rewrite inE eqxx => /(_ isT)=>/andP.
have lowhigh : (low c) <| (high c).
  by move: op_rf=> /allP /(_ c); rewrite inE eqxx /right_form => /(_ isT).
have underhigh : p <<= (high_c).
  rewrite (_ : high_c = high c); last by rewrite ceq.
  by apply: order_edges_viz_point.
have strictunder : p <<< (low c).
  by move: notcontain; rewrite ceq negb_and /= underhigh orbF negbK.
rewrite /right_form /edge_below in rfc1.
move: notcontain; rewrite /contains_point negb_and negbK /==> notcontain.
apply/negP; rewrite negb_and negbK.
by rewrite (strict_under_seq adj_op opvalid op_rf strictunder).
Qed.

Lemma fix_not_contain fc open_cells p   :
(forall c, c \in fc  -> ~ contains_point p c) ->
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
bottom_edge_seq_below open_cells p ->
forall first_cells contact last_cells low_f high_f,
open_cells_decomposition_fix open_cells p fc =
  (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) ->
~ contains_point p c.
Proof.
elim: open_cells fc => [/= | c1 open_cells IH] fc cfc.
  move=>_ _  _ _ fc' cc lc l_e h_e=> [][] <- _ <- _ _ c.
  by rewrite orbF; apply: cfc.
rewrite /bottom_edge_seq_below=> rfc1 valc1  adjc1 pabovec1 fc' cc lc l_e h_e.
rewrite /=.
case c1_eq : c1 => [lpts rpts lc1 hc1].
case open_cells_eq : open_cells => [ | c2 q] //.
  case: ifP => [contains | /negbT notcontains] /=.
    by move=> [] <- _ <- _ _ c; rewrite orbF; apply: cfc.
  move=> [] <- _ <- _ _ c; rewrite orbF -cats1 mem_cat => /orP[cinf |].
    by apply: cfc.
  rewrite inE => /eqP ->.
  by move : notcontains => /negP.

have rfo : s_right_form (c2 :: q).
  rewrite -open_cells_eq.
  by apply/allP=> c' c'in; apply (allP rfc1); rewrite inE c'in orbT.
have valo : seq_valid (c2 :: q) p.
  rewrite -open_cells_eq.
  by apply/allP=> c' c'in; apply: (allP valc1); rewrite inE c'in orbT.
move: (adjc1); rewrite open_cells_eq => /andP[/eqP c1c2 adjc2'].
have adjo : adjacent_cells (c2 :: q) by exact adjc2'.
case: ifP => [contains | /negbT notcontains].
  case contact_eq : 
  (open_cells_decomposition_contact (c2 :: q) p [::] hc1) =>
  [[contact_cells last_cells] edge1] [] <- _ <- _ _.
  move=> c /orP[cinfc | cinlc].
    by apply: cfc.
  have pundero : bottom_edge_seq_above (c2 :: q) p.
    by rewrite /= -c1c2 c1_eq; move: contains => /andP[] /=.
  by apply :  (contact_last_not_contain _ _ _ _ contact_eq).
have belowc2 : bottom_edge_seq_below (c2 :: q) p.
  move: notcontains; rewrite -c1_eq negb_and negbK (negbTE pabovec1) /=.
  by rewrite /= c1c2 => /negP *; apply/negP/underWC.
move=> fixeq.  
have := IH (rcons fc c1); rewrite open_cells_eq c1_eq.
move=> /(_ _ rfo valo adjo belowc2 _ _ _ _ _ fixeq); apply.
move=> c; rewrite -cats1 mem_cat inE=> /orP[cinfc | /eqP ->].
  by apply: cfc.
by move : notcontains => /negP.
Qed.


Lemma decomposition_not_contain open_cells p : 
forall first_cells contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
bottom_edge_seq_below open_cells p ->
open_cells_decomposition open_cells p  = (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) -> ~ contains_point p c.
Proof.
move => fc c_c l_c low_f high_f.
rewrite /open_cells_decomposition.
case: open_cells => [ | c q] rfo valo adjo boto.
  by move=>[] <- _ <- _ _ c.
by move/fix_not_contain; apply.
Qed.

Lemma decomposition_not_end open_cells e :
forall first_cells contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells (point e) ->
adjacent_cells open_cells ->
bottom_edge_seq_below open_cells (point e) ->
open_cells_decomposition open_cells (point e)  = (first_cells, contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) -> ( ~ event_close_edge (low c) e) /\ ( ~ event_close_edge (high c) e).
Proof.
move => fc c_c l_c low_f high_f srf svalid adj bedbelow dec_eq c1 c1nfclc .
have := (decomposition_not_contain srf svalid adj bedbelow dec_eq c1nfclc).
have c1open : c1 \in open_cells.
    rewrite (decomposition_preserve_cells dec_eq).
    move : c1nfclc => /orP [].
      by rewrite mem_cat => -> .
    rewrite !mem_cat => -> .
    by rewrite !orbT.
apply : contrapositive_close_imp_cont.
  apply: (allP srf _ c1open).
apply /andP; apply: (allP svalid _ c1open).
Qed.


Lemma l_h_neq_contact open p high_e contact :
p <<= high_e ->
adjacent_cells open ->
seq_valid open p ->
s_right_form open ->
((p <<< high (last dummy_cell open)) && (high_e == low (head dummy_cell open)) && (open !=nil)) || ((open == nil) &&  (p <<< high_e)) ->
forall c_c last_c high_c, 
open_cells_decomposition_contact open p contact high_e = (c_c,last_c, high_c) ->
p <<< high_c.
Proof.
elim : open contact high_e  => [//= | c q Ih/=] contact high_e   /=.
 by rewrite andbF /= => _ _ _ _ pinfe a b c [] _ _ <-  .
rewrite orbF andbT.
move => pinfe  adjopen valopen rf_open pinfhighc c_c lc highc //.
case c_eq : c pinfhighc adjopen valopen rf_open => [lpts rpts lowc high_c].

case : ifP => [contain| notcontain {Ih}] /= pinfh adjopen valopen rf_open op_dec .
  
move : contain.
  rewrite /contains_point => /andP [] _ /= pinf_c.
  have := (Ih _ _  pinf_c _ _ _  _ _ _  _ op_dec )  =>  Ih' {Ih}.
  

  case : q adjopen  op_dec valopen rf_open pinfh Ih' => [//= |  c' q'  /= /andP [] -> -> op_dec] .
    rewrite andbF orFb /= => _ _ _ _ /andP [] -> _ a.
    by apply a.
  rewrite !andbT orbF =>  /andP [] _ /andP [] /andP [] -> -> -> /andP [] _ /andP [] -> -> /andP [] -> _ a.
  by apply a.

move : op_dec => [] _ _ <-. 
move : notcontain.
rewrite /contains_point /= .
move => /idPn.
rewrite negb_and => /orP [/negPn |].
  by move : pinfh => /andP  [] _ /eqP ->.
move : pinfh => /andP  [] _ /eqP heql .
rewrite heql in pinfe.
move : valopen => /andP [] /andP []  vallow valhigh _.
have vall': valid_edge (low c) p.
  by rewrite c_eq.
have valh': valid_edge (high c) p.
  by rewrite c_eq.
move : rf_open.
rewrite /right_form /= => /andP [] linfh _.
have inf' : low c <| high c.
  by rewrite c_eq.
have pinf : p <<= low c .
  by rewrite c_eq.
move => /negPf.
have := order_edges_viz_point vall' valh' inf' pinf.
by rewrite c_eq /= => -> .
Qed.

Lemma l_h_above_under_contact open p high_e contact :
p <<= high_e ->
forall c_c last_c high_c, 
open_cells_decomposition_contact open p contact high_e = (c_c,last_c, high_c) ->
p <<= high_c.
Proof.
elim : open contact high_e  => [//= | c open Ih] contact high_e pinf.
  by move => _ _ _ [] _ _ <-.
case : c=> [lpts rpts lowc highc].
rewrite /=.
case : ifP => [contain| notcontain]. 
  case h : (open_cells_decomposition_contact _ _ _ _) => [[cc lc]high_final].
  move => _ _ _ [] _ _ <-.
  have := Ih _ _ _ _ _ _ h => d.
  apply d.
  move : contain.
  by rewrite /contains_point /= => /andP [] _ pinfhc.
by move => _ _ _ [] _ _ <-.
Qed.

Lemma l_h_above_under_fix open_cells  p fc :
(exists c, (c \in open_cells) && contains_point p c)  ->
forall first_cells contact last_cells low_f high_f ,
open_cells_decomposition_fix open_cells p fc = (first_cells, contact, last_cells, low_f, high_f)   ->
~~( p <<< low_f) && (p <<= high_f).
Proof.
move => exi f_c c_c l_c lowf highf .
elim : open_cells fc exi => [//= fc []c' |c' q' IH /= fc].
  by [].
case : c' => [lpts rpts lowc highc] .
case : ifP => [contain |notcontain].
  case op_c: (open_cells_decomposition_contact _ _ _ _) => [/= []cc lc high_c] _ [] _ _ _ <- <-.
  move : contain.
  rewrite /contains_point /= => /andP [] -> pinfhc.
  by rewrite (l_h_above_under_contact pinfhc op_c) andbT.
move => [] c' /andP.

rewrite inE => [][] /orP [/eqP -> a|cin cont op_c].
  by rewrite a in notcontain.
apply : (IH _ _ op_c).
exists c'.
by rewrite cin cont.
Qed.


End proof_environment.
