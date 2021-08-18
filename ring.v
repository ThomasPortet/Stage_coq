
From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope ring_scope.
Section ring_sandbox.

Variable R : numFieldType.
Definition R' := (R : Type).

Let mul : R' -> R' -> R' := @GRing.mul _.
Let add : R' -> R' -> R' := @GRing.add _.
Let sub : R' -> R' -> R' := (fun x y => x - y).
Let opp : R' -> R' := @GRing.opp _.
Let zero : R' := 0.
Let one : R' := 1.


Let R2_theory :=
   @mk_rt R' zero one add mul sub opp
    (@eq R')
    (@add0r R) (@addrC R) (@addrA R) (@mul1r R) (@mulrC R)
      (@mulrA R) (@mulrDl R) (fun x y : R' => erefl (x - y)) (@addrN R).

Add Ring R2_Ring : R2_theory.

Ltac mc_ring :=
rewrite ?mxE /= ?(expr0, exprS, mulrS, mulr0n) -?[@GRing.add _]/add
    -?[@GRing.mul _]/mul
    -?[@GRing.opp _]/opp -?[1]/one -?[0]/zero;
match goal with |- @eq ?X _ _ => change X with R' end;
ring.

Let inv : R' -> R' := @GRing.inv _.
Let div : R' -> R' -> R' := fun x y => mul x (inv y).

Definition R2_sft : field_theory zero one add mul sub opp div inv (@eq R').
Proof.
constructor.
- exact R2_theory.
- have // : one <> zero by apply/eqP; rewrite oner_eq0.
- have // : forall p q : R', div p q = mul p (inv q) by [].
- have // : forall p : R', p <> zero -> mul (inv p) p = one.
  by move=> *; apply/mulVf/eqP.
Qed.

Add Field Qfield : R2_sft.

Ltac mc_field :=
rewrite ?mxE /= ?(expr0, exprS, mulrS, mulr0n) -?[@GRing.add _]/add
    -?[@GRing.mul _]/mul -[@GRing.inv _]/inv
    -?[@GRing.opp _]/opp -?[1]/one -?[0]/zero;
match goal with |- @eq ?X _ _ => change X with R' end;
field.

Example field_playground (x y : R' ) : x != 0 -> y != 0 -> (x * y) / (x * y) = 1.
Proof.
move=> xn0 yn0; mc_field.
by split; apply/eqP.
Qed.

(* returns true if p is under A B *)
Definition pue_f (p_x p_y a_x a_y b_x b_y : R')  : R' :=
     (b_x * p_y - p_x * b_y - (a_x * p_y - p_x * a_y) + a_x * b_y - b_x * a_y).

Lemma pue_f_o p_x p_y a_x a_y b_x b_y:  pue_f p_x p_y a_x a_y b_x b_y = - pue_f  b_x b_y a_x a_y p_x p_y.
Proof.
  rewrite /pue_f.
  mc_ring.
Qed.

Lemma pue_f_c p_x p_y a_x a_y b_x b_y:  pue_f p_x p_y a_x a_y b_x b_y =  pue_f   b_x b_y p_x p_y a_x a_y.
Proof.
  rewrite /pue_f.
  mc_ring.
Qed.

Lemma pue_f_inter p_x  a_x a_y b_x b_y :  b_x != a_x -> (pue_f p_x ((p_x - a_x)* ((b_y - a_y)/(b_x - a_x)) + a_y) a_x a_y b_x b_y) == 0.
Proof.
rewrite /pue_f.
rewrite -subr_eq0 => h.
set slope := (_ / _).

rewrite (mulrDr b_x).
rewrite (mulrDr a_x).
rewrite -(orbF (_==0)).
rewrite -(negbTE   h).
rewrite -mulf_eq0 .
rewrite ! ( mulrBl (b_x - a_x), fun x y => mulrDl  x y (b_x - a_x)).

rewrite /slope !mulrA !mulfVK //.
apply/eqP; mc_ring.
Qed.

Lemma pue_f_inters p_x p_y a_x a_y b_x b_y  :  b_x != a_x -> p_y = ((p_x - a_x) * ((b_y - a_y) / (b_x - a_x)) + a_y) ->
pue_f p_x p_y a_x a_y b_x b_y == 0.
Proof.
move => h ->.
by apply pue_f_inter; rewrite h.


Qed.

Lemma pue_f_eq p_x p_y a_x a_y :
pue_f p_x p_y p_x p_y a_x a_y == 0.
Proof.
rewrite /pue_f /=.

apply /eqP.
mc_ring.
Qed.

Lemma pue_f_two_points p_x p_y a_x a_y :
pue_f p_x p_y p_x p_y a_x a_y == 0 /\ pue_f p_x p_y a_x a_y p_x p_y == 0 /\
pue_f p_x p_y a_x a_y a_x a_y == 0.
Proof.
split.
apply pue_f_eq.
split.
have := pue_f_c p_x p_y  a_x a_y p_x p_y.
move => ->.
apply pue_f_eq.
have := pue_f_c  a_x a_y  a_x a_y p_x p_y.
move => <-.
apply pue_f_eq.
Qed.

Lemma pue_f_vert p_y a_x a_y b_x b_y :
 (pue_f  a_x a_y b_x b_y b_x p_y) == (b_x - a_x) * (p_y - b_y).
Proof.
rewrite /pue_f.
apply /eqP.
mc_ring.
Qed.


Lemma ax4 p_x p_y q_x q_y r_x r_y t_x t_y :
pue_f t_x t_y q_x q_y r_x r_y + pue_f p_x p_y t_x t_y r_x r_y
+ pue_f p_x p_y q_x q_y t_x t_y == pue_f p_x p_y q_x q_y r_x r_y.
Proof.
rewrite /pue_f.
apply /eqP.
  mc_ring.
Qed.

Lemma pue_f_linear l a b c d e f :
l * pue_f a b c d e f = pue_f a (l*b) c (l*d) e (l*f).
Proof.
rewrite /pue_f.
mc_ring.
Qed.

Lemma pue_f_on_edge_y a_x a_y b_x b_y m_x m_y :
pue_f a_x a_y b_x b_y m_x m_y == 0 ->
(b_x - a_x) * m_y = m_x * (b_y -a_y)- (a_x * b_y - b_x *a_y).
Proof.
move => /eqP abmeq0.
apply /eqP.
rewrite -subr_eq0.
apply /eqP.
rewrite -abmeq0 /pue_f.
mc_ring.
Qed.

Lemma pue_f_on_edge a_x a_y b_x b_y c_x c_y d_x d_y m_x m_y :
pue_f a_x a_y b_x b_y m_x m_y == 0 ->
(b_x - a_x) * pue_f c_x c_y d_x d_y m_x m_y ==
(m_x - a_x) * pue_f c_x c_y d_x d_y b_x b_y + (b_x - m_x) * pue_f c_x c_y d_x d_y a_x a_y.
Proof.
move => on_ed.
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge a_x a_y b_x b_y p_x p_y p'_x p'_y :
pue_f a_x a_y b_x b_y p'_x p'_y == 0 ->
(b_x - a_x) * pue_f a_x a_y p_x p_y p'_x p'_y ==
(p'_x - a_x) * pue_f a_x a_y p_x p_y b_x b_y .
Proof.
move=> on_ed.
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge' a_x a_y b_x b_y p_x p_y p'_x p'_y :
pue_f a_x a_y b_x b_y p'_x p'_y == 0 ->
(b_x - a_x) * pue_f p_x p_y b_x b_y p'_x p'_y ==
(b_x - p'_x) * pue_f a_x a_y p_x p_y b_x b_y .
Proof.
move => on_ed .
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.


Lemma pue_f_on_edge_same_point_counter_example :
  ~ (forall a_x a_y b_x b_y p_x p_y p_x' p_y',
    a_x != b_x ->  (* The two points are not on the same vertical *)
    pue_f a_x a_y b_x b_y p_x p_y == 0 ->
    pue_f a_x a_y b_x b_y p_x' p_y' == 0 ->
    (p_y == p_y') = (p_x == p_x')).
Proof.
move=> bad_thm.
have := bad_thm 1%:R 0 2%:R 0 1%:R 0 2%:R 0.
rewrite (eqr_nat R 1%N 2%N) /=.
have -> : pue_f 1%:R 0 2%:R 0 1%:R 0 == 0.
  apply/eqP; rewrite /pue_f.
  mc_ring.
have -> : pue_f 1%:R 0 2%:R 0 2%:R 0 == 0.
  apply/eqP; rewrite /pue_f.
  mc_ring.
move=> /(_ isT isT isT).
rewrite eqxx.
by[].
Qed.

Lemma pue_f_on_edge_same_point a_x a_y b_x b_y p_x p_y p_x' p_y':
a_x != b_x ->
pue_f a_x a_y b_x b_y p_x p_y == 0 ->
pue_f a_x a_y b_x b_y p_x' p_y' == 0 ->
(p_x == p_x') -> (p_y == p_y').
Proof.
move => axnbx puep0 puep'0.
have pyeq := (pue_f_on_edge_y puep0 ).
have p'yeq := (pue_f_on_edge_y puep'0 ).
move=> xxs; have yys : (b_x - a_x) * p_y = (b_x - a_x) * p_y'.
  by rewrite pyeq (eqP xxs) p'yeq.
move: (axnbx); rewrite eq_sym -subr_eq0=> bxmax.
apply/eqP.
by apply: (mulfI bxmax).
Qed.

Lemma pue_f_ax5 p_x p_y q_x q_y a_x a_y b_x b_y c_x c_y :
  pue_f p_x p_y a_x a_y b_x b_y *
  pue_f p_x p_y q_x q_y c_x c_y +
  pue_f p_x p_y b_x b_y c_x c_y *
  pue_f p_x p_y q_x q_y a_x a_y =
  pue_f p_x p_y a_x a_y c_x c_y *
  pue_f p_x p_y q_x q_y b_x b_y.
Proof.
rewrite /pue_f; mc_ring.
Qed.

Lemma pue_f_triangle_decompose a_x a_y b_x b_y c_x c_y d_x d_y :
  pue_f a_x a_y c_x c_y d_x d_y = 0 ->
  pue_f a_x a_y b_x b_y c_x c_y =
  pue_f a_x a_y b_x b_y d_x d_y +
  pue_f b_x b_y c_x c_y d_x d_y.
Proof.
move=> online.
rewrite -(eqP (ax4 _ _ _ _ _ _ d_x d_y)).
rewrite addrC; congr (_ + _).
by rewrite addrC pue_f_o pue_f_c online oppr0 add0r -pue_f_c.
Qed.

End ring_sandbox.