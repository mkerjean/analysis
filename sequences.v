(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype bigop matrix interval.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology hierarchy landau forms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Definition sequence R := nat -> R.
Notation "R ^nat" := (sequence R) (at level 0).

Section sequences.

Canonical eventually_filter := FilterType eventually _.
Canonical eventually_pfilter := PFilterType eventually (filter_not_empty _).
Notation eqolimn := (@eqolim _ _ _ (eventually_filter)).
Notation eqolimPn := (@eqolimP _ _ _ (eventually_filter)).

Lemma lim_add_sequence (u_ v_ : (R^o) ^nat) : cvg u_ -> cvg v_ ->
  lim (u_ + v_) = lim u_ + lim v_.
Proof. by move=> u_cv v_cv; apply/flim_map_lim/lim_add. Qed.

Lemma addo' (K : absRingType) (T : Type) (V W : normedModType K) (F : filter_on T)
  (f g : T -> V) (e : T -> W) (F' := unkeyed F) :
  [o_F e of f] + [o_F' e of g] =o_F e.
Proof. exact: addo. Qed.


Lemma lim_add3sequence (u_ v_ w_ : (R^o) ^nat) : cvg u_ -> cvg v_ -> cvg w_ ->
  lim (u_ + v_ + w_) = lim u_ + lim v_ +  lim w_.
Proof.
move=> /eqolimPn u_cv /eqolimPn v_cv /eqolimPn w_cv.
apply/flim_map_lim.
apply: eqolimn.
rewrite [in LHS]u_cv /= [in LHS]v_cv /= [in LHS]w_cv.
rewrite addrACA -!addrA.
(* rewrite showo. *)
rewrite addo'.
(* rewrite showo. *)
rewrite [cst _ + (cst _ + _)]addrA addrA.
rewrite addrACA !addrA -addrA.
rewrite [X in X + _]addrAC.
congr (_ + _ + _ + _).
rewrite addo'.
done.
Qed.

End sequences.