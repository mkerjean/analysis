
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(*Require Import ssrsearch.*)
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop order ssralg ssrnum.
From mathcomp Require Import complex.
From mathcomp Require Import boolp reals ereal derive.
Require Import classical_sets posnum topology normedtype landau.

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* I need to import ComplexField to use its lemmas on RComplex,
I don't want the canonical lmodtype structure on C,
Therefore this is based on a fork of real-closed *)


Section complex_extras.
Variable R : rcfType.
Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
(* Local Notation Re := (@complex.Re R). (* clean redundancy with Re in algC TODO *) *)
(* Local Notation Im := (@complex.Im R). *)

(*Adapting lemma eq_complex from complex.v, which was done in boolean style*)
Lemma eqE_complex : forall (x y : C), (x = y) = ((Re x = Re y) /\ (Im x = Im y)). (*Locate Re.*)
Proof.
move=> [a b] [c d]; apply : propositional_extensionality ; split.
by move=> -> ; split.
by case=> //= -> ->.
Qed.

Lemma Re0 : Re 0 = 0 :> R.
Proof. by []. Qed.

Lemma Im0 : Im 0 = 0 :> R.
Proof. by []. Qed.

Lemma ReIm_eq0 (x : C) : (x = 0) = ((Re x = 0) /\ (Im x = 0)).
Proof. by rewrite -[in Re x= _]Re0 -Im0 -eqE_complex. Qed.

Lemma scalei_muli (z : C^o) : 'i * z = 'i *: z.
Proof. by []. Qed.

Lemma iE : 'i%C = 'i :> C.
Proof. by []. Qed.

Lemma scalecM : forall (w  v : C^o), (v *: w = v * w).
Proof. by []. Qed.

Lemma normc0 : normc 0 = 0 :> R  .
Proof. by rewrite /normc //= expr0n //= add0r sqrtr0. Qed.

Lemma normcN (x : C) : normc (- x) = normc x.
Proof. by case: x => a b /=; rewrite 2!sqrrN. Qed.

Lemma normcr (x : R) : normc (x%:C) = normr x.
Proof. by rewrite /normc/= expr0n //= addr0 sqrtr_sqr. Qed.

Lemma normcR (x : C) : (normc x)%:C = normr x.
Proof. by rewrite /normr /=. Qed.

Lemma normc_i (x : R) : normc (x*i) = normr x.
Proof. by rewrite /normc/= expr0n //=  add0r sqrtr_sqr. Qed.

Lemma normc1 : normc (1 ) = 1 :> R.
Proof. by rewrite /normc/= expr0n addr0 expr1n sqrtr1. Qed.

Lemma normcN1 : normc (-1%:C) = 1 :> R.
Proof. by rewrite /normc/=  oppr0 expr0n addr0 -signr_odd expr0 sqrtr1. Qed.


Lemma realCD (x y : R) : (x + y)%:C = x%:C + y%:C.
Proof.
(*realC_additive*)
rewrite -!complexr0 eqE_complex //=; by split; last by rewrite addr0.
Qed.

Lemma Inv_realC (x : R) : x%:C^-1 = (x^-1)%:C.
Proof.
have [/eqP->|x0] := boolP (x == 0); first by rewrite !invr0.
apply/eqP; rewrite eq_complex /= mul0r oppr0 eqxx andbT expr0n addr0.
by rewrite expr2 invrM ?unitfE // mulrA divrr ?unitfE // div1r.
Qed.

Lemma CimV : ('i%C)^-1 = (-1 *i) :> C.
Proof. by rewrite complexiE invCi. Qed.

Lemma invcM (x y : C) : (x * y)^-1 = x^-1 * y^-1.
Proof.
have [/eqP->|x0] := boolP (x == 0); first by rewrite !(invr0,mul0r).
have [/eqP->|y0] := boolP (y == 0); first by rewrite !(invr0,mulr0).
by rewrite invrM // mulrC.
Qed.

Lemma Im_mul (x : R) : x *i = x%:C * 'i%C.
Proof. by simpc. Qed.

Lemma normcD (x y : C) : normc (x + y) <= normc x + normc y.
Proof. by rewrite -lecR realCD; apply: lec_normD. Qed.

Lemma normc_ge0 (x : C) : 0 <= normc x.
Proof. case: x => ? ?; exact: sqrtr_ge0. Qed.

Lemma normc_gt0 (v : C) : (0 < normc v) = (v != 0).
Proof.
rewrite lt_neqAle normc_ge0 andbT; apply/idP/idP; apply/contra.
by move/eqP ->; rewrite normc0.
by rewrite eq_sym => /eqP/eq0_normc ->.
Qed.

Lemma mulrnc (a b : R) k : a +i* b *+ k = (a *+ k) +i* (b *+ k).
Proof.
by elim: k => // k ih; apply/eqP; rewrite !mulrS eq_complex !ih !eqxx.
Qed.

Lemma realCM (a b :R) : a%:C * b%:C = (a * b)%:C.
Proof. by rewrite eqE_complex /= !mulr0 mul0r addr0 subr0. Qed.

Lemma complexA: forall (h : C^o), h%:A = h.
Proof. by move => h; rewrite scalecM mulr1. Qed. 

Lemma lecM (a b : R) k : a +i* b *+ k = (a *+ k) +i* (b *+ k).
Proof.
by elim: k => // k ih; apply/eqP; rewrite !mulrS eq_complex !ih !eqxx.
Qed.

Lemma normc_natmul (k : nat) : normc k%:R = k%:R :> R.
Proof.
by rewrite mulrnc /= mul0rn expr0n addr0 sqrtr_sqr ger0_norm // ler0n.
Qed.

Lemma normc_mulrn (x : C) k : normc (x *+ k) = (normc x) *+ k.
Proof.
by rewrite -mulr_natr normcM -[in RHS]mulr_natr normc_natmul.
Qed.

Lemma gt0_normc (r : C) : 0 < r -> r = (normc r)%:C.
Proof.
move=> r0; have rr : r \is Num.real by rewrite realE (ltW r0).
rewrite /normc (complexE r) /=; simpc.
rewrite (ger0_Im (ltW r0)) expr0n addr0 sqrtr_sqr gtr0_norm ?complexr0 //.
by move: r0; rewrite {1}(complexE r) /=; simpc => /andP[/eqP].
Qed.

Lemma gt0_realC (r : C) : 0 < r -> r = (Re r)%:C.
Proof.
by move=> r0; rewrite eqE_complex /=; split; last by apply: ger0_Im; apply: ltW.
Qed. (* TODO : utiliser algC *)

Lemma ltr0c  (k : R): (0 < k%:C) = (0 < k).
Proof.  by simpc. Qed.


Lemma complex_pos (r : {posnum C}) :  0 < (Re r%:num).
Proof.  by rewrite -ltr0c -gt0_realC. Qed.

(*TBA algC *)
Lemma realC_gt0 (d : C) :  0 < d = (0 < Re d :> R). 
Proof. Admitted.

Lemma Creal_gtE (c d : C) :  c < d = (complex.Re c < complex.Re d). (*name*)
Proof. Admitted.

Canonical complex_Re_posnum (x : {posnum C}) := PosNum (complex_pos x).

Lemma realC_pos_gt0 (r : {posnum R}) :  0 < (r%:num)%:C.
Proof. by rewrite ltcR. Qed.

Canonical realC_posnum (x : {posnum R}) := PosNum (realC_pos_gt0 x).

Lemma realC_norm (b : R) : `|b%:C| = `|b|%:C.
Proof. by rewrite normc_def /= expr0n addr0 sqrtr_sqr. Qed.

Lemma eqCr (r s : R) : (r%:C == s%:C) = (r == s).
Proof. exact: (inj_eq (@complexI _)). Qed.

Lemma eqCI (r s : R) : (r *i == s *i) = (r == s).
Proof. by apply/idP/idP => [/eqP[] ->//|/eqP ->]. Qed.

Lemma neqCr0 (r : R) : (r%:C != 0) = (r != 0).
Proof. by apply/negP/negP; rewrite ?eqCr. Qed.


Lemma realCV (*name ?*) (h: R) : h != 0 -> (h^-1)%:C = h%:C^-1.
Proof.
rewrite eqE_complex //=; split; last by rewrite mul0r oppr0.
by rewrite expr0n //= addr0 -exprVn expr2 mulrA mulrV ?unitfE ?mul1r //=.
Qed.


Lemma real_normc_ler (x y : R) :
  `|x| <= normc (x +i* y).
Proof.
rewrite /normc /= -ler_sqr ?nnegrE ?normr_ge0 ?sqrtr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 ?real_normK //=; last by apply: num_real.
by rewrite ler_addl ?sqr_ge0.
Qed.

Lemma im_normc_ler (x y : R) :
  `|y| <= normc (x +i* y).
Proof.
rewrite /normc /= -ler_sqr ?nnegrE ?normr_ge0 ?sqrtr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 ?real_normK //=; last by apply: num_real.
by rewrite ler_addr ?sqr_ge0.
Qed.

End complex_extras.


Section Holomorphe_der.
Variable R : rcfType.

Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
(* Local Notation Re := (@complex.Re R). *)
(* Local Notation Im := (@complex.Im R). *)

(*TODO : introduce Rcomplex at top, and use notation Rdifferentiable everywhere *)

Lemma is_cvg_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
 (F : set (set T)) (H :Filter F) (f : T -> V) (k : K) :
 cvg (f @ F) -> cvg ((k \*: f) @ F ).
Proof. by move => /cvg_ex [l H0] ; apply: cvgP; apply: cvgZr; apply: H0. Qed.

Lemma limin_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
  (F : set (set T)) (FF : ProperFilter F) (f : T -> V) (k : K) :
  cvg(f @ F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
Proof. by move => cv; apply/esym/cvg_lim => //; apply: cvgZr. Qed.


Definition holomorphic (f : C^o -> C^o) (c : C) :=
  cvg ((fun h => h^-1 *: (f (c + h) - f c)) @ (nbhs' (0:C^o))).
(* todo: rewrite in an unfolded form for shift and scalar *)

(* No Rmodule structure on C if we can avoid,
so the following line shouldn't type check. *)
Fail Definition Rderivable_fromcomplex_false (f : C^o -> C^o) (c v: C^o) :=
  cvg (fun (h : R^o) =>  h^-1 *: (f (c +h *: v) - f c)) @ (nbhs' (0:R^o)).

Definition realC : R^o -> C := ( fun r => r%:C ). 

Definition Rderivable_fromcomplex (f : C^o -> C^o) (c v: C^o) :=
  cvg ((fun (h : C^o) => h^-1 *: (f(c + h *: v) - f c)) @
                                     (realC @ (nbhs' (0:R^o)))).

Definition CauchyRiemanEq (f : C^o -> C^o) z :=
  'i * (lim  ((fun h : C^o => h^-1 *: (f(z + h) - f z)) @
                                        (realC @ (nbhs' (0:R^o))))) =
  lim ((fun h : C^o => h^-1 *: (f (z + h * 'i) - f z)) @
                                        (realC @ (nbhs' (0:R^o)))) .

(* todo : faire des réécritures par conversion dans le script de preuve *)

Lemma holo_derivable (f : (C)^o -> (C)^o) c :
  holomorphic f c -> (forall v : C^o, Rderivable_fromcomplex f c v).
Proof.
move=> /cvg_ex; rewrite /type_of_filter /=.
move => [l H]; rewrite /Rderivable_fromcomplex => v /=.
set quotR := (X in (X @ _)).
simpl in (type of quotR).
pose mulrv (h : R^o) := (h%:C * v).
pose quotC (h : C^o) : C^o := h^-1 *: (f (c + h) - f c).
have -> :  quotR @ (realC @ nbhs' 0) = (quotR \o (realC)) @ nbhs' 0 by [].
case: (v =P 0) =>  [eqv0|/eqP vneq0].
  have -> :  quotR \o realC = 0.
    apply: funext => h; rewrite  /quotR  /= eqv0.
    by rewrite scaler0 addr0 /= subrr /= scaler0 //=.
  by apply: (cvgP (0:C^o)); apply: (cvg_cst (0 : C^o)).
apply: (cvgP (v *: l)).
have eqnear0: {near nbhs' 0, (v \*o quotC) \o mulrv =1 (quotR \o realC)}.
(* as we need to perform computation for h != 0, we cannot prove fun equality directly *)
  exists 1 => // h _ neq0h; rewrite /quotC /quotR /realC /mulrv //=.
(*have -> :  (h *: v)^-1 = h^-1 *: v^-1. Fail rewrite (@invrZ R _ h _). *) (* issue with R^o*)
  rewrite invrM ?unitfE //; last by rewrite neqCr0 ?unitfE.
  by rewrite mulrA (mulrA v) mulrV ?unitfE // mul1r /= !scalecM [X in f X]addrC.
have subsetfilters : quotR \o realC @ nbhs' 0 `=>` (v \*o quotC) \o mulrv @ nbhs' 0.
by apply: (near_eq_cvg eqnear0).
apply: cvg_trans subsetfilters _.
suff: v \*o quotC \o mulrv @ nbhs' 0 `=>` nbhs (v *: l) by move/cvg_trans; apply.
apply: (@cvg_comp _ _ _ _ _ _ (nbhs' (0:C^o))); last by apply: cvgZr.
move => //= A [r leq0r /= ballrA].   exists ( normc r / normc v ).
 by  rewrite /= mulr_gt0 // ?normc_gt0 ?gt_eqF //= ?invr_gt0 ?normc_gt0.
move=> b ; rewrite /ball_ /= sub0r normrN => ballrb neqb0.
have ballCrb : (@ball_ _ _ (fun x => `|x|) 0 r (mulrv b)).
  rewrite /ball_ /= sub0r normrN /mulrv normrM.
  rewrite ltr_pdivl_mulr in ballrb; last by rewrite normc_gt0.
  by rewrite -(ger0_norm (ltW leq0r)) realC_norm realCM ltcR.
  by apply: (ballrA (mulrv b) ballCrb); apply: mulf_neq0 ; rewrite ?eqCr.
Qed.


(*The fact that the topological structure is only available on C^o
makes iterations of C^o apply *)

(*The equality between 'i as imaginaryC from ssrnum and 'i is not transparent:
 neq0ci is part of ssrnum and uneasy to find *)

Lemma holo_CauchyRieman (f : C^o -> C^o) c: holomorphic f c -> CauchyRiemanEq f c.
Proof. (* To be cleaned *)
move=> /cvg_ex; rewrite /type_of_filter //= /CauchyRiemanEq.
set quotC := (X in (exists l : ((R[i])^o),  X @ nbhs' 0  --> l)).
simpl in (type of quotC).
set quotR := fun h => h^-1 *: (f (c + h * 'i) - f c) .
simpl in (type of quotR).
move => [l H].
have -> :  quotR @ (realC @ nbhs' 0) =  (quotR \o (realC)) @ nbhs' 0 by [].
have HR0:(quotC \o (realC) @ nbhs' 0)  --> l.
  apply: cvg_comp; last by exact: H.
  move => A [[r ri]];  rewrite /= ltcE=> /andP /= [/eqP -> r0]; rewrite complexr0 => ball.
  exists r; first by [].
  move=> a /=; rewrite sub0r normrN => ar aneq0.
  apply: ball; last by rewrite eqCr.
  by simpl; rewrite sub0r normrN ltcR normcr.
have lem : quotC \o  *%R^~ 'i%R @ (realC @ (nbhs' (0 : R^o))) --> l.
  apply: cvg_comp; last by exact: H.
  move => A /= [ [r ri] ].
  rewrite /= ltcE=> /andP /= [/eqP -> r0]; rewrite complexr0 => ball.
  exists r; first by [].
  move => a /= ; rewrite sub0r normrN => ar aneq0; apply: ball.
    simpl; rewrite sub0r normrN normrM /=.
    have ->: `|'i| = 1 by move => T;  simpc; rewrite expr0n expr1n /= add0r sqrtr1.
    by rewrite mulr1 ltcR normcr.
  apply: mulf_neq0; last by rewrite neq0Ci.
  by rewrite eqCr.
have HRcomp:  cvg (quotC \o *%R^~ 'i%R @ (realC @ (nbhs' (0 : R^o)))) .
  by apply/cvg_ex;  simpl; exists l.
have ->: lim (quotR @ (realC @ (nbhs' (0 : R^o))))
  = 'i *: lim (quotC \o ( fun h => h *'i) @ (realC @ (nbhs' (0 : R^o)))).
  have: 'i \*:quotC \o ( fun h => h *'i) =1 quotR.
  move => h /= ;rewrite /quotC /quotR /=.
  rewrite invcM scalerA mulrC -mulrA mulVf.
    by rewrite mulr1.
    by rewrite neq0Ci.
by move => /funext <-; rewrite (limin_scaler _ 'i HRcomp).
rewrite scalecM.
suff: lim (quotC @ (realC @ (nbhs' (0 : R^o))))
      = lim (quotC \o  *%R^~ 'i%R @ (realC @ (nbhs' (0 : R^o)))) by move => -> .
suff -> : lim (quotC @ (realC @ (nbhs' (0 : R^o)))) = l.
  apply/eqP; rewrite eq_sym; apply/eqP. apply: (cvg_map_lim _ lem).
  by apply: norm_hausdorff.
by apply: (@cvg_map_lim [topologicalType of C^o]); first by apply: norm_hausdorff.
Qed.

End Holomorphe_der.

Module CR_holo.

Section Rcomplex.

Canonical Rcomplex_eqType (R : eqType) := [eqType of Rcomplex R].
Canonical Rcomplex_countType (R : countType) := [countType of Rcomplex R].
Canonical Rcomplex_choiceType (R : choiceType) := [choiceType of Rcomplex R].
Canonical Rcomplex_zmodType (R : rcfType) := [zmodType of Rcomplex R].
Canonical Rcomplex_ringType (R : rcfType) := [ringType of Rcomplex R].
Canonical Rcomplex_comRingType (R : rcfType) := [comRingType of Rcomplex R].
Canonical Rcomplex_unitRingType (R : rcfType) := [unitRingType of Rcomplex R].
Canonical Rcomplex_comUnitRingType (R : rcfType) := [comUnitRingType of Rcomplex R].
Canonical Rcomplex_idomainType (R : rcfType) := [idomainType of Rcomplex R].
Canonical Rcomplex_fieldType (R : rcfType) := [fieldType of Rcomplex R].
Canonical Rcomplex_lmodType (R : rcfType) :=
  LmodType R (Rcomplex R) (complex_real_lmodMixin R).

Canonical Rcomplex_pointedType  (R: realType)  := PointedType (Rcomplex R) 0.
Canonical Rcomplex_filteredType (R: realType) :=
  FilteredType (Rcomplex R) (Rcomplex R) (nbhs_ball_ (ball_ (@normc R))).

Definition Rcomplex_normedZmodMixin (R: realType) :=
  @Num.NormedMixin R (Rcomplex_zmodType R) _ _ (@normcD R) (@eq0_normc R)
                   (@normc_mulrn R) (@normcN R).

Canonical Rcomplex_normedZmodType (R: realType) :=
  NormedZmodType R (Rcomplex R) (Rcomplex_normedZmodMixin R).

Definition Rcomplex_pseudoMetricMixin (R: realType) :=
  (@pseudoMetric_of_normedDomain R (Rcomplex_normedZmodType R)).

Definition Rcomplex_topologicalMixin (R: realType):=
  topologyOfEntourageMixin (uniformityOfBallMixin
      (@nbhs_ball_normE R (Rcomplex_normedZmodType R) )
      (Rcomplex_pseudoMetricMixin R)).

Canonical Rcomplex_topologicalType (R: realType) :=
  TopologicalType (Rcomplex R) (Rcomplex_topologicalMixin R).

Definition Rcomplex_uniformMixin (R: realType):=
  uniformityOfBallMixin (@nbhs_ball_normE R (Rcomplex_normedZmodType R) )
                        (Rcomplex_pseudoMetricMixin R).

Canonical Rcomplex_uniformType (R: realType) :=
  UniformType (Rcomplex R) (Rcomplex_uniformMixin R).

Canonical Rcomplex_pseudoMetricType (R: realType) :=
  PseudoMetricType (Rcomplex_normedZmodType R) (Rcomplex_pseudoMetricMixin R).


Lemma Rcomplex_ball_ball_ (R: realType):
  @ball _ (Rcomplex_pseudoMetricType R ) = ball_ (fun x => `| x |).
Proof. by []. Qed.

Definition Rcomplex_pseudoMetricNormedZmodMixin (R: realType):=
  PseudoMetricNormedZmodule.Mixin (Rcomplex_ball_ball_ (R: realType)).

Canonical Rcomplex_pseudoMetricNormedZmodType (R: realType) :=
  PseudoMetricNormedZmodType R (Rcomplex_normedZmodType R)
                       (Rcomplex_pseudoMetricNormedZmodMixin R).

Lemma RnormcZ  (R: realType) (l : R) : forall (x : Rcomplex R),
    normc (l *: x) = `|l| * (normc x).
Proof.
by case=> ? ?; rewrite /normc //= !exprMn -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Definition Rcomplex_normedModMixin (R: realType):=
  @NormedModMixin R (Rcomplex_pseudoMetricNormedZmodType R)  _ (@RnormcZ R).

Canonical Rcomplex_normedModType (R: realType):=
  NormedModType R _ (Rcomplex_normedModMixin R).

End Rcomplex.



Notation  "f %:Rfun" :=
  (f : (Rcomplex_normedModType _) -> (Rcomplex_normedModType _))
  (at level 5,  format "f %:Rfun")  : complex_scope.

Notation  "v %:Rc" :=   (v : (Rcomplex _))
  (at level 5, format "v %:Rc")  : complex_scope.


Section CR_holo.
Variable (R: realType). (* because of proper_filter_nbhs'*)
Notation C := R[i].
Notation Rcomplex := (Rcomplex R).

(* TODO: find better names and clear the redudancies between lemmas *)

Lemma normcZ (l : R) : forall (x : Rcomplex),
    normc (l *: x) = `|l| * (normc x).
Proof.
by case=> ? ?; rewrite /normc //= !exprMn -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma realCZ (a : R) : forall (b : Rcomplex),  a%:C * b = a *: b.
Proof. move => [x y]; rewrite /(real_complex R) /scalec.
Admitted.

Lemma realC_alg (a : R) :  a *: (1%:Rc) = a%:C.
Proof.
apply/eqP; rewrite eq_complex; apply/andP.
by split; simpl; apply/eqP; rewrite ?mulr1 ?mulr0.
Qed.

Lemma scalecr: forall w: C^o, forall r : R, r *: (w: Rcomplex) = r%:C *: w .
Proof.
Proof. by move=> [a b] r; rewrite eqE_complex //=; split; simpc. Qed.

Lemma scalecAl (h : R) (x y : Rcomplex) : h *: (x * y) = h *: x * y.
Proof.
by move: h x y => h [a b] [c d]; simpc; rewrite -!mulrA -mulrBr -mulrDr.
Qed.

Lemma scalecV (h: R) (v: Rcomplex):
  h != 0 -> v != 0 -> (h *: v)^-1 = h^-1 *: v^-1. (* scaleCV *)
Proof.
by move=> h0 v0; rewrite scalecr invrM // ?unitfE ?eqCr // mulrC scalecr realCV.
Qed.

Definition C_RLalg := LalgType R (Rcomplex) scalecAl.

Lemma complex0 : 0%:C = 0 :> C.
Proof. rewrite eqE_complex //=. Qed.

(* Should Real_Line be a proper subtype of C *)
(* TBA: type of hausdorff topologicaltype *)

Lemma cvg_compE ( T U V : topologicalType)
      (f : T -> U) (g : V -> T)
      (F : set ( set V)) :
  cvg (f @ (g @ F)) <-> cvg (f \o g @ F).
Proof.
  by [].
Qed.

Lemma lim_compE ( T U V : topologicalType)
      (f : T -> U) (g : V -> T)
      (F : set ( set V)) :
  lim (f @ (g @ F)) = lim (f \o g @ F).
Proof.
  by [].
Qed.



(** Tentative proof with the @ notations **)

(*As norms on Rcomplex and C^o are equal, we are able to prove the following *)
(*would be great to generalize to equivalent norms *)

(* Notation "F --> l `in` T" := (@cvg_to T [filter of F] [filter of l]) (at level 70). *)


Lemma complex_limP (F : set (set C))  (l : C):
  (F --> (l: C^o)) <-> ( F --> (l : Rcomplex)).
Proof.
split; move => /= H A /=.
  move/(nbhs_ex (x:=l : Rcomplex_normedModType R)) =>  [[r r0] /=].
  rewrite -ball_normE /= => Br.
  have : nbhs (l: C^o) A.
    exists r%:C; first by rewrite /= ltcR.
    by move => y /=; rewrite /= ltcR; apply: Br.
  by move/(H A).
move/(nbhs_ex (x:=l : C^o))=>  [[[r ri] r0] /=].
move: r0; rewrite ltcE /= => /andP [/eqP ri0 r0] //.
rewrite -ball_normE ri0 complexr0 /= => Br.
have : nbhs (l: Rcomplex) A.
  by exists r; last by move => y /=; rewrite -ltcR; apply: Br.
by move/(H A).
Qed.

Lemma complex_cvgP (F : set (set C)) (FF: Filter F) :
  [cvg F in [topologicalType of Rcomplex]] <->
   [cvg F in [topologicalType of C^o]].
Proof.
split; move/cvg_ex => /= [l H].
apply: (cvgP (l : C^o)).
  by apply/complex_limP.
by apply: (cvgP (l%:Rc)); apply/complex_limP.
Qed.


Lemma complex_liminP (F : set (set C)) (FF: ProperFilter F):
   [lim F in [topologicalType of Rcomplex]] =
   [lim F in [topologicalType of C^o]].
Proof.
case: (EM ([cvg F in [topologicalType of C^o]])).
  move/cvg_ex=> /= [l Fl].
  rewrite (norm_cvg_lim (l := l)) //. 
  by apply: (@norm_cvg_lim _ (Rcomplex_normedModType R)); apply/complex_limP.
move => dvg; pose copy := dvg ;move/dvgP: copy => ->.
by move/complex_cvgP/dvgP: dvg => ->.
Qed.

(* here notations are misleading and don't show the different topologies
at the target *)


Lemma Rdiff (f : C^o -> C^o) c v:
  (Rderivable_fromcomplex f c v) <->
  (derivable (f%:Rfun) c v).
Proof.
rewrite /Rderivable_fromcomplex /derivable cvg_compE.
have -> :  (fun h : (R[i])^o => h^-1 * ((f \o shift c) (h *: v) - f c)) \o
           realC (R:=R)  =
          (fun h : R => h^-1 *: ((f%:Rfun \o shift c) (h *: v%:Rc) - f c)).
  by apply: funext => h /=; rewrite Inv_realC -scalecM -!scalecr.
by split;  move/complex_cvgP => /=.
Qed.



Lemma Rdiff1 (f : C^o -> C^o) c:
          lim ( (fun h : C^o => h^-1 *: ((f \o shift c) (h) - f c))
                 @ (((@realC R))@ (nbhs' (0:R^o))))
         = 'D_1 (f%:Rfun) c%:Rc.
Proof.
rewrite /derive lim_compE.
suff -> :  (fun h : (R[i])^o => h^-1 * ((f \o shift c) (h ) - f c)) \o
realC (R:=R) = fun h : R => h^-1 *: ((f%:Rfun \o shift c) (h *: (1%:Rc)) - f c).
  by rewrite complex_liminP /=.
apply: funext => h /=.
by rewrite Inv_realC -scalecM -!scalecr realC_alg.
Qed.


Lemma Rdiffi (f : C^o -> C^o) c:
         lim ( (fun h : C^o => h^-1 *: ((f \o shift c) (h * 'i) - f c))
                 @ (((@realC R))@ (nbhs' (0:R^o))))
         = 'D_('i) (f%:Rfun)  c%:Rc.
Proof.
rewrite /derive lim_compE.
suff -> :  (fun h : (R[i])^o => h^-1 * ((f \o shift c) (h * 'i) - f c)) \o
realC (R:=R) = fun h : R => h^-1 *: ((f%:Rfun \o shift c) (h *: ('i%:Rc)) - f c).
  by rewrite complex_liminP /=.
apply: funext => h /=.
by rewrite Inv_realC -scalecM -!scalecr realCZ.
Qed.

Lemma continuous_near (T U: topologicalType) (f: T -> U) (P : set U) (a : T):
 (f @ a --> f a) -> ((\forall x \near nbhs (f a), P x)
                           -> (\forall y \near nbhs a, P (f y))).
Proof. by move/(_ P) => /=; near_simpl. Qed.


Lemma holomorphicP (f : C^o -> C^o)  (c: C^o) : holomorphic f c <-> derivable f c 1.
Proof.
rewrite /holomorphic /derivable.
suff -> : (fun h : C => h^-1 *: ((f \o shift c) h - f c)) =
         ((fun h : C => h^-1 *: ((f \o shift c) (h *: 1) - f c))) by [].
by apply: funext =>h; rewrite complexA.
Qed.

(*TBA normedType- Cyril's suggestion *)
Lemma nbhs'0_le  (K : numFieldType) (V : normedModType K) e :
   0 < e -> \forall x \near (nbhs' (0 : V)), `|x| <= e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
rewrite -ball_normE /= sub0r normrN => le_nxe _ .
by rewrite ltW.
Qed.


Lemma nbhs0_le  (K : numFieldType) (V : normedModType K) e :
   0 < e -> \forall x \near (nbhs' (0 : V)), `|x| <= e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
rewrite -ball_normE /= sub0r normrN => le_nxe _ .
by rewrite ltW.
Qed.

Lemma nbhs'0_lt  (K : numFieldType) (V : normedModType K) e :
   0 < e -> \forall x \near (nbhs' (0 : V)), `|x| < e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
by rewrite -ball_normE /= sub0r normrN.
Qed.

Lemma nbhs0_lt  (K : numFieldType) (V : normedModType K) e :
   0 < e -> \forall x \near (nbhs' (0 : V)), `|x| < e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
by rewrite -ball_normE /= sub0r normrN.
Qed.

Lemma normc_ge_Im (x : R[i]) : `|complex.Im x|%:C <= `|x|.
Proof.
by case: x => a b; simpc; rewrite -sqrtr_sqr ler_wsqrtr // ler_addr sqr_ge0.
Qed.

Notation Rdifferentiable f c := (differentiable f%:Rfun c%:Rc).

Lemma Diff_CR_holo (f : C^o -> C^o)  (c: C):
   (Rdifferentiable f c) /\
  (CauchyRiemanEq f c)
  -> (holomorphic f c).
Proof.
move => [] H; have derf := H ; move: H.
move/diff_locally /eqaddoP => der.
(* TODO : diff_locally to be renamed diff_nbhs *)
rewrite /CauchyRiemanEq Rdiff1 Rdiffi.
move => CR.
rewrite /holomorphic; apply: (cvgP (('D_1 f%:Rfun c) : C^o)).
apply/(cvg_distP (('D_1 f%:Rfun c) : C^o)).
move => eps eps_lt0 /=.
pose er := Re eps.
have eq_ereps := gt0_realC eps_lt0.
have er_lt0 : 0 < er/2 by rewrite mulr_gt0 // -realC_gt0.
move /(_ (er/2) er_lt0): der; rewrite /= nearE.
move => /(@nbhs_ex _  _ (0 : Rcomplex_normedModType R)) [[d d0]] /= der.
rewrite nearE /= nbhs_filterE.
exists d%:C; first by rewrite /= ltcR.
move=> z /=; rewrite sub0r normrN => lt_nzd z0.
have ltr_nzd : (normc z) < d by rewrite -ltcR.
have -> : eps  =  `|z|^-1 * `|z| * eps.
  rewrite [X in X*_]mulrC mulfV; first by rewrite  ?mul1r.
  by apply/eqP => /normr0_eq0; move/eqP: z0.  (*ugly*)
rewrite -mulrA ltr_pdivl_mull ?normr_gt0 // -normrM mulrDr mulrN.
rewrite scalecM mulrA mulfV // mul1r.
move /(_ z): der; rewrite -ball_normE /= sub0r normrN => /(_ ltr_nzd).
rewrite -[`|(_)z|]/(`|_ z + _ z|) /=.
set b := ((cst (f c)) : C -> Rcomplex).
rewrite -[(- (b + _)) z]/(- ( f c + _ z))  /= mulrC opprD.
set x := Re z; set y := Im z.
have zeq : z = x *: 1 %:Rc + y *: 'i%:Rc.
  by rewrite [LHS]complexE /= realC_alg scalecr scalecM [in RHS]mulrC.
rewrite [X in 'd _ _ X]zeq addrC linearP linearZ /= -!deriveE //.
rewrite -CR (scalecAl y) (* why scalec *) -scalecM !scalecr.
rewrite -(scalerDl  (('D_1 f%:Rfun c%:Rc): C^o) x%:C). (*clean, do it in Rcomplex *)
rewrite addrAC -!scalecr -realC_alg -zeq. (*clean*)
rewrite addrC [X in (-_ + X)]addrC -[X in `|_ + X|]opprK -opprD normrN scalecM.
rewrite -lecR => H. rewrite /normr /=. apply: le_lt_trans; first by exact H.
rewrite eq_ereps realCM ltcR /normr /= ltr_pmul2l ?normc_gt0 //.
rewrite /er -[X in (_ < X)]mulr1 ltr_pmul2l //= ?invf_lt1 ?ltr1n //.
rewrite -ltr0c -eq_ereps //.
Qed. 

(* (* Partial proof using continuity of partial derivatices and resketching *)
(*   continuity of parital der => diff *) *)
(* Lemma Der_CR_holo (f : C^o -> C^o)  (c: C): *)
(*   (forall d v : C^o, Rderivable_fromcomplex f d v)/\ *)
(*    (('D_'i f%:Rfun)@ c%:Rc --> 'D_'i f%:Rfun c%:Rc) /\ *)
(*    (CauchyRiemanEq f c) *)
(*   -> (holomorphic f c). *)
(* Proof. *)
(* move => [der] [CL]; rewrite /CauchyRiemanEq Rdiff1 Rdiffi. *)
(* set  L: C^o := (X in 'i * X) => CR. *)
(* suff lem: (fun h : C^o => h^-1 *: ((f \o shift c) h - f c)) *)
(*            @ nbhs' 0 --> L. *)
(*   by rewrite /holomorphic; apply: (cvgP L). *)
(* move => A /=; simpl in (type of A). *)
(* move => H; have nbhsAL := H; move: H. *)
(* move/(nbhs_ex (x:=L : C^o)) => [[d d0]  /= AL]. *)
(* pose dr := Re d. *)
(* have eq_drd := gt0_realC d0. *)
(* pose dr3 := (dr/2%:R). *)
(* pose dr' := (dr/2%:R/2%:R). *)
(* have lt0_dr3 : 0 < dr3 by rewrite !pmulr_lgt0 // -ltr0c -eq_drd. *)
(* have lt0_dr' : 0 < dr' by rewrite !pmulr_lgt0 // -ltr0c -eq_drd. *)
(* move: (der c (1%:Rc)) ; rewrite Rdiff=> /derivable_nbhsP /eqaddoP /(_ dr'). *)
(*  elim; last by []; move => rx rx0 /= Dx. *)
(* have foo : Filter ('D_'i f%:Rfun @ c%:Rc).  (* complicated - issue with filteredtype *) *)
(*    apply: fmap_filter; apply: filter_from_filter; first by exists 1. *)
(*     move => i j i0 j0; exists (minr i j); first by rewrite /= lt_minr; apply/andP; split. *)
(*     move => r /= H; split; apply: lt_le_trans. *)
(*       by exact:H ; rewrite le_minl; apply/orP; left. *)
(*       by rewrite le_minl; apply/orP; left. *)
(*     by exact:H ; rewrite le_minl; apply/orP; right. *)
(*     by rewrite le_minl; apply/orP; right. *)
(* move/cvg_dist: CL => /(_ dr3 lt0_dr3); rewrite nearE. *)
(* move => /(@nbhs_ex _ (Rcomplex_pseudoMetricType R)) [[e' e0] /=]. *)
(* rewrite -ball_normE /= /normr /= => Bc. *)
(* near (nbhs' (0 : C^o) : set (set C^o)) => e. *)
(* exists (`|e| : C). *)
(*   near: e; rewrite nearE nbhs_filterE. *)
(*   by apply/(@nbhs_ballP); exists 1; first by []; move => x _ ; rewrite /= normr_gt0. *)
(* move => z /=; rewrite sub0r normrN => nze z0 ; apply: AL. *)
(* rewrite -ball_normE /=. *)
(* set x := Re z; set y := complex.Im z. *)
(* have zxy : z = x +i* y by apply/eqP; rewrite eq_complex; apply/andP;split. *)
(* have -> : d =  `|z|^-1 * `|z| * d. *)
(*   rewrite [X in X*_]mulrC mulfV; first by rewrite  ?mul1r. *)
(*   by apply/eqP => /normr0_eq0; move/eqP: z0.  (*ugly*) *)
(* rewrite -mulrA ltr_pdivl_mull ?normr_gt0 // -normrM mulrDr mulrN. *)
(* rewrite scalecM mulrA mulfV // mul1r. *)
(* have -> : z * L - (f (z + c) - f c) = *)
(*           ((f c + x *: 'D_1 f%:Rfun c)%:Rc) - f (c + x *: 1%:Rc ) *)
(*           + (f (c + x *: 1%:Rc) - (f(c + x *: 1%:Rc + y *: 'i%:Rc) - *)
(*             y *: 'D_'i f%:Rfun c)). *)
(*   have -> : z = (x *: 1%:Rc + y *: 'i%:Rc) *)
(*   by rewrite eqE_complex /=; rewrite !mulr1 !mulr0 addr0 add0r. *)
(*   rewrite  subrKA !scalecr !scalecM -CR  !/L !opprB. *)
(*   rewrite -[RHS]addrA [X in _ = _ + X]addrA mulrA-[in RHS]mulrDl. *)
(*   rewrite addrCA mulr1 complexiE. *)
(*   by rewrite [X in (- f X)]addrAC [X in (- f (X + _))]addrC. *)
(* have lem1x:  `|x| * dr' <=  (normc z * dr'). *)
(*     rewrite -lter_pdivr_mulr // -mulrA mulfV; last by apply: lt0r_neq0. *)
(*     by rewrite mulr1 -lecR normc_ge_Re. *)
(* have lem2: normc z * dr' < normc z * dr3. *)
(*     rewrite -lter_pdivr_mulr /dr3 /dr'?mulr_gt0 -?complex_gt0E//. *)
(*     rewrite mulrAC -mulrA gtr_pmulr ?normc_gt0 // invf_div -!mulrA (mulrA _ dr). *)
(*     rewrite mulVr ?unitf_gt0 ?mul1r -?complex_gt0E //. *)
(*     by rewrite mulrA mulfV ?div1r ?invf_lt1 ?ltr1n //=. *)
(* have nxr: `|x|< rx. *)
(*     apply: le_lt_trans; first by rewrite -lecR; exact (normc_ge_Re z). *)
(*     rewrite -ltcR /= ; apply: lt_le_trans; first by exact nze. *)
(*     by near: e; rewrite nbhs_filterE; apply: nbhs'0_le; rewrite ltcR. *)
(* have ltDx: normc((f c + x *: 'D_1 f%:Rfun c)%:Rc - f (c + x *: 1%:Rc)) *)
(*                < (normc z)*dr3. *)
(* (*the use of normc is  necessary to enforce addition in Rcomplex on the left side of the inequality *) (* there is a missing join between zmodules structure of C^o and Rcomplex *) *)
(*   move: Dx =>  /(_ x) /=; rewrite sub0r normrN. *)
(*   move => /(_ nxr) /=; rewrite -[`|(_)x|]/(`|_ x + _ x|) /=. *)
(*   set b := ((cst (f c)) : R -> C^o). *)
(*   rewrite -[(- (b + _)) x]/(- ( f c + _ x)) /= mulrC. *)
(*   move/le_trans => /(_ _ lem1x) /(le_lt_trans) /(_ lem2). *)
(*   by rewrite -opprB normrN [X in - f X]addrC. *)
(* apply: le_lt_trans; first by apply ler_norm_add. *)
(* apply: le_lt_trans;first by apply: ler_add. *)
(* have -> : `|z|*d= `|z|*dr3%:C+ `|z|*dr3%:C. *)
(*   rewrite -!mulrDl /dr3 -realCM -eq_drd mulrCA [RHS]mulrC. *)
(*   apply/(@mulIf _ d^-1); first by apply:invr_neq0; apply: lt0r_neq0. *)
(*   rewrite -!mulrA !mulfV ?lt0r_neq0 // !mulr1 complexV //.  admit. (*argh*) *)
(* apply: ltr_le_add; first by rewrite realCM ltcR. *)
(* rewrite opprB addrCA. *)
(* have [a leny ->] : exists2 a : R, `|a| <= `|y| & *)
(*                    (f (c + x *: 1%:Rc) - f (c + x *: 1%:Rc + y *: 'i%:Rc) = *)
(*                            - y *: 'D_'i f%:Rfun (c + (x *: 1%:Rc+ a*:'i%:Rc))). *)
(* (* use MVT *) (* distinguish real and complex projections *) admit. *)
(* rewrite scaleNr !scalecr !scalecM -mulrBr normrM ler_pmul //. *)
(*   by rewrite real_norm  normc_ge_Im. *)
(* rewrite ltW // ltcR; apply: Bc. *)
(* rewrite opprD !addrA addrN add0r normcN mulr1 /normc /=. *)
(* rewrite !mulr0 mul0r !add0r addr0 subr0 mulr1. *)
(* apply: le_lt_trans; last first. *)
(*   apply: lt_le_trans; first by rewrite -ltcR; exact nze. *)
(*   rewrite -lecR; near: e; rewrite nbhs_filterE; apply: nbhs'0_le. *)
(*     by rewrite ltcR. *)
(* case: (eqVneq z 0). *)
(*       rewrite eqE_complex. admit. *)
(* rewrite -normr_gt0  ltcR !/normc zxy sqrtr_gt0 => lem; rewrite ler_sqrt //. *)
(* rewrite ler_add //  -real_normK -?(@real_normK _ y) ?num_real //. *)
(* rewrite ler_sqr // !nnegrE !normr_ge0 //. *)
(* Admitted. *)



(* (* failed proof using continuity of partial derivative *) *)
(* Lemma Der_CR_holo' (f : C^o -> C^o)  (c: C): *)
(*   (forall d v : C^o, Rderivable_fromcomplex f d v)/\ *)
(*    (('D_'i f%:Rfun)@ c%:Rc --> 'D_'i f%:Rfun c%:Rc) /\ *)
(*    (CauchyRiemanEq f c) *)
(*   -> (holomorphic f c). *)
(* Proof. *)
(* move => [der] [CL]; rewrite /CauchyRiemanEq Rdiff1 Rdiffi. *)
(* set L: C^o := (X in 'i * X) => CR. *)
(* suff lem: (fun h : C^o => h^-1 *: ((f \o shift c) h - f c)) *)
(*            @ nbhs' 0 --> L. *)
(*   by rewrite /holomorphic; apply: (cvgP L). *)
(* move => A /=; simpl in (type of A). *)
(* move => H; have nbhsAL := H; move: H. *)
(* move/(nbhs_ex (x:=L : C^o)) => [[d d0]  /= AL]. *)
(* pose dr := Re d. *)
(* have eq_drd := gt0_realC d0. *)
(* pose dr3 := (dr/3%:R). *)
(* pose dr' := (dr/3%:R/2%:R). *)
(* have lt0_dr3 : 0 < dr3 by rewrite !pmulr_lgt0 // -ltr0c -eq_drd. *)
(* have lt0_dr' : 0 < dr' by rewrite !pmulr_lgt0 // -ltr0c -eq_drd. *)
(* have AL' := AL. *)
(* move: (der c (1%:Rc)) ; rewrite Rdiff=> /derivable_nbhsP /eqaddoP /(_ dr'). *)
(*  elim; last by []; move => rx rx0 /= Dx. *)
(* move: (der c ('i%:Rc)); rewrite Rdiff. *)
(*   move => /derivable_nbhsP /eqaddoP /(_ dr'). *)
(*   elim; last by []; move => ry ry0 /= Dy. *)
(* near (nbhs' (0 : C^o) : set (set C^o)) => e. *)
(* exists (`|e| : C). *)
(*   near: e; rewrite nearE nbhs_filterE. *)
(*   by apply/(@nbhs_ballP); exists 1; first by []; move => x _ ; rewrite /= normr_gt0. *)
(* move => z /=; rewrite sub0r normrN => nze z0 ; apply: AL. *)
(* rewrite -ball_normE /=. *)
(* set x := Re z; set y := complex.Im z. *)
(* have -> : d =  `|z|^-1 * `|z| * d. *)
(*   rewrite [X in X*_]mulrC mulfV; first by rewrite  ?mul1r. *)
(*   by apply/eqP => /normr0_eq0; move/eqP: z0.  (*ugly*) *)
(* rewrite -mulrA ltr_pdivl_mull ?normr_gt0 // -normrM mulrDr mulrN. *)
(* rewrite scalecM mulrA mulfV // mul1r. *)
(* have -> : z * L - (f (z + c) - f c) = *)
(*           (f c + x *: 'D_1 f%:Rfun c)%:Rc - f (c + x *: 1%:Rc ) *)
(*           + (f (c + x *: 1%:Rc) + *)
(*              (- f(c + x *: 1%:Rc + y *: 'i%:Rc) + *)
(*             y *: 'D_'i f%:Rfun (c + x *: 1%:Rc))) *)
(*         - (y *:  'D_'i f%:Rfun  (c + x *: 1%:Rc) + (x *: 'D_1 f%:Rfun c - z*L)). *)
(*   rewrite subrKA -[in RHS]addrA -[in RHS]addrA addrKA. *)
(*   rewrite -[in RHS]opprB -[X in _= _ - X]addrA addrKA !opprB !opprK. *)
(*   rewrite [X in _ =_ + X]addrC [RHS]addrCA [X in - f X]addrC. *)
(*   suff -> : z = (x *: 1%:Rc + y *: 'i%:Rc) by []. *)
(*   by rewrite eqE_complex /=; rewrite !mulr1 !mulr0 addr0 add0r. *)

(* have lem1y:  `|y| * dr' <=  (normc z * dr'). *)
(*     rewrite -lter_pdivr_mulr // -mulrA mulfV; last by apply: lt0r_neq0. *)
(*       by rewrite mulr1 -lecR normc_ge_Im. *)
(* have lem1x:  `|x| * dr' <=  (normc z * dr'). *)
(*     rewrite -lter_pdivr_mulr // -mulrA mulfV; last by apply: lt0r_neq0. *)
(*     by rewrite mulr1 -lecR normc_ge_Re. *)
(* have lem2: normc z * dr' < normc z * dr3. *)
(*     rewrite -lter_pdivr_mulr /dr3 /dr'?mulr_gt0 -?complex_gt0E//. *)
(*     rewrite mulrAC -mulrA gtr_pmulr ?normc_gt0 // invf_div -!mulrA (mulrA _ dr). *)
(*     rewrite mulVr ?unitf_gt0 ?mul1r -?complex_gt0E //. *)
(*     by rewrite mulrA mulfV ?div1r ?invf_lt1 ?ltr1n //=. *)
(* have nxr: `|x|< rx. *)
(*     apply: le_lt_trans; first by rewrite -lecR; exact (normc_ge_Re z). *)
(*     rewrite -ltcR /= ; apply: lt_le_trans; first by exact nze. *)
(*     by near: e; rewrite nbhs_filterE; apply: nbhs'0_le; rewrite ltcR. *)
(* have nyr: `|y|< ry. *)
(*     apply: le_lt_trans; first by rewrite -lecR; exact (normc_ge_Im z). *)
(*     rewrite -ltcR /= ; apply: lt_le_trans; first by exact nze. *)
(*     by near: e; rewrite nbhs_filterE; apply: nbhs'0_le; rewrite ltcR. *)
(* have ltDx: normc((f c + x *: 'D_1 f%:Rfun c)%:Rc - f (c + x *: 1%:Rc)) *)
(*                < (normc z)*dr3. *)
(* (*the use of normc is  necessary to enforce addition in Rcomplex on the left side of the inequality *) (* there is a missing join between zmodules structure of C^o and Rcomplex *) *)
(*   move: Dx =>  /(_ x) /=; rewrite sub0r normrN. *)
(*   move => /(_ nxr) /=; rewrite -[`|(_)x|]/(`|_ x + _ x|) /=. *)
(*   set b := ((cst (f c)) : R -> C^o). *)
(*   rewrite -[(- (b + _)) x]/(- ( f c + _ x)) /= mulrC. *)
(*   move/le_trans => /(_ _ lem1x) /(le_lt_trans) /(_ lem2). *)
(*   by rewrite -opprB normrN [X in - f X]addrC. *)
(* (* have ltDy: *) *)
(* (*  normc (f (c + x *: 1%:Rc) + *) *)
(* (*      (- f(c + x *: 1%:Rc + y *: 'i%:Rc) + y *: 'D_'i f%:Rfun (c + x *: 1%:Rc))) *) *)
(* (*      < (normc z)*dr3. *) *)
(* (*   move:  Dy =>  /(_ y) /=; rewrite sub0r normrN. *) *)
(* (*   move => /(_ nyr) /=; rewrite -[`|(_)y|]/(`|_ y + _ y|) /=. *) *)
(* (*   set b := ((cst (f (c + x *: 1%:Rc))) : R -> C^o). *) *)
(* (*   rewrite -[(- (b + _)) y]/(- ( f (_) + _ y)) /= mulrC. *) *)
(* (*   move/le_trans => /(_ _ lem1y) /(le_lt_trans) /(_ lem2). *) *)
(* (*   rewrite complexiE [X in f(X)]addrC -opprB normrN. *) *)
(* (*   by move => H; rewrite [X in _ + X ]addrC addrA. *) *)
(* have CLy : normc ((y *:  'D_'i f%:Rfun  (c + x *: 1%:Rc) + *)
(*                    (x *: 'D_1 f%:Rfun c - z*L)))  <= (normc z)*dr3. *)
(*   rewrite -(subrKA (y *: 'D_'i f%:Rfun c)). *)
(*   have -> : y *: 'D_'i f%:Rfun c + (x *: 'D_1 f%:Rfun c - z * L) = 0. *)
(*     rewrite -CR /L addrA scalecAl !scalecr !scalecM -mulrDl [X in X *_]addrC. *)
(*     suff -> : (x%:C + y%:C * 'i) = z by rewrite addrN. *)
(*     by rewrite mulrC [RHS]complexE /=. *)
(*   rewrite addr0 -scalerBr normcZ ler_pmul ?normr_ge0 ?normc_ge0 -?lecR ?normc_ge_Im //. *)
(*   rewrite lecR. move /cvg_dist : CL. *)
(*   have : Filter ('D_'i f%:Rfun @ c%:Rc). (* why is it so complicated *) *)
(*    apply: fmap_filter; apply: filter_from_filter; first by exists 1. *)
(*     move => i j i0 j0; exists (minr i j); first by rewrite /= lt_minr; apply/andP; split. *)
(*     move => r /= H; split; apply: lt_le_trans. *)
(*       by exact:H ; rewrite le_minl; apply/orP; left. *)
(*       by rewrite le_minl; apply/orP; left. *)
(*     by exact:H ; rewrite le_minl; apply/orP; right. *)
(*     by rewrite le_minl; apply/orP; right. *)
(*   move => H /(_ H dr3 lt0_dr3). *)
(*   rewrite nearE /= =>  /(@nbhs_ex _ (Rcomplex_pseudoMetricType R)) [[e' e0] /= Bc]. (*argh*) *)
(*   rewrite ltW // -opprB normcN; apply: Bc. *)
(*   rewrite -ball_normE /= opprD addrA addrN sub0r normrN normmZ. *)
(*   rewrite {2}/normr /= expr0n addr0 expr1n sqrtr1 mulr1. *)
(*   apply: le_lt_trans; first by apply: (real_normc_ler x y). *)
(*   rewrite -ltcR normcR. *)
(*   have <- : z = x +i* y by rewrite eqE_complex /=; split. *)
(*   apply: lt_le_trans; first by exact: nze. *)
(*     near: e; rewrite locked_withE /= => x0. *)
(*      admit. (* near `|_| *) *)
(* apply: le_lt_trans; first by apply ler_norm_add. *)
(* apply: le_lt_trans;first by apply: ler_add; first by apply:ler_norm_add. *)
(* have -> : `|z|*d= `|z|*dr3%:C+ `|z|*dr3%:C + `|z|*dr3%:C. *)
(*   rewrite -!mulrDl /dr3 -realCM -eq_drd mulrCA [RHS]mulrC. *)
(*   apply/(@mulIf _ d^-1); first by apply:invr_neq0; apply: lt0r_neq0. *)
(*   rewrite -!mulrA !mulfV ?lt0r_neq0 // !mulr1 complexV //; admit. (*argh*) *)
(* apply: ltr_le_add; last by rewrite realCM lecR normcN. *)
(*   apply: ltr_add; rewrite realCM ltcR //=. *)
(* Admitted. *)

(* Lemma Der_CR_holo'' (f : C^o -> C^o)  (c: C): *)
(*   (forall d v : C^o, Rderivable_fromcomplex f d v)/\ *)
(*    {for c, continuous f%:Rfun} /\ *)
(*    (CauchyRiemanEq f c) *)
(*   -> (holomorphic f c). *)
(* Proof. *)
(* move => [der] [Cf]; rewrite /CauchyRiemanEq Rdiff1 Rdiffi. *)
(* set L: C^o := (X in 'i * X) => CR. *)
(* suff : (fun h : C^o => h^-1 *: ((f \o shift c) h - f c)) *)
(*            @ nbhs' 0 --> L. *)
(*   by rewrite /holomorphic; apply: (cvgP L). *)
(* move => A /=; simpl in (type of A). *)
(* move => H; have nbhsAL := H; move: H. *)
(* move/(nbhs_ex (x:=L : C^o)) => [[d d0]  /= AL]. *)
(* pose dr := Re d. *)
(* have eq_drd := gt0_realC d0. *)
(* pose dr3 := (dr/4%:R). (*change name*) *)
(* pose dr' := (dr/4%:R/2%:R). *)
(* have lt0_dr3 : 0 < dr3 by rewrite !pmulr_lgt0 // -ltr0c -eq_drd. *)
(* have lt0_dr' : 0 < dr' by rewrite !pmulr_lgt0 // -ltr0c -eq_drd. *)
(* have AL' := AL. *)
(* have foo: Filter (f @ (c%:Rc)). apply: fmap_filter. (*issue with Filter on Rcomplex *) admit. *)
(* move/cvg_distP /(_ dr' lt0_dr'): Cf => Cf. *)
(* move: (der c (1%:Rc)) ; rewrite Rdiff=> /derivable_nbhsP /eqaddoP /(_ dr'). *)
(*  elim; last by []; move => rx rx0 /= Dx. *)
(* move: (der c ('i%:Rc)); rewrite Rdiff. *)
(*   move => /derivable_nbhsP /eqaddoP /(_ dr'). *)
(*   elim; last by []; move => ry ry0 /= Dy. *)
(* near (nbhs' (0 : C^o) : set (set C^o)) => e. *)
(* exists (`|e| : C). *)
(*   near: e; rewrite nearE nbhs_filterE. *)
(*   by apply/(@nbhs_ballP); exists 1; first by []; move => x _ ; rewrite /= normr_gt0. *)
(* move => z /=; rewrite sub0r normrN => nze z0 ; apply: AL. *)
(* rewrite -ball_normE /=. *)
(* set x := Re z; set y := complex.Im z. *)
(* have -> : d =  `|z|^-1 * `|z| * d. *)
(*   rewrite [X in X*_]mulrC mulfV; first by rewrite  ?mul1r. *)
(*   by apply/eqP => /normr0_eq0; move/eqP: z0.  (*ugly*) *)
(* rewrite -mulrA ltr_pdivl_mull ?normr_gt0 // -normrM mulrDr mulrN. *)
(* rewrite scalecM mulrA mulfV // mul1r. *)
(* have -> : z * L - (f (z + c) - f c) = (* not working *) *)
(*          (f (c + y *: 'i%:Rc ) - f (c)) + *)
(*          (f c - f (c + z)) + *)
(*          (f (c + x *: 1%:Rc ) - f c) + *)
(*          ((f c + x *: 'D_1 f%:Rfun c)%:Rc - f (c + x *: 1%:Rc )) *)
(*        + (f c + y *: 'D_'i f%:Rfun c - f(c + y *: 'i%:Rc)). *)
(*   have -> : z * L = y *: 'D_'i f%:Rfun c + x *: 'D_1 f%:Rfun c. *)
(*      have <- : (x%:C + y%:C * 'i) = z by rewrite [RHS]complexE /= mulrC. *)
(*      by rewrite -CR /L mulrDl addrC !scalecr !scalecM mulrA. *)
(*   admit. *)
(* have lem1y:  `|y| * dr' <=  (normc z * dr'). *)
(*     rewrite -lter_pdivr_mulr // -mulrA mulfV; last by apply: lt0r_neq0. *)
(*       by rewrite mulr1 -lecR normc_ge_Im. *)
(* have lem1x:  `|x| * dr' <=  (normc z * dr'). *)
(*     rewrite -lter_pdivr_mulr // -mulrA mulfV; last by apply: lt0r_neq0. *)
(*     by rewrite mulr1 -lecR normc_ge_Re. *)
(* have lem2: normc z * dr' < normc z * dr3. *)
(*     rewrite -lter_pdivr_mulr /dr3 /dr'?mulr_gt0 -?complex_gt0E//. *)
(*     rewrite mulrAC -mulrA gtr_pmulr ?normc_gt0 // invf_div -!mulrA (mulrA _ dr). *)
(*     rewrite mulVr ?unitf_gt0 ?mul1r -?complex_gt0E //. *)
(*     by rewrite mulrA mulfV ?div1r ?invf_lt1 ?ltr1n //=. *)
(* have nxr: `|x|< rx. *)
(*     apply: le_lt_trans; first by rewrite -lecR; exact (normc_ge_Re z). *)
(*     rewrite -ltcR /= ; apply: lt_le_trans; first by exact nze. *)
(*     by near: e; rewrite nbhs_filterE; apply: nbhs'0_le; rewrite ltcR. *)
(* have nyr: `|y|< ry. *)
(*     apply: le_lt_trans; first by rewrite -lecR; exact (normc_ge_Im z). *)
(*     rewrite -ltcR /= ; apply: lt_le_trans; first by exact nze. *)
(*     by near: e; rewrite nbhs_filterE; apply: nbhs'0_le; rewrite ltcR. *)
(* have ltDx: normc((f c + x *: 'D_1 f%:Rfun c)%:Rc - f (c + x *: 1%:Rc)) *)
(*                < (normc z)*dr3. *)
(* (*the use of normc is  necessary to enforce addition in Rcomplex on the *)
(* left side of the inequality *) (* there is a missing join between zmodules *)
(* structure of C^o and Rcomplex *) *)
(*   move: Dx => /(_ x) /=; rewrite sub0r normrN. *)
(*   move => /(_ nxr) /=; rewrite -[`|(_)x|]/(`|_ x + _ x|) /=. *)
(*   set b := ((cst (f c)) : R -> C^o). *)
(*   rewrite -[(- (b + _)) x]/(- ( f c + _ x)) /= mulrC. *)
(*   move/le_trans => /(_ _ lem1x) /(le_lt_trans) /(_ lem2). *)
(*   by rewrite -opprB normrN [X in - f X]addrC. *)
(* have ltDy: *)
(*  normc (f c + y *: 'D_'i f%:Rfun c - f(c + y *: 'i%:Rc)) *)
(*      < (normc z)*dr3. *)
(*   move: Dy => /(_ y) /=; rewrite sub0r normrN. *)
(*   move => /(_ nyr) /=; rewrite -[`|(_)y|]/(`|_ y + _ y|) /=. *)
(*   set b := ((cst (f c)) : R -> C^o). *)
(*   rewrite -[(- (b + _)) y]/(- ( f (_) + _ y)) /= mulrC. *)
(*   move/le_trans => /(_ _ lem1y) /(le_lt_trans) /(_ lem2). *)
(*   by rewrite complexiE [X in f(X)]addrC -opprB -opprB opprK normrN. *)
(* have ltfy :  normc (f (c + y *: 'i%:Rc ) - f (c)) < dr'. admit. *)
(* have ltfz : normc (f c - f (c + z)) < dr'. admit. *)
(* have ltfx : normc (f (c + x *: 1%:Rc ) - f c) < dr'. admit. *)
(* (* have CLy : normc (y *:  'D_'i f%:Rfun c  + (x *: 'D_1 f%:Rfun c - z*L))  <= (normc z)*dr3. *) *)
(* (*   rewrite -(subrKA (y *: 'D_'i f%:Rfun c)). *) *)
(* (*   have -> : y *: 'D_'i f%:Rfun c + (x *: 'D_1 f%:Rfun c - z * L) = 0. *) *)
(* (*     rewrite -CR /L addrA scalecAl !scalecr !scalecM -mulrDl [X in X *_]addrC. *) *)
(* (*     suff -> : (x%:C + y%:C * 'i) = z by rewrite addrN. *) *)
(* (*     by rewrite mulrC [RHS]complexE /=. *) *)
(* (*   rewrite addr0 -scalerBr normcZ ler_pmul ?normr_ge0 ?normc_ge0 -?lecR ?normc_ge_Im //.  *) *)
(* (*   rewrite lecR. move /cvg_dist : CL. *) *)
(* (*   have : Filter ('D_'i f%:Rfun @ c%:Rc). (* why is it so complicated *) *) *)
(* (*    apply: fmap_filter; apply: filter_from_filter; first by exists 1. *) *)
(* (*     move => i j i0 j0; exists (minr i j); first by rewrite lt_minr; apply/andP; split. *) *)
(* (*     move => r /= H; split; apply: lt_le_trans. *) *)
(* (*       by exact:H ; rewrite le_minl; apply/orP; left. *) *)
(* (*       by rewrite le_minl; apply/orP; left. *) *)
(* (*     by exact:H ; rewrite le_minl; apply/orP; right. *) *)
(* (*     by rewrite le_minl; apply/orP; right. *) *)
(* (*   move => H /(_ H dr3 lt0_dr3). *) *)
(* (*   rewrite nearE /= =>  /(@nbhs_ex _ (Rcomplex_pseudoMetricType R)) [[e' e0] /= Bc]. (*argh*) *) *)
(* (*   rewrite ltW // -opprB normcN; apply: Bc. *) *)
(* (*   rewrite -ball_normE /= opprD addrA addrN sub0r normrN normmZ. *) *)
(* (*   rewrite {2}/normr /= expr0n addr0 expr1n sqrtr1 mulr1. *) *)
(* (*   apply: le_lt_trans; first by apply: (real_normc_ler x y). *) *)
(* (*   rewrite -ltcR normcR. *) *)
(* (*   have <- : z = x +i* y by rewrite eqE_complex /=; split. *) *)
(* (*   apply: lt_le_trans; first by exact: nze. *) *)
(* (*     near: e; rewrite locked_withE /= => x0. *) *)
(* (*      admit. (* near `|_| *) *) *)
(* apply: le_lt_trans; first by apply ler_norm_add. *)
(* apply: le_lt_trans;first by apply: ler_add; first by apply:ler_norm_add. *)
(* apply: le_lt_trans. *)
(* by apply: ler_add; first by apply ler_add; first by apply: ler_norm_add. *)

(* have -> : `|z|*d= `|z|*dr3%:C+ `|z|*dr3%:C + `|z|*dr3%:C + `|z|*dr3%:C. *)
(*   rewrite -!mulrDl /dr3 -realCM -eq_drd mulrCA [RHS]mulrC. *)
(*   apply/(@mulIf _ d^-1); first by apply:invr_neq0; apply: lt0r_neq0. *)
(*   rewrite -!mulrA !mulfV ?lt0r_neq0 // !mulr1 complexV //; admit. (*argh*) *)
(* apply: ltr_le_add; last by  rewrite realCM lecR ltW. *)
(* apply: ltr_add; last by  rewrite realCM ltcR. *)
(* apply: ltr_add. Fail apply: ltr_add. *)
(* Admitted. *)


(* Theorem CauchyRiemann (f : C^o -> C^o) c : (holomorphic f c) <-> *)
(*  (forall v : C^o, Rderivable_fromcomplex' f c v)/\ (CauchyRiemanEq' f c). *)
(* Proof. *)
(* Admitted. *)

(* End CR_holo. *)


(* Section holo_within. *)
(*  Variable R : rcfType. *)

(* Local Notation sqrtr := Num.sqrt. *)
(* Local Notation C := R[i]. *)
(* Local Notation Re := (@complex.Re R). *)
(* Local Notation Im := (@complex.Im R). *)

(* (* First part of CR with the within defintions *) *)

(* Lemma is_cvg_within (T U : topologicalType) (h : T -> U) (F: set (set T)) (D: set T): *)
(*   (Filter F) -> cvg (h @ F) -> cvg (h @ within D F). *)
(* Proof. *)
(*   by move=> FF /cvg_ex [l H]; apply/cvg_ex; exists l; apply: cvg_within_filter. *)
(* Qed. *)




(* Definition Real_line (c:C^o) := (Im c = 0). *)

(* Definition CauchyRiemanEq (f : C^o -> C^o) z := *)
(*   'i * lim ( (fun h : C^o => h^-1 *: ((f \o shift z) (h) - f z)) @ *)
(*                                        (within Real_line (nbhs' (0)))) = *)
(*   lim ((fun h : C^o => h^-1 *: ((f \o shift z) (h * 'i) - f z)) @ *)
(*                                        (within Real_line (nbhs' (0)))) . *)

(* Definition Rderivable_fromcomplex (f : C^o -> C^o) (c v: C^o) := *)
(*   cvg ((fun (h : C^o) => h^-1 * ((f \o shift c) (h *:v) - f c)) @ *)
(*                          (within Real_line (nbhs' (0:C^o)))). *)


(* Lemma holo_derivable (f : (C)^o -> (C)^o) c : *)
(*   holomorphic f c -> (forall v : C^o, Rderivable_fromcomplex f c v). *)
(* Proof. *)
(* move=> /cvg_ex. rewrite /type_of_filter /=. *)
(* move => [l H]; rewrite /Rderivable_fromcomplex => v /=. *)
(* set quotR := (X in (X @ _)). *)
(* pose locR0 := within Real_line (nbhs' 0). *)
(* simpl in (type of quotR). *)
(* pose mulv (h : C) := (h * v). *)
(* pose quotC (h : C^o) : C^o := h^-1 *: ((f \o shift c) h - f c). *)
(* case: (v =P 0) =>  [eqv0|/eqP vneq0]. *)
(*   apply: cvgP. *)
(*   have eqnear0 : {near locR0, 0 =1 quotR}. *)
(*     by  exists 1=> // h _ _ ; rewrite /quotR /shift eqv0 /= scaler0 add0r addrN mulr0. *)
(*   apply: cvg_trans; first by exact (near_eq_cvg eqnear0). *)
(*   by apply: (cvg_cst (0 : C^o)). *)
(* apply: (cvgP (v *: l)). *)
(* have eqnear0 : {near (locR0), (v \*: quotC) \o mulv =1 quotR}. *)
(*   exists 1 => // h _ neq0h //=; rewrite /quotC /quotR /mulv invrM /= ?unitfE //=. *)
(*   (*hiatus invrM and scale_inv *) *)
(*   rewrite scalerAl scalerCA  mulrA -(mulrC v) mulrA // divff ?div1r //=. *)
(* have subsetfilters : quotR @ locR0 `=>` (v *: quotC) \o mulv @ locR0. *)
(* by exact: (near_eq_cvg eqnear0). *)
(* apply: cvg_trans subsetfilters _. *)
(* suff: v \*: quotC \o mulv @ locR0 `=>` nbhs (v *: l) by move/cvg_trans; apply. *)
(* apply: (@cvg_comp _ _ _ _ _ _ (nbhs' (0:C^o))). *)
(*   (*mulv @ locR0 `=>` locally' 0*) (* should be simpler *) *)
(* move => //= A [r leq0r ballrA];  exists (`|r| / `|v|). *)
(* by rewrite mulr_gt0 // ?normr_gt0 ?gt_eqF //= ?invr_gt0 ?normr_gt0. *)
(* move=> b ; rewrite /ball_ sub0r normrN => ballrb neqb0 Rb. *)
(* have ballCrb : (@ball_ _ _ (fun x => `|x|) 0 r (mulv b)). *)
(*   rewrite /ball_ sub0r normrN /mulv normrM. *)
(*   rewrite ltr_pdivl_mulr in ballrb; last by rewrite normr_gt0. *)
(*   by rewrite -(ger0_norm (ltW leq0r)) (le_lt_trans _ ballrb) // rmorphM /=. *)
(* by apply: (ballrA (mulv b) ballCrb); apply mulf_neq0. *)
(* by apply: cvgZr. *)
(* Qed. *)

(* Lemma properlocR0 : ProperFilter (within Real_line (nbhs' 0)). *)
(* Proof. *)
(* apply: Build_ProperFilter. *)
(* move => P [[r1 r2] ler] /= b. *)
(* move: ler; rewrite ltcE /= => /andP [r20 r10]. *)
(* exists (r1 / 2)%:C. *)
(* have : (ball_ [eta normr] 0 (r1 +i* r2) ) ((r1 / 2)%:C). *)
(*   rewrite /ball_ sub0r normrN ltcE /=; apply/andP; split; simpl; first by []. *)
(*   rewrite expr0n /= addr0 sqrtr_sqr /= gtr0_norm //. *)
(*   rewrite gtr_pmulr ?invf_lt1 ?ltr1n //. *)
(*   by apply: mulr_gt0. *)
(* move=> /b h. *)
(* have r1n0: r1 != 0 by apply: lt0r_neq0. *)
(* have: (r1 / 2)%:C != 0. *)
(*   rewrite (neqCr0 (r1/2)); apply mulf_neq0; first by []. *)
(*   by apply:invr_neq0. *)
(* by move => /h {h} {r10}; rewrite /Real_line /= => h; apply: (h _). *)
(* Qed. *)



(* Lemma holo_CauchyRieman (f : C^o -> C^o) c: holomorphic f c -> CauchyRiemanEq f c. *)
(* Proof. *)
(* move=> /cvg_ex ; rewrite /type_of_filter /= /CauchyRiemanEq. *)
(* pose quotC := fun h => h^-1 *: ((f \o shift c) (h) - f c). *)
(* pose quotR := fun h => h^-1 *: ((f \o shift c) (h * 'i) - f c). *)
(* pose locR0 := within Real_line (nbhs' 0). *)
(* have -> :  within Real_line (nbhs' 0) = locR0  by []. *)
(* have -> :  (fun h  => h^-1 *: ((f \o shift c) (h * 'i) - f c)) = quotR by []. *)
(* have -> :  (fun h  => h^-1 *: ((f \o shift c) (h) - f c)) = quotC by []. *)
(* move => [l H]. *)
(* have HR0: cvg (quotC @ locR0) by apply: is_cvg_within ;  apply/cvg_ex; exists l. *)
(* have lem : quotC \o  *%R^~ 'i%R @ locR0 --> l. *)
(*   apply: cvg_comp. *)
(*   2:  exact H. *)
(*   move => A /=; simpl in (type of A). *)
(*   move => [r ler] ball; simpl in (type of ball). *)
(*   exists r ; first by []. *)
(*   move => a /= ; rewrite sub0r normrN => Ba aneq0  Ra. *)
(*   have: a * 'i != 0 by apply: mulf_neq0; last by rewrite neq0Ci. *)
(*   have: ball_ [eta normr] 0 r (a * 'i). *)
(*     simpl; rewrite sub0r normrN normrM /=. *)
(*     have ->: `|'i| = 1 by move => T;  simpc; rewrite expr0n expr1n /= add0r sqrtr1. *)
(*     by rewrite mulr1. *)
(*   by move => /ball. have HRcomp: cvg (quotC \o *%R^~ 'i%R @ locR0). *)
(*   by apply/cvg_ex;  simpl; exists l. *)
(* have ->: lim (quotR @ locR0) = 'i *: lim (quotC \o ( fun h => h *'i) @ locR0). *)
(*   have: 'i \*:quotC \o ( fun h => h *'i) =1 quotR. *)
(*   move => h /= ;rewrite /quotC /quotR /=. *)
(*   rewrite invcM scalerA mulrC -mulrA mulVf. *)
(*     by rewrite mulr1. *)
(*     by rewrite neq0Ci. *)
(* by move => /funext <-; rewrite (limin_scaler properlocR0 'i HRcomp). *)
(* rewrite scalecM. *)
(* suff: lim (quotC @ locR0) = lim (quotC \o  *%R^~ 'i%R @ locR0) by move => -> . *)
(* have -> : lim (quotC @ locR0) = l. *)
(* apply/cvg_lim; first by apply: norm_hausdorff. *)
(*   by apply:fmap_proper_filter; exact: properlocR0. *)
(*   by apply: cvg_within_filter. *)
(* have -> :  lim (quotC \o  *%R^~ 'i%R @ locR0) = l. *)
(*   apply/cvg_lim; first by apply: norm_hausdorff. *)
(*   by apply:fmap_proper_filter; exact: properlocR0. *)
(*   by []. *)
(* by []. *)
(* Qed. *)

(* End holo_within. *)
