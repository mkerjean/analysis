(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)      
From HB Require Import structures.  
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum vector.
From mathcomp Require Import interval_inference.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import convex set_interval reals initial_topology topology num_normedtype.
From mathcomp Require Import pseudometric_normed_Zmodule.

(**md**************************************************************************)
(* # Topological vector spaces                                                *)
(*                                                                            *)
(* This file introduces locally convex topological vector spaces.             *)
(* ```                                                                        *)
(*              NbhsNmodule == HB class, join of Nbhs and Nmodule             *)
(*              NbhsZmodule == HB class, join of Nbhs and Zmodule             *)
(*            NbhsLmodule K == HB class, join of Nbhs and Lmodule over K      *)
(*                             K is a numDomainType.                          *)
(*    PreTopologicalNmodule == HB class, join of Topological and Nmodule      *)
(*       TopologicalNmodule == HB class, PreTopologicalNmodule with a         *)
(*                             continuous addition                            *)
(*    PreTopologicalZmodule == HB class, join of Topological and Zmodule      *)
(*      topologicalZmodType == topological abelian group                      *)
(*       TopologicalZmodule == HB class, join of TopologicalNmodule and       *)
(*                             Zmodule with a continuous opposite operator    *)
(* preTopologicalLmodType K == topological space and Lmodule over K           *)
(*                             K is a numDomainType                           *)
(*                             The HB class is PreTopologicalLmodule.         *)
(*    topologicalLmodType K == topologicalNmodule and Lmodule over K with a   *)
(*                             continuous scaling operation                   *)
(*                             The HB class is TopologicalLmodule.            *)
(*        PreUniformNmodule == HB class, join of Uniform and Nmodule          *)
(*           UniformNmodule == HB class, join of Uniform and Nmodule with a   *)
(*                             uniformly continuous addition                  *)
(*        PreUniformZmodule == HB class, join of Uniform and Zmodule          *)
(*           UniformZmodule == HB class, join of UniformNmodule and Zmodule   *)
(*                             with uniformly continuous opposite operator    *)
(*      PreUniformLmodule K == HB class, join of Uniform and Lmodule over K   *)
(*                             K is a numDomainType.                          *)
(*         UniformLmodule K == HB class, join of UniformNmodule and Lmodule   *)
(*                             with a uniformly continuous scaling operation  *)
(*                             K is a numFieldType.                           *)
(*         convexTvsType R  == interface type for a locally convex            *)
(*                             tvs on a numDomain R                           *)
(*                             A convex tvs is constructed over a uniform     *)
(*                             space.                                         *)
(*                             The HB class is ConvexTvs.                     *)
(*   subConvexTvsType R V S == join of subTopologicalType, convexTvsType,     *)
(*                             and subLmoduleType                             *)
(*                             The HB class is SubConvexTvs.                  *)
(*                             Instance: in particular, it is shown that a    *)
(*                             sub-Lmodule is a sub-convex TVS.               *)
(* PreTopologicalLmod_isConvexTvs == factory allowing the construction of a   *)
(*                             convex tvs from an Lmodule which is also a     *)
(*                             topological space                              *)
(* {linear_continuous E -> F} == the type of all linear and continuous        *)
(*                             functions between E and F, where E is a        *)
(*                             NbhsLmodule.type and F a NbhsZmodule.type over *)
(*                             a numDomainType R                              *)
(*                             The HB class is called LinearContinuous.       *)
(*                             The notation {linear_continuous E -> F | s}    *)
(*                             also exists.                                   *)
(*              lcfun E F s == membership predicate for linear continuous     *)
(*                             functions of type E -> F with scalar operator  *)
(*                             s : K -> F -> F                                *)
(*                             E and F have type convexTvsType K.             *)
(*                             This is used in particular to attach a type of *)
(*                             lmodType to {linear_continuous E -> F | s}.    *)
(*             lcfun_spec f == specification for membership of the linear     *)
(*                             continuous function f                          *)
(* ```                                                                        *)
(* HB instances:                                                              *)
(* - The type R^o (R : numFieldType) is endowed with the structure of         *)
(*   ConvexTvs.                                                               *)
(* - The product of two Tvs is endowed with the structure of ConvexTvs.       *)
(* - {linear_continuous E-> F} is endowed with a lmodType structure when E    *)
(*   and F are convexTvs.                                                     *)
(******************************************************************************)


Reserved Notation "'{' 'linear_continuous' U '->' V '|' s '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'linear_continuous'  U  ->  V  |  s }").
Reserved Notation "'{' 'linear_continuous' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
    format "{ 'linear_continuous'  U  ->  V }").

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.



Module DDist.
Section dDist.
Context (R: numDomainType) (n : nat).

Record d :=  {
   t :> n.-tuple R ;
   le1 : \sum_(a <- t) `|a| <= 1}.

End dDist.
End DDist.
Coercion DDist.t : DDist.d >-> tuple_of. 


Reserved Notation "{ 'ddist' n }" (at level 0, format "{ 'ddist'  n }").
Reserved Notation "R '.-ddist' n" (at level 2, format "R '.-ddist'  n").

Notation "R '.-ddist' n" := (DDist.d R n%type).
Notation "{ 'ddist' n }" := (_.-ddist n).


Section absolutely_convex.
Context (K : numDomainType) (V : lmodType K).
          
Definition balanced_set (A : set V) := (forall r, `|r| <= 1 ->  (fun x => r *: x) @`A `<=` A).

Definition absolutely_convex_set  (A : set V) := convex_set A /\ balanced_set A.

Definition absorbing_set (A : set V) := forall x : V, exists a, exists2 r, (a \in A) & (x = r *:a).

Definition pabsorbing_set (A : set V) := forall x : V, exists2 r, ( 0< r) & r*: x \in A.

Definition absolutely_convex_hull  (A : set V) := smallest absolutely_convex_set A.



(* TODO : move to convex.v *)
Lemma setI_convex : setI_closed (@convex_set K V).
Proof.
move=> A B cA cB x y r /[!inE] -[xA xB] [yA yB]; split; apply/set_mem. 
by apply/cA; apply/mem_set.
by apply/cB; apply/mem_set.
Qed.

Lemma bigcap_convex : bigcap_closed (@convex_set K V).
Proof.
move=> H Hconv x y r /[!inE] /= Hx Hy A /[dup] HA /Hconv /(_ _ _ _ _ _ )/set_mem; apply. 
- by apply: mem_set; apply: Hx.
- by apply: mem_set; apply: Hy. 
Qed.

Lemma setI_balanced : setI_closed balanced_set.
Proof.
move=> A B bA bB x r /=; rewrite subsetI; split => z /= [t [At Bt] <-]. 
- by apply: (bA _ r)  => //; exists t. 
- by apply: (bB _ r)  => //; exists t. 
Qed.

Lemma bigcap_balanced : bigcap_closed balanced_set.
Proof.
move=> H Hconv /= r r1; apply: sub_bigcap => A HA x /= [t Ht <-].
apply: (Hconv A HA r r1) => //.
by exists t; first by apply: Ht.  
Qed.

Lemma absolutely_convex_hull_set  (A : set V) : absolutely_convex_set (absolutely_convex_hull A).
Proof.
apply: bigcap_closed_smallest => H Habs.
split. 
- by apply: bigcap_convex; apply: (subset_trans Habs); apply: subIsetl. 
- by apply: bigcap_balanced; apply: (subset_trans Habs); apply: subIsetr.  
Qed.

Lemma absolutely_convex_hullE  (A : set V):
  absolutely_convex_hull A = [set a | exists n  (t: {ddist n}) (l : n.-tuple V),
                             [set` l] `<=` A  /\  a = \sum_(i < n) t`_i *: l`_i].
Abort.
  
Lemma absolutely_convex_hull_subset  (A : set V): A `<=` absolutely_convex_hull A.
Proof.
by exact: sub_gen_smallest.
Qed.

Lemma absolutely_convex0 (B : set V) :  B !=set0 -> absolutely_convex_set B  ->  B 0. 
Proof. 
move => [] x Bx []  _ /(_ 0); rewrite normr0 ler01 // => /(_ isT) /(_ 0); apply. 
by exists x; rewrite //= scale0r.
Qed.

End absolutely_convex.


(* HB.structure Definition PointedNmodule := {M of Pointed M & GRing.Nmodule M}. *)
(* HB.structure Definition PointedZmodule := {M of Pointed M & GRing.Zmodule M}. *)
(* HB.structure Definition PointedLmodule (K : numDomainType) := *)
(*   {M of Pointed M & GRing.Lmodule K M}. *)

(* HB.structure Definition FilteredNmodule := {M of Filtered M M & GRing.Nmodule M}. *)
(* HB.structure Definition FilteredZmodule := {M of Filtered M M & GRing.Zmodule M}. *)
(* HB.structure Definition FilteredLmodule (K : numDomainType) := *)
(*   {M of Filtered M M & GRing.Lmodule K M}. *)
HB.structure Definition NbhsLmodule (K : numDomainType) :=
  {M of Nbhs M & GRing.Lmodule K M}.

HB.mixin Record PreTopologicalNmodule_isTopologicalNmodule M
    & PreTopologicalNmodule M := {
  add_continuous : continuous (fun x : M * M => x.1 + x.2) ;
}.

HB.structure Definition TopologicalNmodule :=
  {M of PreTopologicalNmodule M & PreTopologicalNmodule_isTopologicalNmodule M}.

Section TopologicalNmodule_theory.
Variable (E : topologicalType) (F : TopologicalNmodule.type) (U : set_system E).

(** TODO:
  We have observed one thing:
  `pseudometric_normedZmodType` is morally a `topologicalNmodule`
  but `topologicalNmodule` is defined later in `tvs.v` (which imports `pseudometric_normed_zmodule.v`).
  We think that it should be defined at the beginning of `pseudometric_normed_zmodule.v` and that
  `pseudometric_normedZmodType` should be defined using `topologicalNmodule`.
  We have realized this because of the lemmas such as `cvgD/fun_cvgD` that we needed to duplicate. *)
Lemma fun_cvgD {FF : Filter U} (f g : E -> F) a b :
  f @ U --> a -> g @ U --> b -> (f \+ g) @ U --> a + b.
Proof.
move=> fa ga.
by apply: continuous2_cvg; [exact: (add_continuous (a, b))|by []..].
Qed.

Lemma cvg_sum (I : Type) (r : seq I) (P : pred I)
    (Ff : I -> E -> F) (Fa : I -> F) :
  Filter U -> (forall i, P i -> Ff i x @[x --> U] --> Fa i) ->
  \sum_(i <- r | P i) Ff i x @[x --> U] --> \sum_(i <- r| P i) Fa i.
Proof. by move=> FF Ffa; apply: cvg_big => //; apply: add_continuous. Qed.

Lemma sum_continuous (I : Type) (r : seq I) (P : pred I) (f : I -> E -> F) :
  (forall i : I, P i -> continuous (f i)) ->
  continuous (fun x1 : E => \sum_(i <- r | P i) f i x1).
Proof. by move=> FC0; apply: continuous_big => //; apply: add_continuous. Qed.

End TopologicalNmodule_theory.

HB.mixin Record TopologicalNmodule_isTopologicalZmodule M
    & Topological M & GRing.Zmodule M := {
  opp_continuous : continuous (-%R : M -> M) ;
}.

#[short(type="topologicalZmodType")]
HB.structure Definition TopologicalZmodule :=
  {M of TopologicalNmodule M & GRing.Zmodule M
        & TopologicalNmodule_isTopologicalZmodule M}.

Section TopologicalZmoduleTheory.
Variables (M : topologicalZmodType).

Lemma sub_continuous : continuous (fun x : M * M => x.1 - x.2).
Proof.
move=> x; apply: (@continuous_comp _ _ _ (fun x => (x.1, - x.2))
  (fun x : M * M => x.1 + x.2)); last exact: add_continuous.
apply: cvg_pair; first exact: cvg_fst.
by apply: continuous_comp; [exact: cvg_snd|exact: opp_continuous].
Qed.

Lemma fun_cvgN (F : topologicalZmodType) (U : set_system M) {FF : Filter U}
    (f : M -> F) a :
  f @ U --> a -> \- f @ U --> - a.
Proof. by move=> ?; apply: continuous_cvg => //; exact: opp_continuous. Qed.

End TopologicalZmoduleTheory.

HB.factory Record PreTopologicalNmodule_isTopologicalZmodule M
    & Topological M & GRing.Zmodule M := {
  sub_continuous : continuous (fun x : M * M => x.1 - x.2) ;
}.

HB.builders Context M & PreTopologicalNmodule_isTopologicalZmodule M.

Let opp_continuous : continuous (-%R : M -> M).
Proof.
move=> x; rewrite /continuous_at.
rewrite -(@eq_cvg _ _ _ (fun x => 0 - x)); first by move=> y; exact: add0r.
rewrite -[- x]add0r.
apply: (@continuous_comp _ _ _ (fun x => (0, x)) (fun x : M * M => x.1 - x.2)).
  by apply: cvg_pair => /=; [exact: cvg_cst|exact: cvg_id].
exact: sub_continuous.
Qed.

Let add_continuous : continuous (fun x : M * M => x.1 + x.2).
Proof.
move=> x; rewrite /continuous_at.
rewrite -(@eq_cvg _ _ _ (fun x => x.1 - (- x.2))).
  by move=> y; rewrite opprK.
rewrite -[in x.1 + _](opprK x.2).
apply: (@continuous_comp _ _ _ (fun x => (x.1, - x.2)) (fun x => x.1 - x.2)).
  apply: cvg_pair; first exact: cvg_fst.
  by apply: continuous_comp; [exact: cvg_snd|exact: opp_continuous].
exact: sub_continuous.
Qed.

HB.instance Definition _ :=
  PreTopologicalNmodule_isTopologicalNmodule.Build M add_continuous.

HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalZmodule.Build M opp_continuous.

HB.end.

#[short(type="preTopologicalLmodType")]
HB.structure Definition PreTopologicalLmodule (K : numDomainType) :=
  {M of Topological M & GRing.Lmodule K M}.

HB.mixin Record TopologicalZmodule_isTopologicalLmodule (R : numDomainType) M
    & Topological M & GRing.Lmodule R M := {
  scale_continuous : continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

#[short(type="topologicalLmodType")]
HB.structure Definition TopologicalLmodule (K : numDomainType) :=
  {M of TopologicalZmodule M & GRing.Lmodule K M
        & TopologicalZmodule_isTopologicalLmodule K M}.

Section TopologicalLmodule_theory.
Variables (R : numFieldType) (E : topologicalType) (F : topologicalLmodType R).

Lemma fun_cvgZ (U : set_system E) {FF : Filter U} (l : E -> R) (f : E -> F)
    (r : R) a :
  l @ U --> r -> f @ U --> a ->
  l x *: f x @[x --> U] --> r *: a.
Proof.
by move=> *; apply: continuous2_cvg => //; exact: (scale_continuous (_, _)).
Qed.

Lemma fun_cvgZr (U : set_system E) {FF : Filter U} k (f : E -> F) a :
  f @ U --> a -> k \*: f @ U --> k *: a.
Proof. by apply: fun_cvgZ => //; exact: cvg_cst. Qed.

End TopologicalLmodule_theory.

HB.factory Record TopologicalNmodule_isTopologicalLmodule (R : numDomainType) M
    & Topological M & GRing.Lmodule R M := {
  scale_continuous : continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

HB.builders Context R M & TopologicalNmodule_isTopologicalLmodule R M.

Let opp_continuous : continuous (-%R : M -> M).
Proof.
move=> x; rewrite /continuous_at.
rewrite -(@eq_cvg _ _ _ (fun x => -1 *: x)); first by move=> y; rewrite scaleN1r.
rewrite -[- x]scaleN1r.
apply: (@continuous_comp M (R^o * M)%type M (fun x => (-1, x))
  (fun x => x.1 *: x.2)); last exact: scale_continuous.
by apply: (@cvg_pair _ _ _ _ (nbhs (-1 : R^o))); [exact: cvg_cst|exact: cvg_id].
Qed.

#[warning="-HB.no-new-instance"]
HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalZmodule.Build M opp_continuous.
HB.instance Definition _ :=
  TopologicalZmodule_isTopologicalLmodule.Build R M scale_continuous.

HB.end.

HB.mixin Record PreUniformNmodule_isUniformNmodule M & PreUniformNmodule M := {
  add_unif_continuous : unif_continuous (fun x : M * M => x.1 + x.2)
}.

HB.structure Definition UniformNmodule :=
  {M of PreUniformNmodule M & PreUniformNmodule_isUniformNmodule M}.

HB.mixin Record UniformNmodule_isUniformZmodule M
    & Uniform M & GRing.Zmodule M := {
  opp_unif_continuous : unif_continuous (-%R : M -> M)
}.

HB.structure Definition UniformZmodule :=
  {M of UniformNmodule M & GRing.Zmodule M & UniformNmodule_isUniformZmodule M}.

HB.factory Record PreUniformNmodule_isUniformZmodule M
    & Uniform M & GRing.Zmodule M := {
  sub_unif_continuous : unif_continuous (fun x : M * M => x.1 - x.2)
}.

HB.builders Context M & PreUniformNmodule_isUniformZmodule M.

Lemma opp_unif_continuous : unif_continuous (-%R : M -> M).
Proof.
have unif : unif_continuous (fun x => (0, x) : M * M).
  move=> /= U [[]] /= U1 U2 [] U1e U2e /subsetP U12.
  apply: filterS U2e => x xU2/=.
  have /U12 : ((0, 0), x) \in U1 `*` U2.
    by rewrite in_setX/= (mem_set xU2) andbT inE; exact: entourage_refl.
  by rewrite inE/= => -[[[a1 a2] [b1 b2]]]/= /[swap]-[] -> -> <-.
move=> /= U /sub_unif_continuous /unif /=.
rewrite -comp_preimage/= /comp/= /nbhs/=.
by congr entourage => /=; rewrite eqEsubset; split=> x /=; rewrite !sub0r.
Qed.

Lemma add_unif_continuous : unif_continuous (fun x : M * M => x.1 + x.2).
Proof.
have unif: unif_continuous (fun x => (x.1, -x.2) : M * M).
  move=> /= U [[]]/= U1 U2 [] U1e /opp_unif_continuous.
  rewrite /nbhs/= => U2e /subsetP U12.
  apply: (@filterS _ _ entourage_filter
      ((fun xy => (xy.1.1, xy.2.1, (-xy.1.2, -xy.2.2))) @^-1` (U1 `*` U2))).
    move=> /= [] [] a1 a2 [] b1 b2/= [] ab1 ab2.
    have /U12 : (a1, b1, (-a2, -b2)) \in U1 `*` U2 by rewrite !inE.
    by rewrite inE/= => [] [] [] [] c1 c2 [] d1 d2/= cd [] <- <- <- <-.
  exists (U1, ((fun xy : M * M => (- xy.1, - xy.2)) @^-1` U2)); first by split.
  by move=> /= [] [] a1 a2 [] b1 b2/= [] aU bU; exists (a1, b1, (a2, b2)).
move=> /= U /sub_unif_continuous/unif; rewrite /nbhs/=.
rewrite -comp_preimage/=/comp/=.
by congr entourage; rewrite eqEsubset; split=> x /=; rewrite !opprK.
Qed.

HB.instance Definition _ :=
  PreUniformNmodule_isUniformNmodule.Build M add_unif_continuous.
HB.instance Definition _ :=
  UniformNmodule_isUniformZmodule.Build M opp_unif_continuous.

HB.end.

Section UniformZmoduleTheory.
Variables (M : UniformZmodule.type).

Lemma sub_unif_continuous : unif_continuous (fun x : M * M => x.1 - x.2).
Proof.
suff unif: unif_continuous (fun x => (x.1, - x.2) : M * M).
  by move=> /= U /add_unif_continuous/unif; rewrite /nbhs/= -comp_preimage.
move=> /= U [[]]/= U1 U2 [] U1e /opp_unif_continuous.
rewrite /nbhs/= => U2e /subsetP U12.
apply: (@filterS _ _ entourage_filter
    ((fun xy => (xy.1.1, xy.2.1, (- xy.1.2, - xy.2.2))) @^-1` (U1 `*` U2))).
  move=> /= [] [] a1 a2 [] b1 b2/= [] ab1 ab2.
  have /U12 : (a1, b1, (-a2, -b2)) \in U1 `*` U2 by rewrite !inE.
  by rewrite inE/= => [] [] [] [] c1 c2 [] d1 d2/= cd [] <- <- <- <-.
exists (U1, ((fun xy : M * M => (- xy.1, - xy.2)) @^-1` U2)); first by split.
by move=> /= [] [] a1 a2 [] b1 b2/= [] aU bU; exists (a1, b1, (a2, b2)).
Qed.

End UniformZmoduleTheory.

HB.structure Definition PreUniformLmodule (K : numDomainType) :=
  {M of Uniform M & GRing.Lmodule K M}.

HB.mixin Record PreUniformLmodule_isUniformLmodule (R : numFieldType) M
    & PreUniformLmodule R M := {
  scale_unif_continuous : unif_continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

HB.structure Definition UniformLmodule (R : numFieldType) :=
  {M of UniformZmodule M & GRing.Lmodule R M
        & PreUniformLmodule_isUniformLmodule R M}.

HB.factory Record UniformNmodule_isUniformLmodule (R : numFieldType) M
    & PreUniformLmodule R M := {
  scale_unif_continuous : unif_continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

HB.builders Context R M & UniformNmodule_isUniformLmodule R M.

Lemma opp_unif_continuous : unif_continuous (-%R : M -> M).
Proof.
have unif: unif_continuous (fun x => (-1, x) : R^o * M).
  move=> /= U [[]] /= U1 U2 [] U1e U2e /subsetP U12.
  rewrite /nbhs/=.
  apply: filterS U2e => x xU2/=.
  have /U12 : ((-1, -1), x) \in U1 `*` U2.
    rewrite in_setX/= (mem_set xU2) andbT.
    by apply/mem_set; exact: entourage_refl.
  by rewrite inE/= => [[[]]] [] a1 a2 [] b1 b2/= abU [] {2}<- <- <-/=.
move=> /= U /scale_unif_continuous/unif/=.
rewrite /nbhs/=.
rewrite -comp_preimage/=/comp/=.
by congr entourage; rewrite eqEsubset; split=> x /=; rewrite !scaleN1r.
Qed.

#[warning="-HB.no-new-instance"]
HB.instance Definition _ :=
  UniformNmodule_isUniformZmodule.Build M opp_unif_continuous.
HB.instance Definition _ :=
  PreUniformLmodule_isUniformLmodule.Build R M scale_unif_continuous.

HB.end.

HB.mixin Record Uniform_isConvexTvs (R : numDomainType) E
    & Uniform E & GRing.Lmodule R E := {
  locally_convex : exists2 B : set_system E,
    (forall b, b \in B -> absolutely_convex_set b) & (nbhs_basis 0)  B
}.
(* absolutely_convex instead of convex *) 
(*filter_from [set U | B U /\ U 0] id --> 0. instead of B*)

#[short(type="convexTvsType")]
HB.structure Definition ConvexTvs (R : numDomainType) :=
  {E of Uniform_isConvexTvs R E & Uniform E & TopologicalLmodule R E}.

#[short(type="subConvexTvsType")]
HB.structure Definition SubConvexTvs (R : numDomainType) (V : convexTvsType R)
    (S : pred V) :=
  { U of SubTopological V S U & ConvexTvs R U & @GRing.SubLmodule R V S U }.

Section SubLmodule_isSubConvexTvs.
Context (R : numFieldType) (V : convexTvsType R) (S : pred V) (U : subLmodType S).

Local Notation sub_init_topo := (sub_initial_topology U).
HB.instance Definition _ := Uniform.on sub_init_topo.
HB.instance Definition _ := GRing.Lmodule.on sub_init_topo.

Let add_sub: continuous (fun x : sub_init_topo * sub_init_topo => x.1 + x.2).
Proof.
apply: continuous_comp_initial => -[/= x y].
pose h := fun xy : U * U => (\val xy.1, \val xy.2).
pose g := fun xy : V * V => xy.1 + xy.2.
rewrite (_ : _ \o _ = g \o h).
  by apply/funext => i /=; rewrite GRing.valD.
apply: continuous_comp; last exact: add_continuous.
apply: cvg_pair => //=.
- apply: (cvg_comp _ _ cvg_fst).
  exact: (continuous_valE (x : sub_init_topo)).
- apply: (cvg_comp _ _ cvg_snd).
  exact: (continuous_valE (y : sub_init_topo)).
Qed.

HB.instance Definition _ :=
  @PreTopologicalNmodule_isTopologicalNmodule.Build sub_init_topo add_sub.

Let opp_sub : continuous (-%R : sub_init_topo -> sub_init_topo).
Proof.
apply: continuous_comp_initial => x.
rewrite (_ : _ \o _ = -%R \o \val).
  by apply/funext=> i /=; rewrite GRing.valN.
apply: continuous_comp; first exact: continuous_valE.
exact: opp_continuous.
Qed.

HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalZmodule.Build sub_init_topo opp_sub.

Let scale_sub : continuous (fun z : R^o * sub_init_topo => z.1 *: z.2).
Proof.
apply: continuous_comp_initial => - [] /= x /= y.
pose h := fun xy : R * U => (xy.1, \val xy.2).
pose g := fun xy : R * V => xy.1 *: xy.2.
rewrite (_ : _ \o _ = g \o h); first by apply/funext=> i /=; rewrite GRing.valZ.
apply: continuous_comp; last exact: scale_continuous.
move=> /= A [/= [/= B C]] [[r/= r0 xrB]].
move/(continuous_valE (y : sub_init_topo)) => [/= C' [woC' C'y C'C] BCA].
apply: filterS; first exact: BCA.
exists (ball x r, C') => /=.
  by split; [exact: nbhsx_ballx|exists C'; split].
by move=> su/= [xru C'u]; split; [exact: xrB|exact: C'C].
Qed.

HB.instance Definition _ :=
  TopologicalZmodule_isTopologicalLmodule.Build R sub_init_topo scale_sub.

Local Open Scope convex_scope.

Let locally_convex_sub : exists2 B : set_system sub_init_topo,
  (forall b, b \in B -> convex_set b) & basis B.
Proof.
have [B convexB [openB/= genB]] := @locally_convex R V.
exists [set a | exists2 b, B b & \val @^-1` b = a].
  move=> a /[!inE]/= -[b Bb ba] r s l ra sa.
  suff : \val (r <|l|> s) \in b by rewrite !inE /= -ba.
  rewrite !GRing.valD !GRing.valZ convexB//; first exact: mem_set.
  - by move: ra; rewrite -ba !inE.
  - by move: sa; rewrite -ba !inE.
split => /=.
  move=> a/= [b Bb <-]; rewrite /open/= /wopen/=; exists b => //.
  exact: openB.
move=> x a [/= b [[/=c openc] cb bx ba]].
rewrite /nbhs/= /filter_from/=.
have : nbhs (val x) c.
 rewrite nbhsE /=; exists c => //; split => //.
 by move: bx; rewrite -cb.
move/genB => [d [Bd dx dc]].
exists (\val @^-1` d); first by split => //; exists d.
by move=> y dy; apply: ba; rewrite -cb; exact: dc.
Qed.

Local Close Scope convex_scope.

HB.instance Definition _ :=
  @Uniform_isConvexTvs.Build R sub_init_topo locally_convex_sub.
HB.instance Definition _ := GRing.SubLmodule.on sub_init_topo.

End SubLmodule_isSubConvexTvs.

Section properties_of_topologicalLmodule.
Context (R : numDomainType) (E : preTopologicalLmodType R) (U : set E).

Lemma nbhsN_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2)) (x : E) :
  nbhs x U -> nbhs (-x) (-%R @` U).
Proof.
move=> Ux; move: (f (-1, -x) U); rewrite /= scaleN1r opprK => /(_ Ux) [] /=.
move=> [B] B12 [B1 B2] BU; near=> y; exists (- y); rewrite ?opprK// -scaleN1r//.
apply: (BU (-1, y)); split => /=; last by near: y.
by move: B1 => [] ? ?; apply => /=; rewrite subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma nbhs0N_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2)) :
  nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. by move => Ux; rewrite -oppr0; exact: nbhsN_subproof. Qed.

Lemma nbhsT_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (x : E) :
  nbhs 0 U -> nbhs x (+%R x @` U).
Proof.
move => U0; have /= := f (x, -x) U; rewrite subrr => /(_ U0).
move=> [B] [B1 B2] BU; near=> x0.
exists (x0 - x); last by rewrite addrC subrK.
by apply: (BU (x0, -x)); split; [near: x0; rewrite nearE|exact: nbhs_singleton].
Unshelve. all: by end_near. Qed.

Lemma nbhsB_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (z x : E) :
  nbhs z U -> nbhs (x + z) (+%R x @` U).
Proof.
move=> U0; have /= := f (x + z, -x) U; rewrite [x + z]addrC addrK.
move=> /(_ U0)[B] [B1 B2] BU; near=> x0.
exists (x0 - x); last by rewrite addrC subrK.
by apply: (BU (x0, -x)); split; [near: x0; rewrite nearE|exact: nbhs_singleton].
Unshelve. all: by end_near. Qed.

End properties_of_topologicalLmodule.

HB.factory Record PreTopologicalLmod_isConvexTvs (R : numDomainType) E
    & Topological E & GRing.Lmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
  locally_convex : exists2 B : set_system E,
    (forall b, b \in B -> absolutely_convex_set b) & nbhs_basis 0 B
  }.

HB.builders Context R E & PreTopologicalLmod_isConvexTvs R E.

Definition entourage : set_system (E * E) :=
  fun P => exists (U : set E), nbhs (0 : E) U  /\
                     (forall xy : E * E,  (xy.1 - xy.2) \in U -> xy \in P).

Let nbhs0N (U : set E) : nbhs (0 : E) U -> nbhs (0 : E) (-%R @` U).
Proof. exact/nbhs0N_subproof/scale_continuous. Qed.

Lemma nbhsN (U : set E) (x : E) : nbhs x U -> nbhs (-x) (-%R @` U).
Proof. exact/nbhsN_subproof/scale_continuous. Qed.

Let nbhsT (U : set E) (x : E) : nbhs (0 : E) U -> nbhs x (+%R x @`U).
Proof. exact/nbhsT_subproof/add_continuous. Qed.

Let nbhsB (U : set E) (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof. exact/nbhsB_subproof/add_continuous. Qed.

Lemma entourage_filter : Filter entourage.
Proof.
split; first by exists [set: E]; split; first exact: filter_nbhsT.
  move=> P Q; rewrite /entourage nbhsE /=.
  move=> [U [[B B0] BU Bxy]] [V [[C C0] CV Cxy]].
  exists (U `&` V); split => [|xy].
    by exists (B `&` C); [exact: open_nbhsI|exact: setISS].
  by rewrite !in_setI => /andP[/Bxy-> /Cxy->].
by move=> P Q PQ [U [HU Hxy]]; exists U; split => [|xy /Hxy /[!inE] /PQ].
Qed.

Local Lemma entourage_refl (A : set (E * E)) :
  entourage A -> [set xy | xy.1 = xy.2] `<=` A.
Proof.
move=> [U [U0 Uxy]] xy eq_xy; apply/set_mem/Uxy; rewrite eq_xy subrr.
apply/mem_set; exact: nbhs_singleton.
Qed.

Local Lemma entourage_inv (A : set (E * E)) :
  entourage A -> entourage A^-1%relation.
Proof.
move=> [/= U [U0 Uxy]]; exists (-%R @` U); split; first exact: nbhs0N.
move=> xy /set_mem /=; rewrite -opprB => [[yx] Uyx] /oppr_inj yxE.
by apply/Uxy/mem_set; rewrite /= -yxE.
Qed.

Local Lemma entourage_split_ex (A : set (E * E)) : entourage A ->
  exists2 B : set (E * E), entourage B & (B \; B)%relation `<=` A.
Proof.
move=> [/= U] [U0 Uxy]; rewrite /entourage /=.
have := @add_continuous (0, 0); rewrite /continuous_at/= addr0 => /(_ U U0)[]/=.
move=> [W1 W2] []; rewrite nbhsE/= => [[U1 nU1 UW1] [U2 nU2 UW2]] Wadd.
exists [set w | (W1 `&` W2) (w.1 - w.2)].
  exists (W1 `&` W2); split; last by [].
  exists (U1 `&` U2); first exact: open_nbhsI.
  by move=> t [U1t U2t]; split; [exact: UW1|exact: UW2].
move => xy /= [z [H1 _] [_ H2]]; apply/set_mem/(Uxy xy)/mem_set.
rewrite [_ - _](_ : _ = (xy.1 - z) + (z - xy.2)); first by rewrite addrA subrK.
exact: (Wadd (xy.1 - z,z - xy.2)).
Qed.

Local Lemma nbhsE : nbhs = nbhs_ entourage.
Proof.
have lem : -1 != 0 :> R by rewrite oppr_eq0 oner_eq0.
rewrite /nbhs_ /=; apply/funext => x; rewrite /filter_from/=.
apply/funext => U; apply/propext => /=; rewrite /entourage /=; split.
- pose V : set E := [set v | x - v \in U].
  move=> nU; exists [set xy | xy.1 - xy.2 \in V]; last first.
    by move=> y /xsectionP; rewrite /V /= !inE /= opprB addrC subrK inE.
  exists V; split; last by move=> xy; rewrite !inE /= inE.
  have /= := nbhsB x (nbhsN nU); rewrite subrr /= /V.
  rewrite [X in nbhs _ X -> _](_ : _ = [set v | x - v \in U])//.
  apply/funext => /= v /=; rewrite inE; apply/propext; split.
    by move=> [x0 [x1]] Ux1 <- <-; rewrite opprB addrC subrK.
  move=> Uxy; exists (v - x); last by rewrite addrC subrK.
  by exists (x - v); rewrite ?opprB.
- move=> [A [U0 [nU UA]] H]; near=> z; apply: H; apply/xsectionP/set_mem/UA.
  near: z; rewrite nearE; have := nbhsT x (nbhs0N nU).
  rewrite [X in nbhs _ X -> _](_ : _ = [set v | x - v \in U0])//.
  apply/funext => /= z /=; apply/propext; split.
    by move=> [x0] [x1 Ux1 <-] <-; rewrite opprB addrC subrK inE.
  rewrite inE => Uxz; exists (z - x); last by rewrite addrC subrK.
  by exists (x - z); rewrite ?opprB.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build E
    entourage_filter entourage_refl
    entourage_inv entourage_split_ex
    nbhsE.

(* TO BE DELETED once PR#1974 is merged *)

HB.instance Definition _ := PreTopologicalNmodule_isTopologicalNmodule.Build E add_continuous.

HB.instance Definition _ := TopologicalNmodule_isTopologicalLmodule.Build R E scale_continuous.

HB.instance Definition _ := Uniform_isConvexTvs.Build R E locally_convex.
(* END TO BE DELETED *)

HB.end.


Notation "A `+ B" := [set x + y | x in A & y in B] (at level 54).
Notation "r `*: B" := [set r *: x | x  in B] (at level 54).

Lemma addsubset (E : zmodType) (A B C D: set E):
  A `<=` B -> C `<=` D -> (A `+ C) `<=` (B `+ D).
Proof.
by move=> AB CD z [a /AB Ba [c /CD Dc <-]]; exists a => //; exists c.
Qed.

Lemma addset0 (E : zmodType) (A: set E):
 ([set 0] `+ A) = A.
Proof.
apply/seteqP; split => z /=.
  by move=> [+ -> [y]]; rewrite add0r => + + <-. 
by move=> Az; exists 0 => //; exists z; rewrite ?add0r.
Qed.

Lemma addsetI (E : zmodType) (A B : set E) (x : E) :
[set x] `+ (A `&` B) = ([set x] `+ A) `&` ([set x] `+ B).
Proof.
apply/seteqP; split => z.
   by move => [r Cr] [y [Ay By] <- {z}]; split => /=; exists r => //; exists y => //.
move => /= [[r ->] [y Ay] <- {z}] [x' ->] [y' By'].
move=> /(congr1 (fun h => h - x)).
rewrite addrAC subrr add0r addrAC subrr add0r => yy'.
rewrite yy' in By' *.
by exists x  => //;  exists y' => //; rewrite ?yy'; first by split.
Qed.

Lemma addsubsetA (E : zmodType) p c (D : set E) :
  [set p + c] `+ D `<=` [set p] `+ ([set c] `+ D).
Proof.
move=> x/= [y ->{y}] [z Dz <-{x}].
exists p => //.
exists (c + z) => //.
  exists c => //.
  by exists z.
by rewrite addrA.
Qed.

(* TODO : how to make a mixin isConvexTvssat of the following axioms, as open_at0 has to be redefined each time 
{
open_at0 : set_system E;
mem0_setsystem : forall B, open_at0 B -> B (0 : E);
split_setsystem : forall B, open_at0 B -> exists2 C, open_at0 C & ( C `+ C  `<=` B);
expand_setsystem : forall B r, open_at0 B -> (0 <r ) -> exists2 U, open_at0 U & (r `*: U `<=` B);
convex_setsystem : forall B, open_at0 B -> convex_set B
}.

HB.structure Definition ConvexTvsat (R : numDomainType) := {E of GRing.Lmodule R E & isConvexTvsat R E}.
*)


HB.factory Record Nbhsbasisat0_isConvexTvs (R: numFieldType) E & GRing.Lmodule R E (*& isConvexTvsat R E*) := {
  nbhsbasis_at0 : set_system E ; (*TODO rename to filterbasis_at0*)
  nonempty_nbhsbasisat0 : exists U, nbhsbasis_at0 U;
  nbhsbasis_at0I : forall U V, nbhsbasis_at0 U -> nbhsbasis_at0 V ->
    exists2 W, nbhsbasis_at0 W & W `<=` U `&` V ;
  mem0_nbhsbasisat0 : forall B, nbhsbasis_at0 B -> B 0 ;
  expand_nbhsbasisat0 : forall B r, nbhsbasis_at0 B -> (*0 <= r ->*)
    exists2 U, nbhsbasis_at0 U & r `*: U `<=` B ; (* implies circled *)
  absorbing_nbhsbasisat0 : forall B , nbhsbasis_at0 B -> pabsorbing_set B;
  absconvex_nbhsbasisat0 : forall B, nbhsbasis_at0 B -> absolutely_convex_set B }.

Definition nbhs_frombasis0 (R : numFieldType) (E : zmodType)
    (nbhsbasis_at0 : set_system E) (x : E) :=
  filter_from [set U | exists2 V, nbhsbasis_at0 V & [set x] `+ V = U] id.
(*
Definition nbhs_fromfilter0  (R: numDomainType) (E : zmodType) (nbhsbasis_at0 : set_system E) (x : E) U := 
exists2 V, ((filter_from nbhsbasis_at0 id) V) & ([set x] `+ V `<=` U).
*)

HB.builders Context R E & Nbhsbasisat0_isConvexTvs R E.

Local Definition nbhs_fromfilter0 := @nbhs_frombasis0 R E (nbhsbasis_at0).

Lemma split_nbhsbasisat0 : forall B, nbhsbasis_at0 B ->
    exists2 C, nbhsbasis_at0 C & C `+ C `<=` B.
Proof.
move => B /(@expand_nbhsbasisat0 _ (2)) [U fU UB].
exists U => //.
move => /= x [u] Uu [v] Uv <-.
apply: UB. 
exists (2^-1 *: (u+v)); last by by rewrite scalerA mulfV // scale1r.  
rewrite scalerDr. 
have [convU _] := absconvex_nbhsbasisat0 fU. 
have H : (0 : R) <= 2^-1 by [].
have G : (2^-1 : R) <= 1 by rewrite invf_le1 ?lerDl //.  
pose r := Itv01 H G.
have := (convU u v r).
rewrite !inE => /(_ Uu Uv); rewrite /conv /=.
suff -> :  (2^-1).~ = 2^-1 :> R by []. (* should be a lemma in convex *)
apply: (@mulIf _ 2%:R); rewrite /((_).~) //.
by rewrite mulrBl mulVf // mul1r // addrK.
Qed.

#[local] Lemma  nbhs_filter : forall p : E, ProperFilter (nbhs_fromfilter0 p).
Proof.
rewrite /nbhs_fromfilter0 => p.
apply: filter_from_proper.
  apply: filter_from_filter => /=.
  have [U fU] := nonempty_nbhsbasisat0.
    exists ([set p] `+ U) => //=. 
    by exists U.
  move=> _ _ /= [U0 FU <-] [V0 FV <-].
  have [W FW WUV] := nbhsbasis_at0I FU FV.
  exists ([set p] `+ W).
    by exists W.
  rewrite -addsetI.
  exact: addsubset.
move=> _ /= [V FV]  <-.
by exists p; exists p => //; exists 0; rewrite ?addr0//; exact: mem0_nbhsbasisat0.
Qed.

#[local] Lemma  nbhs_singleton : forall (p : E) (A : set E), nbhs_fromfilter0 p A -> A p.
Proof.
move=> p A [_/= [C f0C <-]]; apply; exists p => //; exists 0; rewrite ?addr0//.
exact: mem0_nbhsbasisat0.
Qed.

#[local] Lemma nbhs_nbhs (p : E) (A : set E) : nbhs_fromfilter0 p A ->
  nbhs_fromfilter0 p (nbhs_fromfilter0^~ A).
Proof. (* fun x => nbhs_fromfilter0 x A est un voisinage de p *)
rewrite /nbhs_fromfilter0/=.
move=> [B/= [C f0C <- pCA]].
red.
simpl. 
have [D f0D DDC] := split_nbhsbasisat0 f0C.
exists ([set p] `+ D).
  by exists D.
move=> _ [/= _] -> [c Cc <-].
red.
simpl.
exists ([set p + c] `+ D) => //.
  by exists D.
apply: (subset_trans _ pCA).
apply: (@subset_trans _ ([set p] `+ ([set c] `+ D))).
  exact: addsubsetA.
apply: addsubset => //.
apply: subset_trans DDC.
apply: addsubset => //.
by move=> x ->.
Qed.

HB.instance Definition _ := @hasNbhs.Build E (nbhs_fromfilter0).

HB.instance Definition _ := @Nbhs_isNbhsTopological.Build E nbhs_filter nbhs_singleton nbhs_nbhs. 

 
#[local] Lemma add_continuous : continuous (fun x : E * E => x.1 + x.2).
Proof.
move=> /= [x1 x2] /= A /= [V] /= [V0 filterV0 <-{V}] VA.
have [W filter0W WV] := split_nbhsbasisat0 filterV0.
exists ([set x1] `+ W, [set x2] `+ W) => /=.
split => //=; first by exists ([set x1] `+ W) => //; exists W.
exists ([set x2] `+ W) => //; exists W => //.
move => [z1 z2] /= [[x ->]] =>  [[y1] Vy <-{z1}].
move => [t ->{t}] [y2 Wy2 <-].
apply: VA => //=.
exists (x1 + x2) => //; exists (y1 + y2).
apply: WV =>/=; exists y1 => //; exists y2 =>//.
by rewrite addrACA.
Qed.

#[local] Lemma scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2).
Proof. 
move => /= [r x] /= A /= [_] /= [V fV <-] VA.
have [r0|] := eqVneq r 0.

have [V0 fV0 rV0] := (split_nbhsbasisat0 fV).
have [/= s [s0]] := (absorbing_nbhsbasisat0 fV0 x). 
rewrite inE => xV''.
have [convV'' balV''] := (absconvex_nbhsbasisat0 fV0 ). 
exists ((ball_ normr 0 (minr 1 s)) (*[set t | `|t| < r]*), [set x] `+ V0) => //=.
  split. 
   exists (minr 1 s) => //=. rewrite /minr; case: ifPn => //. 
   by rewrite r0.
   by exists ([set x] `+ V0) => //; exists V0. 
move => [z1 z2] /=. 
rewrite sub0r normrN => -[z1s]. 
move=> [_ ->] [y] Vy <- {z2}. 
apply: VA => /=. 
rewrite r0; exists 0. 
rewrite scale0r //.
exists (z1 *: (x + y)); rewrite ?add0r //. 
apply: rV0 => /=. 
exists (z1 *: x). 
 apply: (balV'' (z1 * s^-1)). 
  rewrite normrM normfV ltW // ltr_pdivrMr ?normr_gt0 ?gt_eqF //.  
  rewrite mul1r.
  rewrite [ltRHS]gtr0_norm //.  
  rewrite (lt_le_trans z1s) //. 
  by rewrite /minr; case: ifPn => // /ltW //. 
  exists (s *: x) => //.
  by  rewrite !scalerA divfK//  gt_eqF //.
exists (z1 *: y) => //.
  apply: (balV'' z1).
  rewrite (le_trans (ltW z1s)) //. 
  rewrite /minr; case: real_ltP => //.
  rewrite gtr0_real //.  
  by exists y.
by rewrite -scalerDr.

have [V0 fV0 rV0] := (split_nbhsbasisat0 fV).
have [V' fV' rV'] := (split_nbhsbasisat0 fV0).
have [V'' fV'' rV''] := (expand_nbhsbasisat0 r fV'). 
have [/= s [s0 (*xV'' xx'*)]] := (absorbing_nbhsbasisat0 fV'' x). 
rewrite inE => xV''.
have [convV'' balV''] := (absconvex_nbhsbasisat0 fV''). 
exists ([set r] `+ (ball_ normr 0 (Num.min `|r| (`|r * s|))) (*[set t | `|t| < r]*), [set x] `+ V'') => //=.
  split. 
    exists ((Num.min `|r| (`|r * s|))) => //=.
      rewrite /minr; case: ifPn.  rewrite normr_gt0 //.
      rewrite normr_gt0 => _. 
      by rewrite mulf_neq0 // gt_eqF.
    move=> u/= rur.
    exists r => //.
    exists (u - r).
      rewrite sub0r normrN distrC (lt_le_trans rur)//. 
    by rewrite subrKC.
  by exists ([set x] `+ V'') => //; exists V''.
move => [z1 z2] /= => [] [[x0] -> {x0}] [y]. 
rewrite add0r normrN => yr. 
move => <- [H ->] [t] Vt <-. 
apply: VA => /=.
exists (r *: x) => //.
exists (r *: t + y *: x + y *: t) => //.
  apply: rV0 => /=. 
  exists (r *:t) => //. 
    apply: rV'. exists 0. apply: mem0_nbhsbasisat0 =>//. exists (r *: t). apply: rV''. exists t => //.
    by rewrite add0r.
  exists  (y *: x + y *: t)=> //.
    apply: rV'.
      exists (y *: x).
        apply: rV''.
        exists ((r^-1 * y) *: x).  
          apply: (balV'' (r^-1 * y * s^-1)).
          rewrite -mulrA normrM normfV // ler_pdivrMl ?normr_gt0 // mulr1.
          rewrite normrM -ler_pdivlMr ?normr_gt0 // ?gt_eqF // ?invr_gt0 //.
          rewrite (le_trans (ltW yr)) //; rewrite /minr.
          case: ifPn => //. move/ltW. rewrite normrM normfV //.  
          by rewrite invrK //.
          by move=> _; rewrite normfV normrM invrK.     
         exists (s *: x) => //.
     rewrite !scalerA divfK//  gt_eqF //. 
     by rewrite scalerA mulrA divff// mul1r.
    exists (y *: t) => //.
    apply: rV''.
    exists ((r^-1 * y) *: t).
      apply: (balV'' (r^-1 * y)).
        rewrite normrM normfV// ler_pdivrMl ?normr_gt0// mulr1. 
        apply: (le_trans (ltW yr)). 
        rewrite /minr.  
        case : real_ltP => //. 
      by exists t.
    by rewrite scalerA mulrA divff// mul1r.
  by rewrite addrA.
rewrite !addrA.
rewrite -scalerDr.
rewrite -addrA.
rewrite -scalerDr.
by rewrite scalerDl.
Qed. 

#[local] Lemma locally_convex : exists2 B : set_system E,
    (forall b, b \in B -> absolutely_convex_set b) & nbhs_basis 0 B.
Proof.
exists nbhsbasis_at0; first by move=> b; rewrite inE; apply: absconvex_nbhsbasisat0.
move => b [a] /= [a'] fa; rewrite addset0 => <- ab /=.
by exists a' => //=; split => //; exact: mem0_nbhsbasisat0.
Qed.
 
HB.instance Definition _ := @PreTopologicalLmod_isConvexTvs.Build R E add_continuous scale_continuous locally_convex.

HB.end.


HB.factory Record Nbhssubbasis0_isConvexTvs (R: numFieldType) E & GRing.Lmodule R E (*& isConvexTvsat R E*) := {
  nbhssubbasis0 : set_system E ;
  nonempty_nbhssubbasisat0 : exists U, nbhssubbasis0 U;
  mem0_nbhssubbasisat0 : forall B, nbhssubbasis0 B -> B 0 ;
  expand_nbhssubbasisat0 : forall B r, nbhssubbasis0 B -> (*0 <= r ->*)
    exists2 U, nbhssubbasis0 U & r `*: U `<=` B ; (* implies circled *)
  absorbing_nbhssubbasisat0 : forall B , nbhssubbasis0 B -> pabsorbing_set B;
  absconvex_nbhssubbasisat0 : forall B, nbhssubbasis0 B -> absolutely_convex_set B }.

Definition nbhs_fromsubbasis0 (R : numFieldType) (E : zmodType)
    (nbhssubbasis0 : set_system E)  :=
  finI_from nbhssubbasis0 id.


HB.builders Context R E & Nbhssubbasis0_isConvexTvs R E.

From mathcomp Require Import finmap.
(*Open Scope fset_scope.  *)

Local Definition nbhsbasis_at0 := @nbhs_fromsubbasis0 R E nbhssubbasis0.

#[local] Lemma nonempty_nbhsbasisat0 : exists U, nbhsbasis_at0 U.
Proof.
have [U fU] := nonempty_nbhssubbasisat0; exists U.
rewrite /nbhsbasis_at0 /nbhs_fromsubbasis0 /finI_from /=.
exists [fset U]%fset => /=.
  by move=> _ /fset1P ->; rewrite mem_set //=; exists U; rewrite ?addset0.
rewrite /bigcap /=; apply/seteqP; split => z /=; first by apply; rewrite inE. (*bigcap_set1 not working*) by move=> Uz i /fset1P ->.
Qed.

#[local] Lemma nbhsbasis_at0I : forall U V, nbhsbasis_at0 U -> nbhsbasis_at0 V ->
    exists2 W, nbhsbasis_at0 W & W `<=` U `&` V.
Proof.
move=> U V [/= I fI IV] [/=J fJ JU].
exists (U `&` V) => //.
exists (I `|` J)%fset. 
 move => /= W; rewrite inE => /orP [WI|WJ]; rewrite mem_set //=. 
   by have := (fI _ WI); rewrite asboolE //=. 
(* extremely hard to understand that asboolE is to be used here *)
 by have := (fJ _ WJ); rewrite asboolE //=. 
rewrite -IV -JU /bigcap /=; apply/seteqP; split => z /=.
  by move=> H; split => i iI; apply: H; rewrite inE; apply/orP; [left|right]. (*bigcapI does not work*)
move => [Iz Jz] i; rewrite inE => /orP [|]; first by apply: Iz.
by apply: Jz.
Qed.

#[local] Lemma mem0_nbhsbasisat0 : forall B, nbhsbasis_at0 B -> B 0.
Proof.
by move => B [/= I fI <-] U /= /fI /=; rewrite asboolE /= => /mem0_nbhssubbasisat0.
Qed.


#[local] Lemma expand_nbhsbasisat0 : forall B r, nbhsbasis_at0 B ->
  exists2 U, nbhsbasis_at0 U & r `*: U `<=` B.
Proof. 
move => B r [/= I fI BI]. (* Change to a type I'*)
have H : forall i, (i \in I) -> exists2 V, nbhssubbasis0 V & r `*: V `<=` i.
  move => i /(fI i); rewrite asboolE => /(expand_nbhssubbasisat0 r) /=  [V nV rVi].
  by exists V.
pose f i := if (i \in I) =P true is ReflectT h then (sval (cid2 (H _ h))) else setT.
have Hn i : i \in I -> nbhssubbasis0 (f i). 
 by rewrite /f; case: eqP => // h _; case: cid2.
have Hr i : i \in I -> r `*: (f i) `<=` i.
 by rewrite /f; case: eqP => // h _; case: cid2.
pose U := \bigcap_(i in [set` I])(f i).
exists U. exists (f @` I)%fset => /=.
  - by move => _ /imfsetP[/= b bi ->]; apply/mem_set/Hn.
  - by rewrite set_imfset bigcap_image.  
rewrite -BI => x /= [y]; rewrite /U /= => Uy rx i /= j.
apply: Hr => //=. 
by exists y => //; apply: Uy.
Qed. 
 
#[local] Lemma absorbing_nbhsbasisat0 : forall B , nbhsbasis_at0 B -> pabsorbing_set B.
Proof.
move => B [/= I fI BI] /= x.
have /= H : forall i, (i \in I) -> exists r : {posnum R}, r%:num *: x \in i. 
  move => i /(fI i); rewrite asboolE => /absorbing_nbhssubbasisat0/(_ x) [r r0 rx].
  by exists (PosNum r0).
pose f (i : set E)  : {posnum R} := [elaborate if (i \in I) =P true is ReflectT h then (sval (cid (H i h))) else 1%:pos]. (*elaborate???*)
have /= Hr i : i \in I -> (f i)%:num *: x \in i. 
 by rewrite /f; case: eqP => // h _; case: cid.
pose r0 : {posnum R} := [elaborate \big[Order.min/1%:pos]_(i <- I) f i].
exists r0%:num  => //. (* waouh *)
rewrite -BI asboolE /= => i /= iI.
have ni : nbhssubbasis0 i by apply/set_mem/fI.
have [_ bali] := (absconvex_nbhssubbasisat0 ni).
apply: (bali (r0%:num / (f i)%:num)). 
 rewrite ger0_norm // ler_pdivrMr // mul1r /r0 num_le //. 
 by apply: ge_bigmin_seq.
exists ((f i)%:num *: x); first apply/set_mem/Hr => //.
by rewrite scalerA mulfVK //. 
Qed.

#[local] Lemma absconvex_nbhsbasisat0 : forall B, nbhsbasis_at0 B -> absolutely_convex_set B.
Proof.
move => B [/= I fI <-]; split. 
  move=> x y r; rewrite !asboolE /= => xb yb => // i /= iI.
  have /fI := iI; rewrite asboolE; move/absconvex_nbhssubbasisat0 => [+ _]. 
  move=> /(_ x y r); rewrite !asboolE; apply; first by apply: xb. 
  by apply: yb => /=.
move=> r r1 x /= [y] capy <- i /= iI.
have /fI := iI; rewrite asboolE; move/absconvex_nbhssubbasisat0 => [_ +]. 
by move=> /(_ r r1 (r *: y)); apply => /=; exists y => //; apply: capy.
Qed.


HB.instance Definition _ := @Nbhsbasisat0_isConvexTvs.Build R E 
  nbhsbasis_at0 
  nonempty_nbhsbasisat0
  nbhsbasis_at0I 
  mem0_nbhsbasisat0
  expand_nbhsbasisat0
  absorbing_nbhsbasisat0
  absconvex_nbhsbasisat0.

HB.end.


Section ConvexTvs_numDomain.
Context (R : numDomainType) (E : convexTvsType R) (U : set E).

Lemma nbhs0N : nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. exact/nbhs0N_subproof/scale_continuous. Qed.

Lemma nbhsT (x :E) : nbhs 0 U -> nbhs x (+%R x @` U).
Proof. exact/nbhsT_subproof/add_continuous. Qed.

Lemma nbhsB (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @` U).
Proof. exact/nbhsB_subproof/add_continuous. Qed.

End ConvexTvs_numDomain.

Section ConvexTvs_numField.

Lemma nbhs0Z (R : numFieldType) (E : convexTvsType R) (U : set E) (r : R) :
  r != 0 -> nbhs 0 U -> nbhs 0 ( *:%R r @` U ).
Proof.
move=> r0 U0; have /= := scale_continuous (r^-1, 0) U.
rewrite scaler0 => /(_ U0)[]/= B [B1 B2] BU.
near=> x => //=; exists (r^-1 *: x); last by rewrite scalerA divff// scale1r.
by apply: (BU (r^-1, x)); split => //=;[exact: nbhs_singleton|near: x].
Unshelve. all: by end_near. Qed.

Lemma nbhsZ  (R : numFieldType) (E : convexTvsType R) (U : set E) (r : R) (x :E) :
  r != 0 -> nbhs x U -> nbhs (r *:x) ( *:%R r @` U ).
Proof.
move=> r0 U0; have /= := scale_continuous ((r^-1, r *: x)) U.
rewrite scalerA mulVf// scale1r =>/(_ U0)[] /= B [B1 B2] BU.
near=> z; exists (r^-1 *: z); last by rewrite scalerA divff// scale1r.
by apply: (BU (r^-1,z)); split; [exact: nbhs_singleton|near: z].
Unshelve. all: by end_near. Qed.

End ConvexTvs_numField.

Section standard_topology.
Variable R : numFieldType.

(** NB: we have almost the same proof in `pseudometric_normed_Zmodule.v` *)
Let standard_add_continuous : continuous (fun x : R^o * R^o => x.1 + x.2).
Proof.
move=> [/= x y]; apply/cvgrPdist_lt=> _/posnumP[e]; near=> a b => /=.
by rewrite opprD addrACA normm_lt_split.
Unshelve. all: by end_near. Qed.

Let standard_scale_continuous : continuous (fun z : R^o * R^o => z.1 *: z.2).
Proof.
move=> [/= k x]; apply/cvgrPdist_lt => _/posnumP[e]; near +oo_R => M.
near=> l z => /=; have M0 : 0 < M by [].
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normrM.
  rewrite (@le_lt_trans _ _ (M * `|x - z|)) ?ler_wpM2r -?ltr_pdivlMl//.
  by near: z; apply: cvgr_dist_lt; rewrite // mulr_gt0 ?invr_gt0.
rewrite (@le_lt_trans _ _ (`|k - l| * M)) ?ler_wpM2l -?ltr_pdivlMr//.
  by near: z; near: M; exact: (@cvg_bounded _ R^o _ _ _ _ _ (@cvg_refl _ _)).
by near: l; apply: cvgr_dist_lt; rewrite // divr_gt0.
Unshelve. all: by end_near. Qed.

Local Open Scope convex_scope.


Let standard_ball_convex_set (x : R^o) (r : R) : convex_set (ball x r).
Proof.
apply/convex_setW => z y; rewrite !inE -!ball_normE /= => zx yx l l0 l1.
rewrite inE/=.
rewrite [X in `|X|](_ : _ = (x - z : convex_lmodType _) <| l |>
                            (x - y : convex_lmodType _)).
  by rewrite opprD -[in LHS](convmm l x) addrACA -scalerBr -scalerBr.
rewrite (le_lt_trans (ler_normD _ _))// !normrM.
rewrite (@ger0_norm _ l%:num)// (@ger0_norm _ l%:num.~) ?onem_ge0//.
rewrite -[ltRHS]mul1r -(add_onemK l%:num) [ltRHS]mulrDl.
by rewrite ltrD// ltr_pM2l// onem_gt0.
Qed.

Let standard_ball_balanced_set (r : R) : balanced_set (ball (0 : R^o) r).
Proof.
move => t /= t1 z /= [y].  
rewrite -ball_normE /= !sub0r !normrN => + <-. 
rewrite normrM. Search ( _ * _ < _ * _).  
case: (eqVneq `|t| (1 : R)).
  by move=> -> ; rewrite mul1r.
move=> t11.
have : (`|t| <1) by rewrite lt_neqAle; apply/andP; split.
by move => lt1 yr; rewrite -[ltRHS]mul1r ltr_pM ?normr_ge0.
Qed.

Let standard_locally_convex_set :
  exists2 B : set_system R^o, (forall b, b \in B -> absolutely_convex_set b) & nbhs_basis 0 B.
Proof.
exists [set B | exists r, B = ball 0 r].
   move=> B/= /[!inE]/= [] [r] ->; split; first by  exact: standard_ball_convex_set.
   by exact: standard_ball_balanced_set.
move=> B [] r /= r0 /= Br.
exists (ball 0 r); last by exact: Br.
split; last by apply: ballxx.
by exists r. 
Qed.

HB.instance Definition _ :=
  PreTopologicalNmodule_isTopologicalNmodule.Build R^o standard_add_continuous.
HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalLmodule.Build R R^o standard_scale_continuous.
HB.instance Definition _ :=
  Uniform_isConvexTvs.Build R R^o standard_locally_convex_set.

End standard_topology.

Section prod_ConvexTvs.
Context (K : numFieldType) (E F : convexTvsType K).

Local Lemma prod_add_continuous :
  continuous (fun x : (E * F) * (E * F) => x.1 + x.2).
Proof.
move => [/= xy1 xy2] /= U /= [] [A B] /= [nA nB] nU.
have [/= A0 [A01 A02] nA1] := @add_continuous E (xy1.1, xy2.1) _ nA.
have [/= B0 [B01 B02] nB1] := @add_continuous F (xy1.2, xy2.2) _ nB.
exists ([set xy | A0.1 xy.1 /\ B0.1 xy.2], [set xy | A0.2 xy.1 /\ B0.2 xy.2]).
  by split; [exists (A0.1, B0.1)|exists (A0.2, B0.2)].
move => [[x1 y1][x2 y2]] /= [] [] a1 b1 [] a2 b2.
by apply: nU; split; [exact: (nA1 (x1, x2))|exact: (nB1 (y1, y2))].
Qed.

Local Lemma prod_scale_continuous :
  continuous (fun z : K^o * (E * F) => z.1 *: z.2).
Proof.
move => [/= r [x y]] /= U /= []/= [A B] /= [nA nB] nU.
have [/= A0 [A01 A02] nA1] := @scale_continuous K E (r, x) _ nA.
have [/= B0 [B01 B02] nB1] := @scale_continuous K F (r, y) _ nB .
exists (A0.1 `&` B0.1, A0.2 `*` B0.2).
  by split; [exact: filterI|exists (A0.2,B0.2)].
by move=> [l [e f]] /= [] [Al Bl] [] Ae Be; apply: nU; split;
  [exact: (nA1 (l, e))|exact: (nB1 (l, f))].
Qed.

Local Lemma prod_locally_convex :
  exists2 B : set_system (E * F), (forall b, b \in B -> absolutely_convex_set b) & nbhs_basis (0,0) B.
Proof.
have [Be Bce Beb] := @locally_convex K E.
have [Bf Bcf Bfb] := @locally_convex K F.
pose B := [set ef : set (E * F) | 
  exists be, exists2 bf, Be be & Bf bf /\ be `*` bf = ef].
have lem : nbhs_basis (0,0) B.
  move=> /= b [/= [be bf] [/= nbe nbf]] /= befb /=.
  have [/= be' [Beb' be'0] bbe] := Beb be nbe.
  have [/= bf' [Bfb' bf'0] bbf] := Bfb bf nbf.
  exists (be' `*` bf').
  split; first by exists be'; exists bf'.
  split => //=.
  apply: subset_trans; last by exact: befb.
  move => t /= [bet bft]; split; first by apply: bbe.
  by apply: bbf.
exists B => // => b; rewrite inE /= => [[]] be [] bf Bee [] Bff <-.
have [convbe balbe] := Bce be (mem_set Bee).
have [convbf balbf] := Bcf bf (mem_set Bff).
split.
  move => [x1 y1] [x2 y2] l /[!inE] /= -[xe1 yf1] [xe2 yf2];split.
  by apply/set_mem/convbe;[exact/mem_set|exact/mem_set].
  by apply/set_mem/convbf;[exact/mem_set|exact/mem_set].
move=> r [r1 [x1 y1]] [[x2 y2]]/= [bex bfy] [] <- <-; split.
  by apply/balbe; [exact: r1|exists x2].
  by apply/balbf; [exact: r1|exists y2].
Qed.

HB.instance Definition _ := PreTopologicalNmodule_isTopologicalNmodule.Build
  (E * F)%type prod_add_continuous.
HB.instance Definition _ := TopologicalNmodule_isTopologicalLmodule.Build
  K (E * F)%type prod_scale_continuous.
HB.instance Definition _ :=
  Uniform_isConvexTvs.Build K (E * F)%type prod_locally_convex.

End prod_ConvexTvs.
 
HB.structure Definition LinearContinuous (K : numDomainType) (E : NbhsLmodule.type K)
  (F : NbhsZmodule.type) (s : K -> F -> F) :=
  {f of @GRing.Linear K E F s f &  @Continuous E F f }.

(* https://github.com/math-comp/math-comp/issues/1536
   we use GRing.Scale.law even though it is claimed to be internal *)
HB.factory Structure isLinearContinuous (K : numDomainType) (E : NbhsLmodule.type K)
  (F : NbhsZmodule.type) (s : GRing.Scale.law K F) (f : E -> F) := {
    linearP : linear_for s f ;
    continuousP : continuous f
  }.

HB.builders Context K E F s f & @isLinearContinuous K E F s f.

HB.instance Definition _ := GRing.isLinear.Build K E F s f linearP.
HB.instance Definition _ := isContinuous.Build E F f continuousP.

HB.end.

Section lcfun_pred.
Context  {K : numDomainType} {E : NbhsLmodule.type K}  {F : NbhsZmodule.type}
  {s : K -> F -> F}.

Definition lcfun : {pred E -> F} :=
  mem [set f | linear_for s f /\ continuous f ].

Definition lcfun_key : pred_key lcfun. Proof. exact. Qed.

Canonical lcfun_keyed := KeyedPred lcfun_key.

End lcfun_pred.

Notation "{ 'linear_continuous' U -> V | s }" :=
  (@LinearContinuous.type _ U%type V%type s) : type_scope.
Notation "{ 'linear_continuous' U -> V }" :=
  {linear_continuous U%type -> V%type | *:%R} : type_scope.

Section lcfun.
Context {R : numDomainType} {E : NbhsLmodule.type R}
  {F : NbhsZmodule.type} {s : GRing.Scale.law R F}.

Notation T := {linear_continuous E -> F | s}.

Notation lcfun := (@lcfun _ E F s).

Section Sub.
Context (f : E -> F) (fP : f \in lcfun).

#[local] Definition lcfun_Sub_subproof :=
  @isLinearContinuous.Build _ E F s f (proj1 (set_mem fP)) (proj2 (set_mem fP)).

#[local] HB.instance Definition _ := lcfun_Sub_subproof.

Definition lcfun_Sub : {linear_continuous _  -> _ | _ } := f.

End Sub.

Let lcfun_rect (K : T -> Type) :
  (forall f (Pf : f \in lcfun), K (lcfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2] [Pf3]]].
set G := (G in K G).
have Pf : f \in lcfun.
  by rewrite inE /=; split => // x u v; rewrite Pf1 Pf2.
suff -> : G = lcfun_Sub Pf by apply: Ksub.
rewrite {}/G.
congr (LinearContinuous.Pack (LinearContinuous.Class _ _ _)).
- by congr GRing.isNmodMorphism.Axioms_; exact: Prop_irrelevance.
- by congr GRing.isScalable.Axioms_; exact: Prop_irrelevance.
- by congr isContinuous.Axioms_; exact: Prop_irrelevance.
Qed.

Let lcfun_valP f (Pf : f \in lcfun) : lcfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T lcfun_rect lcfun_valP.

Lemma lcfun_eqP (f g : {linear_continuous E -> F | s}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; exact/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {linear_continuous E -> F | s} by <:].

Variant lcfun_spec (f : E -> F) : (E -> F) -> bool -> Type :=
| Islcfun (l : {linear_continuous E -> F | s}) : lcfun_spec f l true.

Lemma lcfunP (f : E -> F) : f \in lcfun -> lcfun_spec f f (f \in lcfun).
Proof.
move=> /[dup] f_lc ->.
have {2}-> : f = lcfun_Sub f_lc by rewrite lcfun_valP.
by constructor.
Qed.

End lcfun.

Section lcfun_comp.
Context {R : numDomainType} {E F : NbhsLmodule.type R}
  {S : NbhsZmodule.type} {s : GRing.Scale.law R S}
  (f : {linear_continuous E -> F}) (g : {linear_continuous F -> S | s}).

#[local] Lemma lcfun_comp_subproof1 : linear_for s (g \o f).
Proof. by move=> *; move=> *; rewrite !linearP. Qed.

#[local] Lemma lcfun_comp_subproof2 : continuous (g \o f).
Proof. by move=> x; apply: continuous_comp; exact/continuous_fun. Qed.

HB.instance Definition _ := @isLinearContinuous.Build R E S s (g \o f)
  lcfun_comp_subproof1 lcfun_comp_subproof2.

End lcfun_comp.

Section lcfun_lmodtype.
Import GRing.Theory.
Context {R : numFieldType} {E F : convexTvsType R}.
Implicit Types (r : R) (f g : {linear_continuous E -> F}).

Lemma null_fun_continuous : continuous (\0 : E -> F).
Proof. by apply: cst_continuous. Qed.

HB.instance Definition _ := isContinuous.Build E F \0 null_fun_continuous.

#[local] Lemma lcfun_continuousD f g : continuous (f \+ g).
Proof. by move=> /= x; apply: fun_cvgD; exact: continuous_fun. Qed.

HB.instance Definition _ f g :=
  isContinuous.Build E F (f \+ g) (@lcfun_continuousD f g).

#[local] Lemma lcfun_continuousN f : continuous (\- f).
Proof. by move=> /= x; apply: fun_cvgN; exact: continuous_fun. Qed.

HB.instance Definition _ f :=
  isContinuous.Build E F (\- f) (@lcfun_continuousN f).

#[local] Lemma lcfun_continuousM r g : continuous (r \*: g).
Proof. by move=> /= x; apply: fun_cvgZr; exact: continuous_fun. Qed.

HB.instance Definition _ r g :=
  isContinuous.Build E F (r \*: g) (@lcfun_continuousM r g).

#[local] Lemma lcfun_submod_closed : submod_closed (@lcfun R E F *:%R).
Proof.
split; first by rewrite inE; split; first apply/linearP; exact: cst_continuous.
move=> r /= _ _  /lcfunP[f] /lcfunP[g].
by rewrite inE /=; split; [exact: linearP | exact: lcfun_continuousD].
Qed.

HB.instance Definition _ :=
  @GRing.isSubmodClosed.Build _  _ lcfun lcfun_submod_closed.

HB.instance Definition _ :=
  [SubChoice_isSubLmodule of {linear_continuous E -> F } by <:].

End lcfun_lmodtype.

Section lcfunproperties.
Context {R : numDomainType} {E F : NbhsLmodule.type R}
  (f : {linear_continuous E -> F}).

#[warn(note="Consider using `continuous_fun` instead.",cats="discoverability")]
Lemma lcfun_continuous : continuous f.
Proof. exact: continuous_fun. Qed.

#[warn(note="Consider using `linearP` instead.",cats="discoverability")]
Lemma lcfun_linear : linear f.
Proof. move => *; exact: linearP. Qed.

End lcfunproperties.

Import Norm.

Definition gauge_fun  (K : realType) (V : lmodType K) (A : set V)
  (absA :  absolutely_convex_set A) (absorbA: pabsorbing_set A)
  : V -> K :=  
fun v => inf [set r | (0 < r) /\  v \in (fun x => r *: x) @` A].


(* K can be a numDomainType once #1959 is solved *)
(*Definition gauge_fun (K : realType) (V : lmodType K) (A : set V) : V -> \bar K
    := fun v => ereal_inf (EFin @` [set r | 0 < r /\ v \in (fun x => r *: x) @`A]). *)

Section gauge.
Context (K : realType) (V : lmodType K) (A : set V) (absA :  absolutely_convex_set A) (absorbA: pabsorbing_set A).

(*TBD : from PR 1964 *)

Lemma sup_ge0  (B : set K) : (forall x, B x -> 0 <= x) -> 0 <= sup B.
Proof.
Admitted.

Lemma has_sup_wpZl (B : set K) (a : K) : 0 <= a ->  has_sup B -> has_sup [set a * x  | x in B ]. 
Proof. 
Admitted. 

Lemma gt0_has_supZl (B : set K) (a : K) : 0 < a -> has_sup [set a * x  | x in B ] -> has_sup B. 
Proof.
Admitted. 

Lemma ge0_supZl  (B : set K) (a : K) :
  0 <= a -> sup [set a * x  | x in B ] = a * sup B  .
Proof.
Admitted.

(* END TBD *)

Notation gauge_fun := (gauge_fun absA absorbA).

#[local] Lemma gauge0: gauge_fun 0 = 0.
Proof.  
have/absolutely_convex0 := absA =>  A0; rewrite /gauge_fun. 
have [->|]:= eqVneq A set0. 
  rewrite [X in inf X]( _ : _ = set0).
  by rewrite  -subset0 => /= x /=; rewrite image_set0 inE => -[] //. 
  by rewrite inf0.
set P := (X in inf X).
move/set0P/A0 => {}A0.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: lb_le_inf.
    by  exists 1; rewrite /P /=; split => //; rewrite inE; exists 0; rewrite ?scaler0 //; apply: A0. 
  by move=> z; rewrite /P /= => -[z0] _; rewrite ltW.
have infle : forall (r : K), (0 < r) ->  inf P <= r.
  move => r r0. 
  have Pr : P r by split => //; rewrite inE; exists 0 => //; rewrite scaler0.
  apply: ge_inf => //; exists 0 => z /= [] z0 _; rewrite ltW //.
by apply/ler_addgt0Pl => /= r r0; rewrite addr0; apply: infle. 
Qed.

#[local] Lemma gauge_ge0 : forall x, 0 <= gauge_fun x.
Proof. 
move => v. rewrite /gauge_fun.
set P := (X in inf X).
case : (EM (P !=set0)).
  by move=> H; apply: lb_le_inf => // z; rewrite /P /= => -[] z0 _; rewrite ltW.   
move/nonemptyPn -> ;  rewrite  /inf /=.
have -> : [set - (x : K) | x in set0] = set0 by rewrite seteqP; split => // x [] //=.
by rewrite sup0 oppr0. 
Qed.

(*TO BE MOVED to reals *)
Lemma supS (B : set K) (C : set K) : B !=set0 -> has_sup C -> B `<=` C -> sup B <= sup C.
Proof. 
move=> B0 supC BC. 
apply: sup_le => //. 
apply: subset_trans; first by exact: BC. 
by exact: le_down. 
Qed. 

Lemma infS (B : set K) (C : set K) : has_inf B -> C !=set0 -> C `<=` B -> inf B <= inf C.
Proof. 
move=> infB C0 BC. 
rewrite /inf lerN2. 
apply: supS. by apply/nonemptyN.
by apply/has_inf_supN. 
by apply: image_subset.
Qed.
(* END TO BE MOVED *) 


(* TODO : factorise*)
#[local] Lemma ler_gaugeD:
  forall x y, gauge_fun (x + y) <=  gauge_fun x +  gauge_fun y.
Proof.
have A0 : A 0 by move: (absorbA 0)=> [??]; rewrite scaler0 inE.
have :=  absA; rewrite /absolutely_convex_set => -[] convA /= balA.
have lem (w : V) : (exists2 r, (0 < r) & A (r *: w)) -> has_inf [set t | 0 < t /\ w \in t `*: A].
  move => [r r0 Aw]; split => /=; rewrite /set0P; last by exists 0 => z [z0 _]; rewrite ltW.
  exists r^-1 => //=; split=> //.
  rewrite ?invr_gt0 //. 
  rewrite inE /=; exists (r *: w) => //.
  by rewrite scalerA mulVf ?scale1r ?lt0r_neq0 //.
move => x y; rewrite /gauge_fun.
have:= (absorbA x) => -[/= r r0]; rewrite inE /= => Arx.
have:= (absorbA y) => -[/= r' r0']; rewrite inE /= => Ary.
have:= (absorbA (x+y)) => -[/= r2 r20']; rewrite inE /= => Arxy. 
rewrite -inf_sumE; first by apply: lem; exists r.
  by apply: lem; exists r'.
apply: infS; first by apply: lem;  exists r2. 
  exists (r^-1 + r'^-1) => /=.
  exists r^-1 => //=. 
    split=> //; rewrite ?invr_gt0 //. 
    rewrite inE /=; exists (r *: x) => //. 
    by rewrite scalerA mulVf ?scale1r ?lt0r_neq0 //.
  exists r'^-1 => //=.
  split=> //; rewrite ?invr_gt0 //. 
  rewrite inE /=; exists (r' *: y) => //.  
  by rewrite scalerA mulVf ?scale1r ?lt0r_neq0 //.
move => z /= [t [t0]]; rewrite inE /= => [[v] Av rvx] [s] [s0]; rewrite inE /=. 
move => [w Aw twy] <-. rewrite addr_gt0 => //; split => //; rewrite inE /=. 
rewrite -twy -rvx. 
exists  ((t + s)^-1 *: (t *: v + s *: w)).
rewrite scalerDr !scalerA mulrC (mulrC _ s).   
rewrite -divD_onem => //.
pose st := Itv01 (mathcomp_extra.divDl_ge0 (ltW t0) (ltW s0))
                      (mathcomp_extra.divDl_le1 (ltW t0) (ltW s0)). 
have := convA v w st. 
rewrite !inE => /(_ Av Aw); rewrite /conv /=; apply. 
by rewrite !scalerA divff ?scale1r //; rewrite gt_eqF // addr_gt0.  
Qed.

Lemma ge0_infZl : forall (B : set K) [a : K], 0 <= a -> inf [set a * x | x in B] = a * inf B.
Proof.
move => B a a0; rewrite /inf mulrN -(ge0_supZl (-%R @` B) a0); congr (- sup _).
by rewrite !image_comp/=; apply: eq_imagel => //= ? _; rewrite mulrN.
Qed.

Lemma inf_ge0  (B : set K) : (forall x, B x -> 0 <= x) -> 0 <= inf B.
Proof.
move=> B0; have [->|B0'] := eqVneq B set0; first by rewrite inf0.
by apply: lb_le_inf => //; exact/set0P.
Qed.

Lemma inf_pos : inf [set r : K | 0 < r] = 0.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: inf_ge0 => x /ltW.
apply/ler_addgt0Pr => e e0; rewrite add0r.
apply: ge_inf => //=.
by exists 0 => r /ltW.
Qed.

(* see coq-robot/ode_common.v *)
#[local] Lemma gaugeZ r v : gauge_fun (r *: v) = `|r| * gauge_fun v.
Proof.
rewrite /gauge_fun; have [->|] := eqVneq r 0.
  rewrite normr0 mul0r.
  have A0 : A 0 by move: (absorbA 0)=> [??]; rewrite scaler0 inE.
  rewrite [X in inf X](_ : _ = [set r0 | 0 < r0]).
    apply/seteqP; split=> [s []//|s /= s0]/=; split => //.
    by rewrite inE/=; exists 0 => //; rewrite scale0r scaler0.
  exact: inf_pos.
rewrite neq_lt -ge0_infZl// => /orP[r0|r0]; congr inf.
- rewrite ltr0_norm//.
  have balA w : A w -> A (- w).
     move=> Aw; case: absA => _ /(_ (-1)); apply => /=; first by rewrite normrN1.
     by exists w => //; rewrite scaleN1r.
  apply/seteqP; split => [x [x0 /[!inE]-[w Aw xwry]]|_ [y [y0 /[!inE]-[w Aw <-{v} <-]]]]/=.
    exists ((- r)^-1 * x); last by rewrite invrN mulrA mulrNN divff ?mul1r// lt_eqF.
    rewrite mulr_gt0// ?invr_gt0 ?oppr_gt0//; split => //.
    rewrite inE/=; exists (- w); first exact: balA.
    rewrite scalerN invrN mulNr scaleNr opprK -scalerA xwry scalerA.
    by rewrite mulVf ?scale1r ?lt_eqF.
  rewrite inE/= mulr_gt0 ?oppr_gt0//; split => //.
  exists (- w); first exact: balA.
  by rewrite scalerN mulNr scaleNr opprK scalerA.
- rewrite gtr0_norm//.
  apply/seteqP; split => [x [x0 /[!inE]-[w Aw xwry]]|_ [y [y0 /[!inE]-[w Aw <-{v} <-]]]]/=.
    exists (r^-1 * x); last by rewrite mulrA divff ?mul1r// gt_eqF.
    rewrite mulr_gt0 ?invr_gt0 ?gt_eqF//; split => //.
    rewrite inE/=; exists w => //.
    by rewrite -[LHS]scalerA xwry scalerA mulVf ?scale1r// gt_eqF.
  rewrite inE/= mulr_gt0//; split => //.
  by exists w => //; rewrite scalerA.
Qed.

HB.instance Definition _ := @isSemiNorm.Build  K V gauge_fun gauge0 gauge_ge0 ler_gaugeD gaugeZ.

Check (gauge_fun : SemiNorm.type V).
End gauge.


(* https://www.math.uni-konstanz.de/~infusino/TVS-WS18-19/Lect9.pdf *)
(* TODO : define initial topology wrt a family of functions in initial topology *)

Section convex_topology_seminorm.
Context (R : realFieldType) (E : lmodType R) (P : set (SemiNorm.type E)) (H : P !=set0).

Definition seminorm_on  {R : realFieldType} {E : lmodType R} {P : set (SemiNorm.type E)} {H : P !=set0} : Type := E. 

HB.instance Definition _ := GRing.Lmodule.on (@seminorm_on R E P H).

Definition seminorm_subbasis := 
[set A | exists2 p, (P p) & exists2 e, (0 < e) & (A = p @^-1` (ball (0 : R) e))] : set_system E. 

Lemma nonempty_subbasis : exists B, seminorm_subbasis B.
Proof.
move : H => [p] Pp. 
exists (p @^-1` (ball (0 : R) 1)).
by exists p => //; exists 1.
Qed.

Lemma mem0_seminorm_subbasis : forall B, seminorm_subbasis B -> B 0.
Proof. 
by move=> B; rewrite /seminorm_subbasis /= => -[p Pp [e]] e0 -> /=; rewrite norm0; exact: ballxx.
Qed.

Lemma split_seminorm_subbasis : 
  forall B, seminorm_subbasis B -> exists2 C, seminorm_subbasis C & ( C `+ C  `<=` B).
Proof.  
move=> B; rewrite /seminorm_subbasis /= => -[p Pp [e e0 ->]] /=.
exists (p @^-1` (ball (0 : R) (e/2))); first by exists p => //; exists (e/2); rewrite ?divr_gt0.
rewrite /ball /= => z /=; rewrite sub0r normrN => -[x]; rewrite sub0r normrN => ballx [y]. 
rewrite sub0r normrE => bally <-; rewrite (splitr e).
apply: le_lt_trans; last first. 
  apply: ltrD; first by exact: ballx.
  by exact: bally.
(* Beware that now that we opened the Norm module ler_normD refers to semiNorm and not to norm*)
apply: le_trans; last by apply: Num.Theory.ler_normD. 
have :  p (x + y) <= p x + p y by apply: ler_normD. 
by rewrite ger0_le_norm ?nnegrE ?addr_ge0 ?norm_ge0. 
Qed.

Lemma expand_seminorm_subbasis : 
  forall B r, seminorm_subbasis B -> exists2 U, seminorm_subbasis U & (r `*: U `<=` B). 
move=> B r ; rewrite /seminorm_subbasis /= => -[p Pp [e e0 ->]] /=.
case: (eqVneq r (0 : R)).
  move => ->; exists (p @^-1` (ball (0 : R) (e))); first by exists p => //; exists e.
  by move => z /= [x] _; rewrite scale0r => <-; rewrite norm0; exact: ballxx.
move=> rneq0.
exists (p @^-1` (ball (0 : R) (e/`|r|))).
  by exists p => //; exists (e/`|r|); rewrite ?divr_gt0 // normr_gt0.
rewrite /ball /= => z /=; rewrite sub0r normrN => -[x]; rewrite sub0r normrN => ballx <-.
by rewrite normZ normrM normr_id mulrC -ltr_pdivlMr ?normr_gt0.
Qed.

(* TBA convex *)
Lemma lt_conv (x y r e : R): (0 <= r)-> (r <= 1) -> (x < e)-> (y < e) -> r * x + r.~ * y < e.
Proof.
move => r0 r1 xe ye.
have [->|] := eqVneq r 0; first by rewrite mul0r /onem subr0 add0r mul1r.
have [->|] := eqVneq r 1; first by  rewrite mul1r /onem subrr mul0r addr0.
move=> rneq0 rneq1.
have -> : e = r * e + (1 -r) * e by rewrite -mulrDl addrCA subrr addr0 mul1r.
apply: ltrD. 
rewrite lter_pM2l lt_neqAle; apply/andP; split => //; first by rewrite eq_sym. 
by move: xe; rewrite lt_def; move/andP => []; rewrite eq_sym //.
by apply: ltW.
rewrite lter_pM2l /onem ?subr_gt0 ?ltW //.
by rewrite lt_def; apply/andP; split => //; rewrite eq_sym.
Qed. 

Lemma le_conv (x y r e : R): 
(0 <= r)-> (r <= 1) -> (0 <= x) -> (x <= e)-> (0 <= y) -> (y <= e) -> r * x + r.~ * y <= e.
Proof. 
move => r0 r1 x0 xe y0 ye.
rewrite /onem. 
have -> : e = r * e + (1 -r) * e by rewrite -mulrDl addrCA subrr addr0 mul1r. 
apply: lerD; first by rewrite ler_pM. 
by rewrite ler_pM ?subr_ge0 //.  
Qed.


Lemma convex_seminorm_subbasis: forall B, seminorm_subbasis B -> convex_set B.
Proof. 
move=> B ; rewrite /seminorm_subbasis /= => -[p Pp [e e0 ->]] x y r.
rewrite !inE /ball /= !sub0r !normrN => px py.
rewrite /conv /=. 
have lem1: 
`|p (r%:num *: x + (r%:num).~ *: y)| <= `|p (r%:num *: x) +  p ((r%:num).~ *: y)|.
 rewrite (@ger0_le_norm _   (p (r%:num *: x + (r%:num).~ *: y)))  ?nnegrE  ?norm_ge0 ?ler_normD //. 
   by rewrite ?nnegrE ?addr_ge0 ?norm_ge0 ?ler_normD//. 
apply:le_lt_trans; first by exact: lem1.
apply: le_lt_trans; first by apply: Num.Theory.ler_normD. 
rewrite !normZ !normrM !normr_id [X in X*_]ger0_norm //.
rewrite [X in _ + X*_]ger0_norm ?onem_ge0 //. 
by apply: lt_conv.
Qed.
 

Lemma balanced_seminorm_subbasis: forall B, seminorm_subbasis B -> balanced_set B.
Proof.
move => _ [p Pp [r r0] ->] /= s s1 z /= [x]. 
rewrite /ball /ball_ /= !sub0r !normrN => pixr <-.
rewrite normZ normrM normr_id.
apply: le_lt_trans; last by exact: pixr.
by rewrite ler_piMl ?normr_ge0.
Qed.

Lemma absolutely_convex_seminorm_subbasis: forall B, seminorm_subbasis B -> absolutely_convex_set B.
Proof.
move => b Bb; split; first by apply: convex_seminorm_subbasis.
by apply: balanced_seminorm_subbasis.
Qed.

Lemma absorbing_seminorm : forall B , seminorm_subbasis B -> pabsorbing_set B.
move => _ [p Pp [r r0] ->] /= y.
case: (eqVneq (p y) 0) => y0.
  by exists 1 => //; rewrite scale1r inE /ball/ball_ /= sub0r normrN y0 normr0.
exists (r/2 * (p y)^-1).
  by rewrite !divr_gt0 // lt_neqAle eq_sym norm_ge0; apply/andP.
(*normr_gt0 not available for seminorms *)
rewrite inE /ball/ball_ /= sub0r normrN !normZ !normrM !normr_id. Check normrE.
rewrite !normfV -mulrA mulVf ?normr_eq0 ? mulr1//. 
by rewrite ltr_pdivrMr !gtr0_norm ?ltr_pMr // ltrDr.
Qed.

HB.instance Definition _ :=  @Nbhssubbasis0_isConvexTvs.Build R (seminorm_on) seminorm_subbasis nonempty_subbasis mem0_seminorm_subbasis expand_seminorm_subbasis absorbing_seminorm absolutely_convex_seminorm_subbasis.
  
Check (seminorm_on : convexTvsType R). 
(*
Lemma range_seminorm:  forall f : SemiNorm.type E, (exists x : E, (f x)!= 0 ) -> range f = [set r : R | 0 <= r]. 
Proof. 
move => f [x /eqP fx] /=.
rewrite eqEsubset; split => r; first by move => [t _] <-; apply: norm_ge0.
have f0 : 0 < (f x).
  have : 0<= f(x) by  apply: @norm_ge0. 
  by rewrite le0r; move/orP => [/eqP /fx | ].
have /ltW := f0; rewrite -eqr_norm_id; move/eqP => normf /=.
exists ((r/ f(x) *: x))=> //.  
rewrite normZ normrM normfV normf -mulrA [X in _ * X]mulrC divff ?mulr1; apply/eqP => //.  
by rewrite // eqr_norm_id.
Qed.
*)



(* NB: this doesn't work as we strongly need a 0 basis. Here we are considering nbhs a = [ [A : set E |, exists e , A = [x | |p(x) - p(a)| <e]], while working from a 0 basis gives us nbhs a = [A : set E |, exists e , A = [x | p(x -a) < e]] *)

(*
#[local] Lemma  initial_fam_add_continuous : continuous (fun x : seminorm_on *  seminorm_on => x.1 + x.2).
Proof.
apply/continuous_init_fam => i/= [a b] /= A [e /= e0] piabeA.
have lerB_seminormD v w : p i (v) - p i w <= p i (v + w).
by rewrite -{1}[v](addrK w) lterBDl (le_trans (ler_normD _ _))// addrC Norm.Theory.normN.
have ler_Bseminorm x y :   p i (x) - p i (y) <=  p i ( x - y).
 by rewrite -[p i y]Norm.Theory.normN lerB_seminormD. 
have ler_seminorm_norm x y :   `|p i (x) - p i (y)| <=  p i ( x - y). 
  have [||_|_] // := @real_leP R (p i x) (p i y) => //; rewrite ?realE ?ger0_norm ?norm_ge0 //.   
  by rewrite -(Norm.Theory.normN _ (x - y)) opprB; exact: ler_Bseminorm. 
pose pia := p i @^-1` ball_ [eta normr] (p i a) (e / 2).
pose pib := p i @^-1` ball_ [eta normr] (p i b) (e / 2).
rewrite /nbhs /= /filter_prod /filter_from /=.
exists (pia, pib) => /=.
  by split; apply: initial_fam_continuous; apply: nbhsx_ballx; rewrite divr_gt0.
move=> [c d]/= [piac piad]. rewrite /pia /= in piac.  rewrite /pib /= in piad. 
apply: piabeA; rewrite /ball_ /=. 
Search `| `| _ | - `| _ | | . 
apply: le_lt_trans.  
apply: ler_seminorm_norm. 
rewrite opprD addrACA.
have lem: p i (a - c + (b - d)) <= p i (a - c) + p i (b - d). 
  by rewrite ?ler_normD //.
apply: le_lt_trans; first by exact: lem.
rewrite (splitr e); apply: ltrD. 
move : (piac); rewrite /pia /=. (* apply: ler_seminorm_norm. 
*)
Admitted.

#[local] Lemma  initial_fam_scale_continuous : continuous (fun z : R^o * S => z.1 *: z.2).

  Admitted.
#[local] Lemma  initial_fam_locally_convex : exists2 B : set_system S,
    (forall b, b \in B -> convex_set b) & basis B. Admitted.
                                            
HB.instance Definition _ :=  @PreTopologicalLmod_isConvexTvs.Build R S initial_fam_add_continuous initial_fam_scale_continuous initial_fam_locally_convex.
*)
End convex_topology_seminorm. 

Section generating_seminorm.
Context (R : realType) (E : convexTvsType R).

Definition nbhs_of := sval (cid2 (@locally_convex _ E)).

Definition absconvex_nbhs_of := (svalP (cid2 (@locally_convex _ E))).1.
Definition absconvex_nbhs_of_basis := (svalP (cid2 (@locally_convex _ E))).2.


#[local] Lemma nbhs_ofneq0 : nbhs_of !=set0.
Proof.
Admitted.


Lemma absorbing_nbhs_of : forall b, nbhs_of b -> pabsorbing_set b.
Proof.
rewrite /nbhs_of.
move => b nb x . 
have /(_ b) //= := (absconvex_nbhs_of_basis).
Admitted. 

Definition seminorm_of  := [set p : SemiNorm.type E | exists b, exists h : (nbhs_of b), 
                         p = gauge_fun (absconvex_nbhs_of (mem_set h)) (absorbing_nbhs_of h)].

#[local] Lemma seminorm_ofneq0 : seminorm_of !=set0.
Proof.
Admitted.

#[local] Notation seminormE := (@seminorm_on R E seminorm_of seminorm_ofneq0 : convexTvsType R).

Theorem seminorm_convextvs : continuous (id : E -> seminormE) /\ (continuous (id : seminormE -> E)).
Proof.
Admitted.

Proposition lcfun_seminorm (l : {scalar E}): 
continuous l <-> (exists2 p : SemiNorm.type E, continuous p & (forall x, `|l x| <=p x)).
Proof. 
(* exists I : {fset SemiNorm.type E}, I `<=` seminorm_of &  p = max_i p_i *)
Admitted.

End generating_seminorm.


 (* TODO : apply it to hahn banach *)

 (* TODO : define O-basis *)
