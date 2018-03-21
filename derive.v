(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype bigop matrix interval.
Require Import boolp reals.
Require Import Rstruct Rbar set posnum topology hierarchy landau forms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Section Differential.

Context {K : absRingType} {V W : normedModType K}.

Definition diff (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
  (get (fun (df : {linear V -> W}) => continuous df /\ forall x,
      f x = f (lim F) + df (x - lim F) +o_(x \near F) (x - lim F))).
Canonical diff_linear F phF f := [linear of @diff F phF f].
Canonical diff_raddf F phF f := [additive of @diff F phF f].

Notation "''d_' F" := (@diff _ (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "''d_' F").

Definition differentiable_def (F : filter_on V) (_ : phantom (set (set V)) F)
  (f : V -> W) :=
  continuous ('d_F f) /\
  f = cst (f (lim F)) + 'd_F f \o center (lim F) +o_F (center (lim F)).

Notation differentiable F := (@differentiable_def _ (Phantom _ [filter of F])).

Lemma diffP (F : filter_on V) (f : V -> W) :
  differentiable F f <->
  continuous ('d_F f) /\
  (forall x, f x = f (lim F) + 'd_F f (x - lim F) +o_(x \near F) (x - lim F)).
Proof. by rewrite /differentiable_def funeqE. Qed.

Lemma diff_continuous (F : filter_on V) (f : V -> W) :
  differentiable F f -> continuous ('d_F f).
Proof. by move=> []. Qed.

Lemma diffE (F : filter_on V) (f : V -> W) :
  differentiable F f ->
  forall x, f x = f (lim F) + 'd_F f (x - lim F) +o_(x \near F) (x - lim F).
Proof. by move=> /diffP []. Qed.

Lemma littleo_shift (y x : V) (f : V -> W) (e : V -> V) :
  littleo (locally y) (f \o shift (x - y)) (e \o shift (x - y)) ->
  littleo (locally x) f e.
Proof.
move=> fe _/posnumP[eps]; rewrite near_simpl (near_shift y).
exact: filterS (fe _ [gt0 of eps%:num]).
Qed.

Lemma littleo_center0 (x : V) (f : V -> W) (e : V -> V) :
  [o_x e of f] = [o_ (0 : V) (e \o shift x) of f \o shift x] \o center x.
Proof.
rewrite /the_littleo /insubd /=; have [g /= _ <-{f}|/asboolP Nfe] /= := insubP.
  rewrite insubT //= ?comp_shiftK //; apply/asboolP; apply: (@littleo_shift x).
  by rewrite sub0r !comp_shiftK => ?; apply: littleoP.
rewrite insubF //; apply/asboolP => fe; apply: Nfe.
by apply: (@littleo_shift 0); rewrite subr0.
Qed.

Lemma diff_locallyxP (x : V) (f : V -> W) :
  differentiable x f <-> continuous ('d_x f) /\
  forall h, f (h + x) = f x + 'd_x f h +o_(h \near 0 : V) h.
Proof.
split=> [dxf|[dfc dxf]].
  split; first exact: diff_continuous.
  apply: eqaddoEx => h; have /diffE -> := dxf.
  rewrite lim_id addrK; congr (_ + _); rewrite littleo_center0 /= addrK.
  by congr ('o); rewrite funeqE => k /=; rewrite addrK.
apply/diffP; split=> //; apply: eqaddoEx; move=> y.
rewrite lim_id -[in LHS](subrK x y) dxf; congr (_ + _).
rewrite -(comp_centerK x id) -[X in the_littleo _ _ _ X](comp_centerK x).
by rewrite -[_ (y - x)]/((_ \o (center x)) y) -littleo_center0.
Qed.

Lemma diff_locallyx (x : V) (f : V -> W) : differentiable x f ->
  forall h, f (h + x) = f x + 'd_x f h +o_(h \near 0 : V) h.
Proof. by move=> /diff_locallyxP []. Qed.

Lemma diff_locallyP (x : V) (f : V -> W) :
  differentiable x f <->
  continuous ('d_x f) /\ (f \o shift x = cst (f x) + 'd_x f +o_ (0 : V) id).
Proof. by apply: iff_trans (diff_locallyxP _ _) _; rewrite funeqE. Qed.

Lemma diff_locally (x : V) (f : V -> W) : differentiable x f ->
  (f \o shift x = cst (f x) + 'd_x f +o_ (0 : V) id).
Proof. by move=> /diff_locallyP []. Qed.

End Differential.

Notation "''d_' F" := (@diff _ _ _ _ (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "''d_' F").
Notation differentiable F := (@differentiable_def _ _ _ _ (Phantom _ [filter of F])).

Section jacobian.

Definition jacobian n m (R : absRingType) (f : 'rV[R]_n.+1 -> 'rV[R]_m.+1) p :=
  lin1_mx ('d_p f).

End jacobian.

Section DifferentialR.

Context {V W : normedModType R}.

(* split in multiple bits:
- a linear map which is locally bounded is a little o of 1
- the identity is a littleo of 1
*)
Lemma differentiable_continuous (x : V) (f : V -> W) :
  differentiable x f -> {for x, continuous f}.
Proof.
move=> /diff_locallyP [dfc]; rewrite -addrA.
rewrite (littleo_bigO_eqo (cst (1 : R^o))); last first.
  apply/eqOP; exists 1 => //; rewrite /cst mul1r [`|[1 : R^o]|]absr1.
  near=> y; [rewrite ltrW //; near: y|end_near].
  by apply/locally_normP; eexists=> [|?];
    last (rewrite /= ?sub0r ?normmN; apply).
rewrite addfo; first by move=> /eqolim; rewrite flim_shift add0r.
by apply/eqolim0P; apply: (flim_trans (dfc 0)); rewrite linear0.
Qed.

Section littleo_lemmas.

Variables X Y Z : normedModType R.

Lemma normm_littleo x (f : X -> Y) : `|[ [o_(x \near x) (1 : R^o) of f x]]| = 0.
Proof.
rewrite /cst /=; set e := 'o _; apply/eqP.
have /(_  (`|[e x]|/2) _)/locally_singleton /= := littleoP [littleo of e].
rewrite pmulr_lgt0 // [`|[1 : R^o]|]normr1 mulr1 [X in X <= _]splitr.
by rewrite ger_addr pmulr_lle0 // => /implyP; case: ltrgtP; rewrite ?normm_lt0.
Qed.

Lemma littleo_lim0 (f : X -> Y) (h : _ -> Z) (x : X) :
  f @ x --> (0 : Y) -> [o_x f of h] x = 0.
Proof.
move/eqolim0P => ->.
set k := 'o _; have /(_ _ [gt0 of 1])/= := littleoP [littleo of k].
by move=> /locally_singleton; rewrite mul1r normm_littleo normm_le0 => /eqP.
Qed.

End littleo_lemmas.

Section diff_locally_converse_tentative.
(* if there exist A and B s.t. f(a + h) = A + B h + o(h) then
   f is differentiable at a, A = f(a) and B = f'(a) *)
(* this is a consequence of diff_continuous and eqolim0 *)
(* indeed the differential beeing b *: idfun is locally bounded *)
(* and thus a littleo of 1, and so is id *)
(* This can be generalized to any dimension *)
Lemma diff_locally_converse_part1 (f : R^o -> R^o) (a b : R^o) (x : R^o) :
  f \o shift x = cst a + b *: idfun +o_ (0 : R^o) id -> f x = a.
Proof.
rewrite funeqE => /(_ 0) /=; rewrite add0r => ->.
by rewrite -[LHS]/(_ 0 + _ 0 + _ 0) /cst [X in a + X]scaler0 littleo_lim0 ?addr0.
Qed.

End diff_locally_converse_tentative.

Definition derive (f : V -> W) a v :=
  lim ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ locally' (0 : R^o)).

Definition derivable (f : V -> W) a v :=
  cvg ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ locally' (0 : R^o)).

Lemma derivable_locally (f : V -> W) a v :
  derivable f a v ->
  (fun h => (f \o shift a) (h *: v)) = (cst (f a)) +
    (fun h => h *: (derive f a v)) +o_ (locally' (0 : R^o)) id.
Proof.
move=> df; apply/eqaddoP => _/posnumP[e].
have /eqolimP := df; rewrite -[lim _]/(derive _ _ _).
move=> /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]).
apply: filter_app; near=> h.
  rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
  rewrite /cst /= [`|[1 : R^o]|]absr1 mulr1 => dfv.
  rewrite addrA -[X in X + _]scale1r -(@mulVf _ h); last by near: h.
  rewrite mulrC -scalerA -scalerBr; apply: ler_trans (ler_normmZ _ _) _.
  rewrite -ler_pdivl_mull; last by rewrite absRE normr_gt0; near: h.
  rewrite mulrCA mulVf; last by rewrite absr_eq0; near: h.
  by rewrite mulr1.
by end_near; rewrite /= locally_simpl; exists 1 => // ?? /eqP.
Qed.

Lemma derivable_locallyP (f : V -> W) a v :
  derivable f a v <->
  (fun h => (f \o shift a) (h *: v)) = (cst (f a)) +
    (fun h => h *: (derive f a v)) +o_ (locally' (0 : R^o)) id.
Proof.
split; first exact: derivable_locally.
move=> df; apply/cvg_ex; exists (derive f a v).
apply/(@eqolimP _ _ _ (locally'_filter_on _))/eqaddoP => _/posnumP[e].
have /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]) := df.
apply: filter_app; near=> h.
  rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
  rewrite /cst /= [`|[1 : R^o]|]absr1 mulr1 addrA => dfv.
  rewrite -[X in _ - X]scale1r -(@mulVf _ h); last by near: h.
  rewrite -scalerA -scalerBr; apply: ler_trans (ler_normmZ _ _) _.
  rewrite absRE normfV ler_pdivr_mull; last by rewrite normr_gt0; near: h.
  by rewrite mulrC -absRE.
by end_near; rewrite /= locally_simpl; exists 1 => // ?? /eqP.
Qed.

Lemma derivable_locallyx (f : V -> W) a v :
  derivable f a v -> forall h, f (a + h *: v) = f a + h *: derive f a v
  +o_(h \near (locally' (0 : R^o))) h.
Proof.
move=> /derivable_locally; rewrite funeqE => df.
by apply: eqaddoEx => h; have /= := (df h); rewrite addrC => ->.
Qed.

Lemma derivable_locallyxP (f : V -> W) a v :
  derivable f a v <-> forall h, f (a + h *: v) = f a + h *: derive f a v
  +o_(h \near (locally' (0 : R^o))) h.
Proof.
split; first exact: derivable_locallyx.
move=> df; apply/derivable_locallyP; apply/eqaddoE; rewrite funeqE => h.
by rewrite /= addrC df.
Qed.

Lemma deriveE (f : V -> W) (a v : V) :
  differentiable a f -> derive f a v = 'd_a f v.
Proof.
rewrite /derive /jacobian => /diff_locally -> /=; set k := 'o _.
evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  rewrite funeqE=> h; rewrite !scalerDr scalerN /cst /=.
  by rewrite addrC !addrA addNr add0r linearZ /= scalerA /g.
Admitted.

End DifferentialR.

Section DifferentialR2.
Implicit Type (V : normedModType R).

Lemma derivemxE m n (f : 'rV[R]_m.+1 -> 'rV[R]_n.+1) (a v : 'rV[R]_m.+1) :
  differentiable a f -> derive f a v = v *m jacobian f a.
Proof. by move=> /deriveE->; rewrite /jacobian mul_rV_lin1. Qed.

Definition derive1 V (f : R -> V) (a : R) :=
   lim ((fun h => h^-1 *: (f (h + a) - f a)) @ locally' (0 : R^o)).

Lemma derive1E V (f : R -> V) a : derive1 f a = derive (f : R^o -> _) a 1.
Proof.
rewrite /derive1 /derive; set d := (fun _ : R => _); set d' := (fun _ : R => _).
by suff -> : d = d' by []; rewrite funeqE=> h; rewrite /d /d' /= [h%:A](mulr1).
Qed.

(* Is it necessary? *)
Lemma derive1E' V f a : differentiable a (f : R^o -> V) ->
  derive1 f a = 'd_a f 1.
Proof. by move=> ?; rewrite derive1E deriveE. Qed.

End DifferentialR2.

Section DifferentialR3.

Variables (V W : normedModType R).

Lemma littleo_linear0 (V' W' : normedModType R) (f : {linear V' -> W'})
  (x : V') : [o_x (center x) of f \o center x] = cst 0.
Proof.
rewrite littleo_center0 comp_centerK (comp_centerK x id).
suff -> : [o_ (0 : V') id of f] = cst 0 by [].
rewrite /the_littleo /insubd; case: (insubP _) => // _ /asboolP lino -> {x}.
rewrite /littleo in lino.
suff f0 : forall e, e > 0 -> forall x, `|[x]| > 0 -> `|[f x]| <= e * `|[x]|.
  rewrite funeqE => x; apply/eqP; rewrite -normm_le0.
  case: (lerP `|[x]| 0) => [|xn0].
    by rewrite !normm_le0 => /eqP ->; rewrite linear0.
  rewrite -(mul0r `|[x]|) -ler_pdivr_mulr //; apply/ler_gt0P => e egt0.
  by rewrite ler_pdivr_mulr //; apply: f0.
move=> _ /posnumP[e] x xn0.
have /lino /locallyP [_ /posnumP[d] dfe] := posnum_gt0 e.
set k := ((d%:num / 2) / (PosNum xn0)%:num)^-1.
rewrite -[x in X in X <= _](@scalerKV _ _ k) // linearZZ.
apply: ler_trans (ler_normmZ _ _) _; rewrite -ler_pdivl_mull; last first.
  by rewrite absRE ger0_norm.
suff /dfe /ler_trans : ball 0 d%:num (k^-1 *: x).
  apply.
  rewrite -ler_pdivl_mull // mulrA [_ / _]mulrC -mulrA [_ * (e%:num * _)]mulrA.
  rewrite mulVf // mul1r.
  by apply: ler_trans (ler_normmZ _ _) _; rewrite !absRE normfV.
rewrite -ball_normE /ball_ normmB subr0 invrK.
apply: ler_lt_trans (ler_normmZ _ _) _; rewrite -ltr_pdivl_mulr //.
rewrite absRE ger0_norm // ltr_pdivr_mulr // -mulrA mulVf; last exact:lt0r_neq0.
by rewrite mulr1 [X in _ < X]splitr ltr_addl.
Qed.

Lemma diff_unique (V' W' : normedModType R) (f : V' -> W')
  (df : {linear V' -> W'}) x :
  continuous df -> f \o shift x = cst (f x) + df +o_ (0 : V') id ->
  'd_x f = df :> (V' -> W').
Proof.
move=> dfc dxf; suff dfef' : 'd_x f \- df =o_ (0 : V') id.
  rewrite funeqE => y; apply/subr0_eq.
  rewrite -[0]/(cst 0 y) -(littleo_linear0 [linear of 'd_x f \- df] 0) center0.
  by rewrite -dfef'.
rewrite littleoE => //; apply/eq_some_oP; rewrite funeqE => y /=.
have hdf h :
  (f \o shift x = cst (f x) + h +o_ (0 : V') id) ->
  h = f \o shift x - cst (f x) +o_ (0 : V') id.
  move=> hdf; apply: eqaddoE.
  rewrite hdf -addrA addrCA [cst _ + _]addrC addrK [_ + h]addrC.
  rewrite -addrA -[LHS]addr0; congr (_ + _).
  by apply/eqP; rewrite eq_sym addrC addr_eq0 oppo.
rewrite (hdf _ dxf).
suff /diff_locally /hdf -> : differentiable x f.
  by rewrite opprD addrCA -(addrA (_ - _)) addKr oppox addox.
rewrite /differentiable_def funeqE.
apply: (@getPex _ (fun (df : {linear V' -> W'}) => continuous df /\
  forall y, f y = f (lim x) + df (y - lim x) +o_(y \near x) (y - lim x))).
exists df; split=> //; apply: eqaddoEx => z.
rewrite (hdf _ dxf) !addrA lim_id /funcomp /= subrK [f _ + _]addrC addrK.
rewrite -addrA -[LHS]addr0; congr (_ + _).
apply/eqP; rewrite eq_sym addrC addr_eq0 oppox; apply/eqP.
rewrite littleo_center0 (comp_centerK x id) -[- _ in RHS](comp_centerK x) /=.
by congr ('o).
Qed.

Let dcst (W' : normedModType R) (a : W') (x : V) : continuous (0 : V -> W') /\
  cst a \o shift x = cst (cst a x) + \0 +o_ (0 : V) id.
Proof.
split; first exact: continuous_cst.
apply/eqaddoE; rewrite addr0 funeqE => ? /=; rewrite -[LHS]addr0; congr (_ + _).
by rewrite littleoE; last exact: littleo0_subproof.
Qed.

Lemma diff_cst (W' : normedModType R) a x : ('d_x (cst a) : V -> W') = 0.
Proof. by apply/diff_unique; have [] := dcst a x. Qed.

Lemma differentiable_cst (W' : normedModType R) (a : W') (x : V) :
  differentiable x (cst a).
Proof. by apply/diff_locallyP; rewrite diff_cst; have := dcst a x. Qed.

Let dadd (f g : V -> W) x :
  differentiable x f -> differentiable x g ->
  continuous ('d_x f \+ 'd_x g) /\
  (f + g) \o shift x = cst ((f + g) x) + ('d_x f \+ 'd_x g) +o_ (0 : V) id.
Proof.
move=> df dg; split.
  have /diff_continuous df_cont := df; have /diff_continuous dg_cont := dg.
  by move=> ?; apply: continuousD (df_cont _) (dg_cont _).
apply/eqaddoE; rewrite funeqE => y /=.
have /diff_locallyx dfx := df; have /diff_locallyx dgx := dg.
rewrite -[(f + g) _]/(_ + _) dfx dgx.
by rewrite addrA [_ + (g _ + _)]addrAC -addrA addox addrA addrACA addrA.
Qed.

Lemma diffD (f g : V -> W) x :
  differentiable x f -> differentiable x g ->
  'd_x (f + g) = 'd_x f \+ 'd_x g :> (V -> W).
Proof. by move=> df dg; apply/diff_unique; have [] := dadd df dg. Qed.

Lemma differentiableD (f g : V -> W) x :
  differentiable x f -> differentiable x g -> differentiable x (f + g).
Proof.
by move=> df dg; apply/diff_locallyP; rewrite diffD //; have := dadd df dg.
Qed.

Let dopp (f : V -> W) x :
  differentiable x f -> continuous (- ('d_x f : V -> W)) /\
  (- f) \o shift x = cst (- f x) \- 'd_x f +o_ (0 : V) id.
Proof.
move=> df; split.
  by move=> ?; apply: continuousN; apply: diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=; have /diff_locallyx dfx := df.
by rewrite -[(- f) _]/(- (_ _)) dfx !opprD oppox.
Qed.

Lemma diffN (f : V -> W) x :
  differentiable x f -> 'd_x (- f) = - ('d_x f : V -> W) :> (V -> W).
Proof.
move=> df; have linB : linear (- ('d_x f : V -> W)).
  move=> k p q; rewrite -![(- _ : V -> W) _]/(- (_ _)) linearPZ.
  by rewrite !scalerN opprD.
have -> : - ('d_x f : V -> W) = Linear linB by [].
by apply/diff_unique; have [] := dopp df.
Qed.

Lemma differentiableN (f : V -> W) x :
  differentiable x f -> differentiable x (- f).
Proof.
by move=> df; apply/diff_locallyP; rewrite diffN //; have := dopp df.
Qed.

Lemma diffB (f g : V -> W) x :
  differentiable x f -> differentiable x g ->
  'd_x (f - g) = 'd_x f \- 'd_x g :> (V -> W).
Proof.
move=> df dg; have dNg := differentiableN dg.
by rewrite [LHS]diffD // [X in _ \+ X]diffN.
Qed.

Lemma differentiableB (f g : V -> W) x :
  differentiable x f -> differentiable x g -> differentiable x (f \- g).
Proof. by move=> df dg; apply: differentiableD (differentiableN _). Qed.

Let dscale (f : V -> W) k x :
  differentiable x f -> continuous (k \*: 'd_x f) /\
  (k *: f) \o shift x = cst ((k *: f) x) + k \*: 'd_x f +o_ (0 : V) id.
Proof.
move=> df; split.
  by move=> ?; apply: continuousZ; apply: diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=; have /diff_locallyx dfx := df.
by rewrite -[(k *: f) _]/(_ *: _) dfx !scalerDr scaleox.
Qed.

Lemma diffZ (f : V -> W) k x :
  differentiable x f -> 'd_x (k *: f) = k \*: 'd_x f :> (V -> W).
Proof. by move=> df; apply/diff_unique; have [] := dscale k df. Qed.

Lemma differentiableZ (f : V -> W) k x :
  differentiable x f -> differentiable x (k *: f).
Proof.
by move=> df; apply/diff_locallyP; rewrite diffZ //; have := dscale k df.
Qed.

Let dlin (V' W' : normedModType R) (f : {linear V' -> W'}) x :
  continuous f -> f \o shift x = cst (f x) + f +o_ (0 : V') id.
Proof.
move=> df; apply: eqaddoE; rewrite funeqE => y /=.
rewrite linearD addrC -[LHS]addr0; congr (_ + _).
by rewrite littleoE; last exact: littleo0_subproof.
Qed.

Lemma diff_lin (V' W' : normedModType R) (f : {linear V' -> W'}) x :
  continuous f -> 'd_x f = f :> (V' -> W').
Proof. by move=> fcont; apply/diff_unique => //; apply: dlin. Qed.

Lemma linear_differentiable (V' W' : normedModType R) (f : {linear V' -> W'})
  x : continuous f -> differentiable x f.
Proof.
by move=> fcont; apply/diff_locallyP; rewrite diff_lin //; have := dlin x fcont.
Qed.

Lemma diff_scaler (k : R) (x : V) : 'd_x ( *:%R k) = *:%R k :> (V -> V).
Proof. by rewrite diff_lin //; apply: scaler_continuous. Qed.

Lemma scaler_differentiable (k : R) (x : V) : differentiable x ( *:%R k).
Proof. exact/linear_differentiable/scaler_continuous. Qed.

Lemma diff_scalel (x k : R^o) : 'd_k ( *:%R ^~ x) = *:%R ^~ x :> (R^o -> R^o).
Proof.
have -> : *:%R ^~ x = GRing.scale_linear [lmodType R of R^o] x.
  by rewrite funeqE => ? /=; rewrite [_ *: _]mulrC.
rewrite diff_lin //; apply: scaler_continuous.
Qed.

Lemma scalel_differentiable (x k : R^o) : differentiable k ( *:%R ^~ x).
Proof.
have -> : *:%R ^~ x = GRing.scale_linear [lmodType R of R^o] x.
  by rewrite funeqE => ? /=; rewrite [_ *: _]mulrC.
exact/linear_differentiable/scaler_continuous.
Qed.

Lemma linear_lipschitz (V' W' : normedModType R) (f : {linear V' -> W'}) :
  continuous f -> exists2 k, k > 0 & forall x, `|[f x]| <= k * `|[x]|.
Proof.
move=> /(_ 0); rewrite linear0 => /(_ _ (locally_ball 0 1%:pos)).
move=> /locallyP [_ /posnumP[e] he]; exists (2 / e%:num) => // x.
case: (lerP `|[x]| 0) => [|xn0].
  by rewrite normm_le0 => /eqP->; rewrite linear0 !normm0 mulr0.
rewrite -[`|[x]|]/((PosNum xn0)%:num).
set k := 2 / e%:num * (PosNum xn0)%:num.
have kn0 : k != 0 by apply/lt0r_neq0.
have abskgt0 : `|k| > 0 by rewrite ltr_def absr_ge0 absr_eq0 kn0.
rewrite -[x in X in X <= _](scalerKV kn0) linearZZ.
apply: ler_trans (ler_normmZ _ _) _; rewrite -ler_pdivl_mull //.
suff /he : ball 0 e%:num (k^-1 *: x).
  rewrite -ball_normE /= normmB subr0 => /ltrW /ler_trans; apply.
  by rewrite absRE ger0_norm // mulVf.
rewrite -ball_normE /= normmB subr0; apply: ler_lt_trans (ler_normmZ _ _) _.
rewrite absRE normfV ger0_norm // invrM ?unitfE // mulrAC mulVf //.
by rewrite invf_div mul1r [X in _ < X]splitr; apply: ltr_spaddr.
Qed.

Lemma linear_eqO (V' W' : normedModType R) (f : {linear V' -> W'}) :
  continuous f -> (f : V' -> W') =O_ (0 : V') id.
Proof.
move=> /linear_lipschitz [k kgt0 flip]; apply/eqOP; exists k => //.
exact: filterS filterT.
Qed.

(* TODO: generalize *)
Lemma compoO_eqo (K : absRingType) (U V' W' : normedModType K) (f : U -> V')
  (g : V' -> W') :
  [o_ (0 : V') id of g] \o [O_ (0 : U) id of f] =o_ (0 : U) id.
Proof.
apply/eqoP => _ /posnumP[e].
have /eqO_bigO [_ /posnumP[k]] : [O_ (0 : U) id of f] =O_ (0 : U) id by [].
have /eq_some_oP : [o_ (0 : V') id of g] =o_ (0 : V') id by [].
move=>  /(_ (e%:num / k%:num)) /(_ _) /locallyP [//|_ /posnumP[d] hd].
apply: filter_app; near=> x.
  move=> leOxkx; apply: ler_trans (hd _ _) _; last first.
    rewrite -ler_pdivl_mull //; apply: ler_trans leOxkx _.
    by rewrite invf_div mulrA -[_ / _ * _]mulrA mulVf // mulr1.
  rewrite -ball_normE /= normmB subr0; apply: ler_lt_trans leOxkx _.
  by rewrite -ltr_pdivl_mull //; near: x.
end_near; rewrite /= locally_simpl.
apply/locallyP; exists (k%:num ^-1 * d%:num)=> // x.
by rewrite -ball_normE /= normmB subr0.
Qed.

(* TODO: generalize *)
Lemma compOo_eqo (K : absRingType) (U V' W' : normedModType K) (f : U -> V')
  (g : V' -> W') :
  [O_ (0 : V') id of g] \o [o_ (0 : U) id of f] =o_ (0 : U) id.
Proof.
apply/eqoP => _ /posnumP[e].
have /eqO_bigO [_ /posnumP[k]] : [O_ (0 : V') id of g] =O_ (0 : V') id by [].
move=> /locallyP [_ /posnumP[d] hd].
have /eq_some_oP : [o_ (0 : U) id of f] =o_ (0 : U) id by [].
have ekgt0 : e%:num / k%:num > 0 by [].
move=> /(_ _ ekgt0); apply: filter_app; near=> x.
  move=> leoxekx; apply: ler_trans (hd _ _) _; last first.
    by rewrite -ler_pdivl_mull // mulrA [_^-1 * _]mulrC.
  rewrite -ball_normE /= normmB subr0; apply: ler_lt_trans leoxekx _.
  by rewrite -ltr_pdivl_mull //; near: x.
end_near; rewrite /= locally_simpl.
apply/locallyP; exists ((e%:num / k%:num) ^-1 * d%:num)=> // x.
by rewrite -ball_normE /= normmB subr0.
Qed.

Let dcomp (U V' W' : normedModType R) (f : U -> V') (g : V' -> W') x :
  differentiable x f -> differentiable (f x) g ->
  continuous ('d_(f x) g \o 'd_x f) /\
  g \o f \o shift x = cst ((g \o f) x) + ('d_(f x) g \o 'd_x f) +o_ (0 : U) id.
Proof.
move=> df dg; split.
  by move=> ?; apply: continuous_comp; apply: diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=; have /diff_locallyx -> := df.
rewrite -addrA addrC; have /diff_locallyx -> := dg.
rewrite linearD addrA -addrA; congr (_ + _).
rewrite linear_eqO; last exact: diff_continuous.
rewrite (@linear_eqO _ _ ('d_x f)); last exact: diff_continuous.
rewrite {2}eqoO addOx -[X in _ + X]/((_ \o _) y) compoO_eqo.
by rewrite -[X in X + _]/((_ \o _) y) compOo_eqo addox.
Qed.

Lemma diff_comp (U V' W' : normedModType R) (f : U -> V') (g : V' -> W') x :
  differentiable x f -> differentiable (f x) g ->
  'd_x (g \o f) = 'd_(f x) g \o 'd_x f :> (U -> W').
Proof. by move=> df dg; apply/diff_unique; have [] := dcomp df dg. Qed.

Lemma differentiable_comp (U V' W' : normedModType R) (f : U -> V')
  (g : V' -> W') x : differentiable x f -> differentiable (f x) g ->
  differentiable x (g \o f).
Proof.
by move=> df dg; apply/diff_locallyP; rewrite diff_comp //; have := dcomp df dg.
Qed.

Lemma bilinear_schwarz (U V' W' : normedModType R)
  (f : {bilinear U -> V' -> W'}) : continuous (fun p => f p.1 p.2) ->
  exists2 k, k > 0 & forall u v, `|[f u v]| <= k * `|[u]| * `|[v]|.
Proof.
move=> /(_ 0); rewrite linear0r => /(_ _ (locally_ball 0 1%:pos)).
move=> /locallyP [_ /posnumP[e] he]; exists ((2 / e%:num) ^+2) => // u v.
case: (lerP `|[u]| 0) => [|un0].
  by rewrite normm_le0 => /eqP->; rewrite linear0l !normm0 mulr0 mul0r.
case: (lerP `|[v]| 0) => [|vn0].
  by rewrite normm_le0 => /eqP->; rewrite linear0r !normm0 mulr0.
rewrite -[`|[u]|]/((PosNum un0)%:num) -[`|[v]|]/((PosNum vn0)%:num).
set ku := 2 / e%:num * (PosNum un0)%:num.
set kv := 2 / e%:num * (PosNum vn0)%:num.
rewrite -[X in f X](@scalerKV _ _ ku) // linearZl_LR.
apply: ler_trans (ler_normmZ _ _) _.
rewrite absRE gtr0_norm // -ler_pdivl_mull //.
rewrite -[X in f _ X](@scalerKV _ _ kv) // linearZr_LR.
apply: ler_trans (ler_normmZ _ _) _.
rewrite absRE gtr0_norm // -ler_pdivl_mull //.
suff /he : ball 0 e%:num (ku^-1 *: u, kv^-1 *: v).
  rewrite -ball_normE /= normmB subr0 => /ltrW /ler_trans; apply.
  rewrite ler_pdivl_mull // mulr1 ler_pdivl_mull //.
  by rewrite mulrA [ku * _]mulrAC expr2.
rewrite -ball_normE /= normmB subr0.
have -> : (ku^-1 *: u, kv^-1 *: v) =
  (e%:num / 2) *: ((PosNum un0)%:num ^-1 *: u, (PosNum vn0)%:num ^-1 *: v).
  rewrite invrM ?unitfE // [kv ^-1]invrM ?unitfE //.
  rewrite mulrC -[_ *: u]scalerA [X in X *: v]mulrC -[_ *: v]scalerA.
  by rewrite invf_div.
apply: ler_lt_trans (ler_normmZ _ _) _.
rewrite absRE ger0_norm // -mulrA gtr_pmulr // ltr_pdivr_mull // mulr1.
by rewrite ltr_maxl; apply/andP; split;
  apply: ler_lt_trans (ler_normmZ _ _) _;
  rewrite absRE ger0_norm // mulVf // ltr1n.
Qed.

Lemma bilinear_eqo (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) :
  continuous (fun p => f p.1 p.2) -> (fun p => f p.1 p.2) =o_ (0 : U * V') id.
Proof.
move=> fc; have [_ /posnumP[k] fschwarz] := bilinear_schwarz fc.
apply/eqoP=> _ /posnumP[e]; near=> x.
  apply: ler_trans (fschwarz _ _) _.
  apply: ler_pmul => //; last by rewrite ler_maxr orbC lerr.
    by rewrite pmulr_rge0.
  rewrite -ler_pdivl_mull //; have : `|[x]| <= k%:num ^-1 * e%:num by near: x.
  by apply: ler_trans; rewrite ler_maxr lerr.
end_near; rewrite /= locally_filterE; apply/locally_le_locally_norm.
by exists (k%:num ^-1 * e%:num) => // ? /=; rewrite normmB subr0 => /ltrW.
Qed.

Let dbilin (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) ->
  continuous (fun q => (f p.1 q.2 + f q.1 p.2)) /\
  (fun q => f q.1 q.2) \o shift p = cst (f p.1 p.2) +
    (fun q => f p.1 q.2 + f q.1 p.2) +o_ (0 : U * V') id.
Proof.
move=> fc; split=> [q|].
  by apply: (@continuousD _ _ _ (fun q => f p.1 q.2) (fun q => f q.1 p.2));
    move=> A /(fc (_.1, _.2)) /= /locallyP [_ /posnumP[e] fpqe_A];
    apply/locallyP; exists e%:num => // r [??]; apply: (fpqe_A (_.1, _.2)).
apply/eqaddoE; rewrite funeqE => q /=.
rewrite linearDl !linearDr addrA addrC.
rewrite -[f q.1 _ + _ + _]addrA [f q.1 _ + _]addrC addrA [f q.1 _ + _]addrC.
by congr (_ + _); rewrite -[LHS]/((fun p => f p.1 p.2) q) bilinear_eqo.
Qed.

Lemma diff_bilin (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) -> 'd_p (fun q => f q.1 q.2) =
  (fun q => f p.1 q.2 + f q.1 p.2) :> (U * V' -> W').
Proof.
move=> fc; have lind : linear (fun q => f p.1 q.2 + f q.1 p.2).
  by move=> ???; rewrite linearPr linearPl scalerDr addrACA.
have -> : (fun q => f p.1 q.2 + f q.1 p.2) = Linear lind by [].
by apply/diff_unique; have [] := dbilin p fc.
Qed.

Lemma differentiable_bilin (U V' W' : normedModType R)
  (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) -> differentiable p (fun p => f p.1 p.2).
Proof.
by move=> fc; apply/diff_locallyP; rewrite diff_bilin //; apply: dbilin p fc.
Qed.

Definition Rmult_rev (y x : R) := x * y.
Canonical rev_Rmult := @RevOp _ _ _ Rmult_rev (@GRing.mul [ringType of R])
  (fun _ _ => erefl).

Lemma Rmult_is_linear x : linear (@GRing.mul [ringType of R] x : R^o -> R^o).
Proof. by move=> ???; rewrite mulrDr scalerAr. Qed.
Canonical Rmult_linear x := Linear (Rmult_is_linear x).

Lemma Rmult_rev_is_linear y : linear (Rmult_rev y : R^o -> R^o).
Proof. by move=> ???; rewrite /Rmult_rev mulrDl scalerAl. Qed.
Canonical Rmult_rev_linear y := Linear (Rmult_rev_is_linear y).

Canonical Rmult_bilinear :=
  [bilinear of (@GRing.mul [ringType of [lmodType R of R^o]])].

Lemma diff_Rmult (p : R^o * R^o) :
  'd_p (fun q => q.1 * q.2) = (fun q => p.1 * q.2 + q.1 * p.2) :> (R * R -> R).
Proof. by rewrite diff_bilin //= => ?; apply: lim_mult. Qed.

Lemma differentiable_Rmult (p : R^o * R^o) :
  differentiable p (fun q => q.1 * q.2).
Proof. by apply: differentiable_bilin => ?; apply: lim_mult. Qed.

Lemma eqo_pair (K : absRingType) (U V' W' : normedModType K) (F : filter_on U)
  (f : U -> V') (g : U -> W') :
  (fun t => ([o_F id of f] t, [o_F id of g] t)) =o_F id.
Proof.
apply/eqoP => e egt0; near=> x.
  by rewrite ler_maxl /=; apply/andP; split; near: x.
by end_near; move: e egt0 => /=; apply/eqoP.
Qed.

Let dpair (U V' W' : normedModType R) (f : U -> V') (g : U -> W') x :
  differentiable x f -> differentiable x g ->
  continuous (fun y => ('d_x f y, 'd_x g y)) /\
  (fun y => (f y, g y)) \o shift x = cst (f x, g x) +
  (fun y => ('d_x f y, 'd_x g y)) +o_ (0 : U) id.
Proof.
move=> df dg; split=> [?|]; first by apply: flim_pair; apply: diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=.
rewrite (diff_locallyx df) (diff_locallyx dg).
have -> : forall h e, (f x + 'd_x f y + [o_ (0 : U) id of h] y,
  g x + 'd_x g y + [o_ (0 : U) id of e] y) =
  (f x, g x) + ('d_x f y, 'd_x g y) +
  ([o_ (0 : U) id of h] y, [o_ (0 : U) id of e] y) by [].
by congr (_ + _); rewrite -[LHS]/((fun y => (_ y, _ y)) y) eqo_pair.
Qed.

Lemma diff_pair (U V' W' : normedModType R) (f : U -> V') (g : U -> W') x :
  differentiable x f -> differentiable x g -> 'd_x (fun y => (f y, g y)) =
  (fun y => ('d_x f y, 'd_x g y)) :> (U -> V' * W').
Proof.
move=> df dg.
have lin_pair : linear (fun y => ('d_x f y, 'd_x g y)).
  by move=> ???; rewrite !linearPZ.
have -> : (fun y => ('d_x f y, 'd_x g y)) = Linear lin_pair by [].
by apply: diff_unique; have [] := dpair df dg.
Qed.

Lemma differentiable_pair (U V' W' : normedModType R) (f : U -> V')
  (g : U -> W') x : differentiable x f -> differentiable x g ->
  differentiable x (fun y => (f y, g y)).
Proof.
by move=> df dg; apply/diff_locallyP; rewrite diff_pair //; apply: dpair.
Qed.

Lemma diffM (f g : V -> R^o) x :
  differentiable x f -> differentiable x g ->
  'd_x (f * g) = f x \*: 'd_x g + g x \*: 'd_x f :> (V -> R).
Proof.
move=> df dg.
rewrite [LHS](diff_comp (differentiable_pair _ _) (differentiable_Rmult _)) //.
by rewrite diff_pair // diff_Rmult /= funeqE => ?; rewrite /= [_ * g _]mulrC.
Qed.

Lemma differentiableM (f g : V -> R^o) x :
  differentiable x f -> differentiable x g -> differentiable x (f * g).
Proof.
move=> df dg.
exact: differentiable_comp (differentiable_pair _ _) (differentiable_Rmult _).
Qed.

Let dinv (x : R) :
  x != 0 -> continuous (fun h : R^o => - (1 / x) ^+ 2 *: h) /\
  (fun x => 1 / x : R^o) \o shift x = cst (1 / x) +
  (fun h : R^o => - (1 / x) ^+ 2 *: h) +o_ (0 : R^o) id.
Proof.
move=> xn0; split; first by move=> ?; apply: continuousZ.
apply/eqaddoP => _ /posnumP[e]; near=> h.
  rewrite -[(_ + _ : R -> R) h]/(_ + _) -[(- _ : R -> R) h]/(- _) /=.
  rewrite opprD scaleNr opprK /cst /=.
  rewrite -[- _]mulr1 -[X in - _ * X](mulfVK xn0) mulrA mulNr -expr2 mulNr.
  rewrite [- _ + _]addrC -mulrBr.
  rewrite -[X in X + _]mulr1 -[X in 1 / _ * X](@mulfVK _ (x ^+ 2)); last first.
    by rewrite sqrf_eq0.
  rewrite mulrA mulf_div mulr1.
  rewrite addrC -[X in X * _]mulr1 -{2}[1](@mulfVK _ (h + x)); last by near: h.
  rewrite mulrA expr_div_n expr1n mulf_div mulr1 [_ ^+ 2 * _]mulrC -mulrA.
  rewrite -mulrDr mulrBr [1 / _ * _]mulrC [`|[ _ ]|]absRE normrM.
  rewrite mulrDl mulrDl opprD addrACA addrA [x * _]mulrC expr2.
  do 2 ?[rewrite -addrA [- _ + _]addrC subrr addr0].
  rewrite div1r normfV [X in _ / X]normrM invrM; last 2 first.
      by rewrite unitfE normr_eq0; near: h.
    by rewrite unitfE normr_eq0 mulf_neq0.
  rewrite mulrA mulrAC ler_pdivr_mulr; last by rewrite normr_gt0 mulf_neq0.
  rewrite mulrAC ler_pdivr_mulr; last by rewrite normr_gt0; near: h.
  have : `|h * h| <= `|x / 2| * (e%:num * `|x * x| * `|[h : R^o]|).
    by rewrite !mulrA; near: h.
  move/ler_trans; apply; rewrite [X in X <= _]mulrC; apply: ler_pmul => //.
    by rewrite !mulr_ge0.
  by near: h.
end_near; rewrite /= locally_filterE; apply/locally_normP.
- exists `|x|; first by rewrite normr_gt0.
  move=> h /=; rewrite normmB subr0 -subr_gt0 => lthx.
  rewrite -(normm_gt0 (h + x : R^o)) addrC -[h]opprK.
  apply: ltr_le_trans (ler_distm_dist _ _).
  by rewrite absRE ger0_norm normmN //; apply: ltrW.
- exists (`|x / 2| * e%:num * `|x * x|).
    by rewrite !pmulr_rgt0 // normr_gt0 mulf_neq0.
  by move=> h /ltrW; rewrite normmB subr0 [`|h * _|]normrM => /ler_pmul; apply.
- exists (`|x| / 2); first by apply/divr_gt0 => //; rewrite normr_gt0.
  move=> h /=; rewrite normmB subr0 => lthhx; rewrite addrC -[h]opprK.
  apply: ler_trans (@ler_distm_dist _ [normedModType R of R^o] _ _).
  rewrite absRE normmN [X in _ <= X]ger0_norm; last first.
    rewrite subr_ge0; apply: ltrW; apply: ltr_le_trans lthhx _.
    by rewrite [`|[_]|]splitr ler_addl; apply: divr_ge0.
  rewrite ler_subr_addr -ler_subr_addl (splitr `|[x : R^o]|).
  by rewrite normrM normfV (@ger0_norm _ 2) // -addrA subrr addr0; apply: ltrW.
Qed.

Lemma diff_Rinv (x : R^o) : x != 0 ->
  'd_x (fun y => 1 / y) = (fun h => - (1 / x) ^+ 2 *: h) :> (R^o -> R^o).
Proof.
move=> xn0; have -> : (fun h : R^o => - (1 / x) ^+2 *: h) =
  GRing.scale_linear _ (- (1 / x) ^+2) by [].
by apply: diff_unique; have [] := dinv xn0.
Qed.

Lemma differentiable_Rinv (x : R^o) :
  x != 0 -> differentiable x (fun y => 1 / y).
Proof.
by move=> xn0; apply/diff_locallyP; rewrite diff_Rinv //; apply: dinv.
Qed.

Lemma inv_continuous x : x != 0 -> {for x, continuous (fun y : R^o => 1 / y)}.
Proof.
by move=> xn0; apply: differentiable_continuous (differentiable_Rinv xn0).
Qed.

Lemma lim_inv (T : topologicalType) (F : set (set T)) (FF : Filter F)
  (f : T -> R^o) (a : R^o) :
  a != 0 -> f @ F --> a -> (fun y => 1 / f y) @ F --> 1 / a.
Proof.
move=> an0 fa; apply: (flim_trans _ (inv_continuous an0)).
exact: (@flim_comp _ _ _ f (fun y => 1 / y) _ _ _ fa).
Qed.

Lemma diffV (f : V -> R^o) x : differentiable x f -> f x != 0 ->
  'd_x (fun y => 1 / f y) = - (1 / f x) ^+ 2 \*: 'd_x f :> (V -> R).
Proof.
move=> df fxn0.
by rewrite [LHS](diff_comp df (differentiable_Rinv fxn0)) diff_Rinv.
Qed.

Lemma differentiableV (f : V -> R^o) x :
  differentiable x f -> f x != 0 -> differentiable x (fun y => 1 / f y).
Proof.
by move=> df fxn0; apply: differentiable_comp _ (differentiable_Rinv fxn0).
Qed.

Lemma differentiableX (f : V -> R^o) n x :
  differentiable x f -> differentiable x (f ^+ n).
Proof.
move=> df; elim: n => [|n ihn].
  by rewrite expr0; apply: differentiable_cst.
by rewrite exprS; apply: differentiableM.
Qed.

Lemma exprfunE (T : pointedType) (R : ringType) (f : T -> R) n :
  f ^+ n = (fun x => f x ^+ n).
Proof.
by elim: n => [|n ihn]; rewrite funeqE=> ?; [rewrite !expr0|rewrite !exprS ihn].
Qed.

Lemma diffX (f : V -> R^o) n x :
  differentiable x f ->
  'd_x (f ^+ n.+1) = n.+1%:R * f x ^+ n \*: 'd_x f :> (V -> R).
Proof.
move=> df; elim: n => [|n ihn].
  by rewrite funeqE => ?; rewrite expr1 expr0 mulr1 [RHS]scale1r.
have /(differentiableX n.+1) dfX := df.
rewrite exprSr [LHS]diffM // [X in f x \*: X]ihn funeqE => y.
rewrite -![(_ + _ : V -> R) _]/(_ + _) -![(_ \*: _) _]/(_ *: _).
rewrite scalerA -(scalerDl ('d_x f y)) mulrCA -exprS.
by rewrite -[_ x]mul1r exprfunE -mulrDl -{1}[1]/1%:R -natrD add1n.
Qed.

End DifferentialR3.

(* todo: generalize *)
Lemma eqo_locally' (K : absRingType) (V W : normedModType K) (f g : V -> W) :
  f 0 = 0 -> f = [o_ (locally' (0 : V)) id of g] -> f =o_ (0 : V) id.
Proof.
move=> f0 /eq_some_oP foid; apply/eqoP => _/posnumP[e]; near=> x.
  by case: (eqVneq x 0) => [->|]; [rewrite f0 !normm0 mulr0|move/eqP; near: x].
by end_near; rewrite /= locally_simpl -[locally _ _]/(locally' _ _); case: e.
Qed.

Section Derive.

Variable (V W : normedModType R).

Let der1 (U : normedModType R) (f : R^o -> U) x : derivable f x 1 ->
  f \o shift x = cst (f x) + ( *:%R^~ (derive1 f x)) +o_ (0 : R^o) id.
Proof.
move=> df; apply/eqaddoE; have /derivable_locallyP := df.
have -> : (fun h => (f \o shift x) h%:A) = f \o shift x.
  by rewrite funeqE=> ?; rewrite [_%:A]mulr1.
move=> -> /=; congr (_ + _ + _); first by rewrite derive1E.
rewrite [LHS](eqo_locally' _ (Logic.eq_refl _)) //.
rewrite /the_littleo /insubd; case: (insubP _ _) => //= _ _ ->.
by rewrite -[(_ \- _) _]/(_ - _) opprD scale0r subr0 /funcomp add0r subrr.
Qed.

Lemma deriv1E (U : normedModType R) (f : R^o -> U) x :
  derivable f x 1 -> 'd_x f = ( *:%R^~ (derive1 f x)) :> (R^o -> U).
Proof.
move=> df; have lin_scal : linear (fun h : R^o => h *: derive1 f x).
  by move=> ???; rewrite scalerDl scalerA.
have -> : (fun h : R^o => h *: derive1 f x) = Linear lin_scal by [].
by apply: diff_unique; [apply: scalel_continuous|apply: der1].
Qed.

Lemma diff1E (U : normedModType R) (f : R^o -> U) x :
  differentiable x f -> 'd_x f = (fun h => h *: derive1 f x) :> (R^o -> U).
Proof.
move=> df; have lin_scal : linear (fun h : R^o => h *: 'd_x f 1).
  by move=> ???; rewrite scalerDl scalerA.
have -> : (fun h : R^o => h *: derive1 f x) = Linear lin_scal.
  by rewrite derive1E'.
apply: diff_unique; first exact: scalel_continuous.
apply/eqaddoE; have /diff_locally -> := df; congr (_ + _ + _).
by rewrite funeqE => h /=; rewrite -{1}[h]mulr1 linearZ.
Qed.

Lemma deriv1_diffP (U : normedModType R) (f : R^o -> U) x :
  derivable f x 1 <-> differentiable x f.
Proof.
split=> dfx.
  by apply/diff_locallyP; rewrite deriv1E //; split;
    [apply: scalel_continuous|apply: der1].
apply/derivable_locallyP/eqaddoE.
have -> : (fun h => (f \o shift x) h%:A) = f \o shift x.
  by rewrite funeqE=> ?; rewrite [_%:A]mulr1.
have /diff_locally -> := dfx; congr (_ + _ + _).
  by rewrite diff1E // derive1E.
suff -> : forall h, [o_ (0 : R^o) id of h] =o_ (locally' (0 : R^o)) id by [].
move=> U' h; apply/eqoP => _/posnumP[e].
have : locally (0 : R^o) `<=` locally' (0 : R^o).
  by move=> A /locallyP [d dgt0 Ad]; exists d=> // ? /Ad.
apply; rewrite near_simpl; case: e => /=.
apply: eq_some_oP (Logic.eq_refl [o_ (0 : R^o) id of _]).
Qed.

Lemma derivableP (U : normedModType R) (f : V -> U) x v :
  derivable f x v <-> derivable (fun h : R^o => f (h *: v + x)) 0 1.
Proof.
rewrite /derivable; set g1 := fun h => h^-1 *: _; set g2 := fun h => h^-1 *: _.
suff -> : g1 = g2 by [].
by rewrite funeqE /g1 /g2 => h /=; rewrite addr0 scale0r add0r [_%:A]mulr1.
Qed.

Let der_cst (U : normedModType R) (a : U) (x v : V) :
  (fun h => h^-1 *: ((cst a \o shift x) (h *: v) - cst a x)) @
  locally' (0 : R^o) --> (0 : U).
Proof.
by move=> A /locally_singleton A0; exists 1 => //= ? _ _; rewrite subrr scaler0.
Qed.

Lemma derive_cst (U : normedModType R) (a : U) (x v : V) :
  derive (cst a) x v = 0.
Proof. exact: flim_map_lim (der_cst _ _ _). Qed.

Lemma derivable_cst (U : normedModType R) (a : U) (x v : V) :
  derivable (cst a) x v.
Proof. by apply/cvg_ex; exists 0; apply: der_cst. Qed.

Let der_add (f g : V -> W) (x v : V) : derivable f x v -> derivable g x v ->
  (fun h => h^-1 *: (((f + g) \o shift x) (h *: v) - (f + g) x)) @
  locally' (0 : R^o) --> derive f x v + derive g x v.
Proof.
move=> df dg.
evar (fg : R -> W); rewrite [X in X @ _](_ : _ = fg) /=; last first.
  rewrite funeqE => h.
  by rewrite !scalerDr scalerN scalerDr opprD addrACA -!scalerBr /fg.
exact: lim_add.
Qed.

Lemma deriveD (f g : V -> W) (x v : V) : derivable f x v -> derivable g x v ->
  derive (f + g) x v = derive f x v + derive g x v.
Proof. by move=> df dg; apply: flim_map_lim (der_add df dg). Qed.

Lemma derivableD (f g : V -> W) (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f + g) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (derive f x v + derive g x v).
exact: der_add.
Qed.

Lemma derivable_sum n (f : 'I_n -> V -> W) (x v : V) :
  (forall i, derivable (f i) x v) -> derivable (\sum_(i < n) f i) x v.
Proof.
elim: n f => [f _|n IH f H].
  rewrite big_ord0 (_ : 0 = cst 0) //; exact: derivable_cst.
rewrite big_ord_recr /=; exact: derivableD (IH _ _) (H _).
Qed.

Lemma derive_sum n (f : 'I_n -> V -> W) (x v : V) :
  (forall i, derivable (f i) x v) ->
  derive (\sum_(i < n) f i) x v = \sum_(i < n) derive (f i) x v.
Proof.
elim: n f => [f _|n IH f H].
  by rewrite 2!big_ord0 (_ : 0 = cst 0) // derive_cst.
rewrite big_ord_recr deriveD // ?IH // ?big_ord_recr //; exact: derivable_sum.
Qed.

Let der_opp (f : V -> W) (x v : V) : derivable f x v ->
  (fun h => h^-1 *: (((- f) \o shift x) (h *: v) - (- f) x)) @
  locally' (0 : R^o) --> - derive f x v.
Proof.
move=> df; evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  by rewrite funeqE => h; rewrite !scalerDr !scalerN -opprD -scalerBr /g.
exact: lim_opp.
Qed.

Lemma deriveN (f : V -> W) (x v : V) : derivable f x v ->
  derive (- f) x v = - derive f x v.
Proof. by move=> df; apply: flim_map_lim (der_opp df). Qed.

Lemma derivableN (f : V -> W) (x v : V) :
  derivable f x v -> derivable (- f) x v.
Proof. by move=> df; apply/cvg_ex; exists (- derive f x v); apply: der_opp. Qed.

Lemma deriveB (f g : V -> W) (x v : V) : derivable f x v -> derivable g x v ->
  derive (f - g) x v = derive f x v - derive g x v.
Proof. by move=> df dg; rewrite deriveD ?deriveN //; apply: derivableN. Qed.

Lemma derivableB (f g : V -> W) (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f - g) x v.
Proof. by move=> df dg; apply: derivableD (derivableN _). Qed.

Let der_scal (f : V -> W) (k : R) (x v : V) : derivable f x v ->
  (fun h => h^-1 *: ((k \*: f \o shift x) (h *: v) - (k \*: f) x)) @
  locally' (0 : R^o) --> k *: derive f x v.
Proof.
move=> df; evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  rewrite funeqE => h.
  by rewrite scalerBr !scalerA mulrC -!scalerA -!scalerBr /g.
exact: lim_scaler.
Qed.

Lemma deriveZ (f : V -> W) (k : R) (x v : V) : derivable f x v ->
  derive (k \*: f) x v = k *: derive f x v.
Proof. by move=> df; apply: flim_map_lim (der_scal df). Qed.

Lemma derivableZ (f : V -> W) (k : R) (x v : V) :
  derivable f x v -> derivable (k \*: f) x v.
Proof.
by move=> df; apply/cvg_ex; exists (k *: derive f x v); apply: der_scal.
Qed.

Let der_mult (f g : V -> R^o) (x v : V) :
  derivable f x v -> derivable g x v ->
  (fun h => h^-1 *: (((f * g) \o shift x) (h *: v) - (f * g) x)) @
  locally' (0 : R^o) --> f x *: derive g x v + g x *: derive f x v.
Proof.
move=> df dg.
evar (fg : R -> R); rewrite [X in X @ _](_ : _ = fg) /=; last first.
  rewrite funeqE => h.
  have -> : (f * g) (h *: v + x) - (f * g) x =
    f (h *: v + x) *: (g (h *: v + x) - g x) + g x *: (f (h *: v + x) - f x).
    by rewrite !scalerBr -addrA ![g x *: _]mulrC addKr.
  rewrite scalerDr scalerA mulrC -scalerA.
  by rewrite [_ *: (g x *: _)]scalerA mulrC -scalerA /fg.
apply: lim_add; last exact: lim_scaler df.
apply: flim_comp2 (@lim_mult _ _ _) => /=; last exact: dg.
suff : {for 0, continuous (fun h => f(h *: v + x))}.
  by move=> /continuous_withinNx; rewrite scale0r add0r.
exact/(@differentiable_continuous _ _ (0 : R^o))/deriv1_diffP/derivableP.
Qed.

Lemma deriveM (f g : V -> R^o) (x v : V) :
  derivable f x v -> derivable g x v ->
  derive (f * g) x v = f x *: derive g x v + g x *: derive f x v.
Proof. by move=> df dg; apply: flim_map_lim (der_mult df dg). Qed.

Lemma derivableM (f g : V -> R^o) (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f * g) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (f x *: derive g x v + g x *: derive f x v).
exact: der_mult.
Qed.

Lemma derivableX (f : V -> R^o) n (x v : V) :
  derivable f x v -> derivable (f ^+ n) x v.
Proof.
move=> df; elim: n => [|n ihn].
  by rewrite expr0; apply: derivable_cst.
by rewrite exprS; apply: derivableM.
Qed.

Lemma deriveX (f : V -> R^o) n (x v : V) :
  derivable f x v ->
  derive (f ^+ n.+1) x v = (n.+1%:R * f x ^+ n) *: derive f x v.
Proof.
move=> df; elim: n => [|n ihn]; first by rewrite expr0 mulr1 scale1r expr1.
rewrite exprS (deriveM df (@derivableX _ _ _ _ df)) ihn.
rewrite scalerA -scalerDl mulrCA -[f x * _]exprS.
rewrite -[X in _ + X]mul1r [X in 1 * (X _)]exprfunE -mulrDl.
by rewrite -{2}[1]/1%:R -natrD addn1.
Qed.

Let der_inv (f : V -> R^o) (x v : V) :
  f x != 0 -> derivable f x v ->
  (fun h => h^-1 *: (((fun y => 1 / f y) \o shift x) (h *: v) - 1 / f x)) @
  locally' (0 : R^o) --> - (1 / f x) ^+2 *: derive f x v.
Proof.
move=> fxn0 df.
have /derivableP/deriv1_diffP/differentiable_continuous := df.
move=> /continuous_withinNx; rewrite scale0r add0r => fc.
have fn0 : locally' (0 : R^o) [set h | f (h *: v + x) != 0].
  apply: (fc [set x | x != 0]); exists `|[f x]|; first by rewrite normm_gt0.
  move=> y; rewrite /AbsRing_ball /= => yltfx.
  by apply/eqP => y0; move: yltfx; rewrite y0 subr0 ltrr.
have : (fun h => - ((1 / f x) * (1 / f (h *: v + x))) *:
  (h^-1 *: (f (h *: v + x) - f x))) @ locally' (0 : R^o) -->
  - (1 / f x) ^+2 *: derive f x v.
  apply: flim_comp2 (@lim_mult _ _ _) => //=.
  apply: (@lim_opp _ [normedModType R of R^o]); rewrite expr2.
  exact/lim_scaler/lim_inv.
apply: flim_trans => A [_/posnumP[e] /= Ae].
move: fn0; rewrite !near_simpl; apply: filter_app; near=> h.
  move=> fhvxn0; have he : AbsRing_ball 0 e%:num h by near: h.
  have hn0 : h <> 0 by near: h.
  suff <- :
    - ((1 / f x) * (1 / f (h *: v + x))) *: (h^-1 *: (f (h *: v + x) - f x)) =
    h^-1 *: (1 / f (h *: v + x) - 1 / f x).
    exact: Ae.
  rewrite scalerA mulrC -scalerA; congr (_ *: _).
  apply/eqP; rewrite scaleNr eqr_oppLR opprB !div1r scalerBr.
  rewrite -scalerA [_ *: f _]mulVf // [_%:A]mulr1.
   by rewrite mulrC -scalerA [_ *: f _]mulVf // [_%:A]mulr1.
by end_near; exists e%:num.
Qed.

Lemma deriveV (f : V -> R^o) x v : f x != 0 -> derivable f x v ->
  derive (fun y => 1 / f y) x v = - (1 / f x) ^+2 *: derive f x v.
Proof. by move=> fxn0 df; apply: flim_map_lim (der_inv fxn0 df). Qed.

Lemma derivableV (f : V -> R^o) (x v : V) :
  f x != 0 -> derivable f x v -> derivable (fun y => 1 / f y) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (- (1 / f x) ^+2 *: derive f x v).
exact: der_inv.
Qed.

End Derive.

Lemma EVT_max (f : R -> R) (a b : R) :
  let l := minr a b in let r := maxr a b in
  {in `[l, r], continuous f} -> exists2 c, c \in `[l, r] &
  forall t, t \in `[l, r] -> f t <= f c.
Proof.
move=> l r fcont; set imf := [pred t | t \in f @` [set x | x \in `[l, r]]].
have imf_sup : has_sup imf.
  apply/has_supP; split.
    exists (f l); rewrite !inE; apply/asboolP/imageP.
    by rewrite inE lerr ler_maxr ler_minl lerr.
  have [M imfltM] : bounded (f @` [set x | x \in `[l, r]] : set R^o).
    apply/compact_bounded/continuous_compact; last exact: segment_compact.
    by move=> ?; rewrite inE => /asboolP /fcont.
  exists (M + 1); apply/ubP => y; rewrite !inE => /asboolP /imfltM yltM.
  apply/ltrW; apply: ler_lt_trans (yltM _ _); last by rewrite ltr_addl.
  by rewrite [ `|[_]| ]absRE ler_norm.
case: (pselect (exists2 c, c \in `[l, r] & f c = sup imf)) => [|imf_ltsup].
  move=> [c clr fceqsup]; exists c => // t tlr.
  rewrite fceqsup; apply: sup_upper_bound=> //; rewrite !inE; apply/asboolP.
  exact: imageP.
have {imf_ltsup} imf_ltsup : forall t, t \in `[l, r] -> f t < sup imf.
  move=> t tlr; case: (ltrP (f t) (sup imf))=> // supleft.
  rewrite falseE; apply: imf_ltsup; exists t => //.
  apply/eqP; rewrite eqr_le supleft sup_upper_bound => //.
  by rewrite !inE; apply/asboolP/imageP.
have invf_cont : {in `[l, r], continuous (fun t => 1 / (sup imf - f t))}.
  move=> t tlr; apply: lim_inv.
    by rewrite neqr_lt subr_gt0 orbC imf_ltsup.
  by apply: lim_add; [apply: continuous_cst|apply/lim_opp/fcont].
have [M imVfltM] : bounded ((fun t => 1 / (sup imf - f t)) @`
  [set x | x \in `[l, r]] : set R^o).
  apply/compact_bounded/continuous_compact; last exact: segment_compact.
  by move=> ?; rewrite inE => /asboolP /invf_cont.
set k := maxr (M + 1) 1; have kgt0 : 0 < k by rewrite ltr_maxr ltr01 orbC.
have : exists2 y, y \in imf & sup imf - k^-1 < y.
  by apply: sup_adherent => //; rewrite invr_gt0.
move=> [y]; rewrite !inE => /asboolP [t tlr <-] {y}.
rewrite ltr_subl_addr - ltr_subl_addl.
suff : sup imf - f t > k^-1 by move=> /ltrW; rewrite lerNgt => /negbTE ->.
rewrite -[X in _ < X]invrK ltr_pinv.
    rewrite -div1r; apply: ler_lt_trans (ler_norm _) _; rewrite -absRE.
    by apply: imVfltM; [rewrite ltr_maxr ltr_addl ltr01|apply: imageP].
  by rewrite inE kgt0 unitfE lt0r_neq0.
have invsupft_gt0 : 0 < (sup imf - f t)^-1.
  by rewrite invr_gt0 subr_gt0 imf_ltsup.
by rewrite inE invsupft_gt0 unitfE lt0r_neq0.
Qed.

Lemma EVT_min (f : R -> R) (a b : R) :
  let l := minr a b in let r := maxr a b in
  {in `[l, r], continuous f} -> exists2 c, c \in `[l, r] &
  forall t, t \in `[l, r] -> f c <= f t.
Proof.
move=> l r fcont.
have /EVT_max [c clr fcmax] : {in `[l, r], continuous (- f)}.
  by move=> ? /fcont; apply: (@continuousN _ [normedModType R of R^o]).
by exists c => // ? /fcmax; rewrite ler_opp2.
Qed.

Lemma cvg_at_rightE (V : normedModType R) (f : R -> V) x :
  cvg (f @ locally' x) -> lim (f @ locally' x) = lim (f @ at_right x).
Proof.
move=> cvfx; apply/Logic.eq_sym.
(* should be inferred *)
have atrF := at_right_proper_filter x.
apply: flim_map_lim => A /cvfx /locallyP [_ /posnumP[e] xe_A].
exists e%:num => // y xe_y; rewrite ltr_def => /andP [/eqP xney _].
exact: xe_A.
Qed.

Lemma cvg_at_leftE (V : normedModType R) (f : R -> V) x :
  cvg (f @ locally' x) -> lim (f @ locally' x) = lim (f @ at_left x).
Proof.
move=> cvfx; apply/Logic.eq_sym.
(* should be inferred *)
have atrF := at_left_proper_filter x.
apply: flim_map_lim => A /cvfx /locallyP [_ /posnumP[e] xe_A].
exists e%:num => // y xe_y; rewrite ltr_def => /andP [/eqP xney _].
by apply: xe_A => // /eqP; rewrite eq_sym => /eqP.
Qed.

Lemma le0r_flim_map (T : topologicalType) (F : set (set T))
  (FF : ProperFilter F) (f : T -> R^o) :
  (\forall x \near F, 0 <= f x) -> cvg (f @ F) -> 0 <= lim (f @ F).
Proof.
move=> fge0 fcv; case: (lerP 0 (lim (f @ F))) => // limlt0.
near F have x.
  have : 0 <= f x by near: x.
  rewrite lerNgt => /negbTE<-; near: x.
end_near.
have normlimgt0 : `|[lim (f @ F)]| > 0 by rewrite normm_gt0 ltr0_neq0.
have /fcv := locally_ball_norm (lim (f @ F)) (PosNum normlimgt0).
rewrite /= !near_simpl; apply: filter_app; near=> x.
  rewrite /= normmB [ `|[_]| ]absRE => /(ler_lt_trans (ler_norm _)).
  rewrite ltr_subl_addr => /ltr_le_trans; apply.
  by rewrite [ `|[_]| ]absRE ltr0_norm // addrC subrr.
by end_near.
Qed.

Lemma ler0_flim_map (T : topologicalType) (F : set (set T))
  (FF : ProperFilter F) (f : T -> R^o) :
  (\forall x \near F, f x <= 0) -> cvg (f @ F) -> lim (f @ F) <= 0.
Proof.
move=> fle0 fcv; rewrite -oppr_ge0.
have limopp : - lim (f @ F) = lim (- f @ F).
  exact/Logic.eq_sym/flim_map_lim/lim_opp.
rewrite limopp; apply: le0r_flim_map; last by rewrite -limopp; apply: lim_opp.
by move: fle0; apply: filter_app; near=> x; [rewrite oppr_ge0|end_near].
Qed.

Lemma ler_flim_map (T : topologicalType) (F : set (set T)) (FF : ProperFilter F)
  (f g : T -> R^o) :
  (\forall x \near F, f x <= g x) -> cvg (f @ F) -> cvg (g @ F) ->
  lim (f @ F) <= lim (g @ F).
Proof.
move=> lefg fcv gcv; rewrite -subr_ge0.
have eqlim : lim (g @ F) - lim (f @ F) = lim ((g - f) @ F).
  by apply/Logic.eq_sym/flim_map_lim/lim_add => //; apply: lim_opp.
rewrite eqlim; apply: le0r_flim_map; last first.
  by rewrite /(cvg _) -eqlim /=; apply: lim_add => //; apply: lim_opp.
by move: lefg; apply: filter_app; near=> x; [rewrite subr_ge0|end_near].
Qed.

Lemma derive1_at_max (f : R^o -> R^o) (a b c : R) :
  let l := minr a b in let r := maxr a b in
  (forall t, t \in `]l, r[ -> derivable f t 1) -> c \in `]l, r[ ->
  (forall t, t \in `]l, r[ -> f t <= f c) -> derive1 f c = 0.
Proof.
move=> l r fdrvbl clr cmax.
apply/eqP; rewrite eqr_le; apply/andP; split.
  rewrite derive1E [derive _ _ _]cvg_at_rightE; last exact: fdrvbl.
  apply: ler0_flim_map; last first.
    have /fdrvbl dfc := clr; rewrite -cvg_at_rightE //.
    apply: flim_trans dfc; apply: flim_app.
    move=> A [e egt0 Ae]; exists e => // x xe xgt0; apply: Ae => //.
    exact/eqP/lt0r_neq0.
  near=> h.
    apply: mulr_ge0_le0; first by rewrite invr_ge0; apply: ltrW; near: h.
    by rewrite subr_le0 [_%:A]mulr1; apply: cmax; near: h.
  end_near; first by exists 1.
  exists (r - c); first by rewrite subr_gt0 (itvP clr).
  move=> h; rewrite /AbsRing_ball /= absrB subr0 absRE.
  move=> /(ler_lt_trans (ler_norm _)); rewrite ltr_subr_addr inE => ->.
  by move=> /ltr_spsaddl -> //; rewrite (itvP clr).
rewrite derive1E [derive _ _ _]cvg_at_leftE; last exact: fdrvbl.
apply: le0r_flim_map; last first.
  have /fdrvbl dfc := clr; rewrite -cvg_at_leftE //.
  apply: flim_trans dfc; apply: flim_app.
  move=> A [e egt0 Ae]; exists e => // x xe xgt0; apply: Ae => //.
  exact/eqP/ltr0_neq0.
near=> h.
  apply: mulr_le0; first by rewrite invr_le0; apply: ltrW; near: h.
  by rewrite subr_le0 [_%:A]mulr1; apply: cmax; near: h.
end_near; first by exists 1.
exists (c - l); first by rewrite subr_gt0 (itvP clr).
move=> h; rewrite /AbsRing_ball /= absrB subr0 absRE.
move=> /ltr_normlP []; rewrite ltr_subr_addl ltr_subl_addl inE => -> _.
by move=> /ltr_snsaddl -> //; rewrite (itvP clr).
Qed.

Lemma derive1_at_min (f : R^o -> R^o) (a b c : R) :
  let l := minr a b in let r := maxr a b in
  (forall t, t \in `]l, r[ -> derivable f t 1) -> c \in `]l, r[ ->
  (forall t, t \in `]l, r[ -> f c <= f t) -> derive1 f c = 0.
Proof.
move=> l r fdrvbl clr cmin; apply/eqP; rewrite -oppr_eq0; apply/eqP.
rewrite derive1E -deriveN; last exact: fdrvbl.
rewrite -derive1E; apply: derive1_at_max (clr) _ => t tlr.
  exact/derivableN/fdrvbl.
by rewrite ler_opp2; apply: cmin.
Qed.

Lemma Rolle (f : R^o -> R^o) (a b : R) :
  b - a != 0 ->
  let l := minr a b in let r := maxr a b in
  (forall x, x \in `]l, r[ -> derivable f x 1) -> {in `[l, r], continuous f} ->
  f a = f b -> exists2 c, c \in `]l, r[ & derive1 f c = 0.
Proof.
move=> bnea l r fdrvbl fcont faefb.
have [cmax cmaxlr fcmax] := EVT_max fcont.
case: (pselect ([set l; r] cmax))=> [cmaxelVr|]; last first.
  move=> /asboolPn; rewrite asbool_or => /norP.
  move=> [/asboolPn/eqP cnel /asboolPn/eqP cner].
  have {cmaxlr} cmaxlr : cmax \in `]l, r[.
    by rewrite inE !ltr_def !(itvP cmaxlr) cnel eq_sym cner.
  exists cmax => //; apply: derive1_at_max fdrvbl cmaxlr _ => t tlr.
  by apply: fcmax; rewrite inE !ltrW // (itvP tlr).
have [cmin cminlr fcmin] := EVT_min fcont.
case: (pselect ([set l; r] cmin))=> [cminelVr|]; last first.
  move=> /asboolPn; rewrite asbool_or => /norP.
  move=> [/asboolPn/eqP cnel /asboolPn/eqP cner].
  have {cminlr} cminlr : cmin \in `]l, r[.
    by rewrite inE !ltr_def !(itvP cminlr) cnel eq_sym cner.
  exists cmin => //; apply: derive1_at_min fdrvbl cminlr _ => t tlr.
  by apply: fcmin; rewrite inE !ltrW // (itvP tlr).
have midlr : (l + r) / 2 \in `]l, r[.
  apply: mid_in_itvoo; rewrite ltr_maxr.
  case: (ltrP b a); first by rewrite ltr_minl -orbA orbCA => ->.
  by rewrite orbC ltr_minl ltr_def -subr_eq0 bnea => ->.
exists ((l + r) / 2) => //; apply: derive1_at_max fdrvbl (midlr) _ => t tlr.
suff fcst : forall s, s \in `]l, r[ -> f s = f cmax by rewrite !fcst.
move=> s slr.
apply/eqP; rewrite eqr_le fcmax; last by rewrite inE !ltrW ?(itvP slr).
suff -> : f cmax = f cmin by rewrite fcmin // inE !ltrW ?(itvP slr).
suff flefr : f l = f r by case: cmaxelVr => ->; case: cminelVr => ->.
by case: (lerP a b) => [leab|/ltrW leba]; rewrite /l /r;
  [rewrite maxr_r // minr_l|rewrite maxr_l // minr_r].
Qed.

Lemma MVT (f : R^o -> R^o) (a b : R) :
  let l := minr a b in let r := maxr a b in
  (forall x, x \in `]l, r[ -> derivable f x 1) -> {in `[l, r], continuous f} ->
  exists2 c, c \in `[l, r] & f b - f a = derive1 f c * (b - a).
Proof.
move=> l r fdrvbl fcont.
case: (eqVneq (b - a) 0) => [|bnea].
  move/eqP; rewrite subr_eq0 => /eqP bea.
  exists a; last by rewrite bea !subrr mulr0.
  by rewrite inE ler_minl ler_maxr bea lerr.
set g := f + (- ( *:%R^~ ((f b - f a) / (b - a)) : R -> R)).
have gdrvbl : forall x, x \in `]l, r[ -> derivable g x 1.
  move=> x /fdrvbl dfx; apply: derivableB dfx _; apply/deriv1_diffP.
  exact: scalel_differentiable.
have gcont : {in `[l, r], continuous g}.
  move=> x /fcont fx; apply: continuousD fx _; apply: continuousN.
  exact: scalel_continuous.
have gaegb : g a = g b.
  rewrite /g -![(_ - _ : _ -> _) _]/(_ - _).
  apply/eqP; rewrite -subr_eq /= opprK addrAC -addrA -scalerBl.
  by rewrite [_ *: _]mulrA mulrC mulrA mulVf // mul1r addrCA subrr addr0.
have [c clr dgc0] := Rolle bnea gdrvbl gcont gaegb.
exists c; first by apply/andP; split; apply/ltrW; rewrite (itvP clr).
move: dgc0; rewrite derive1E deriveB; last 2 first; first exact: fdrvbl.
  exact/deriv1_diffP/scalel_differentiable.
move/eqP; rewrite [X in _ - X]deriveE; last exact/scalel_differentiable.
rewrite diff_scalel scale1r subr_eq0 derive1E => /eqP->.
by rewrite -mulrA mulVf // mulr1.
Qed.

Lemma ler0_derive1_nincr (f : R^o -> R^o) (a b : R) :
  (forall x, x \in `[a, b] -> derivable f x 1) ->
  (forall x, x \in `[a, b] -> derive1 f x <= 0) ->
  forall x y, a <= x -> x <= y -> y <= b -> f y <= f x.
Proof.
move=> fdrvbl dfle0 x y leax lexy leyb; rewrite -subr_ge0.
have itvW : {subset `[minr y x, maxr y x] <= `[a, b]}.
  apply/subitvP; rewrite /= ler_minr ler_maxl leyb /= -andbA andbCA leax /=.
  by apply/andP; split; [apply: ler_trans lexy|apply: ler_trans leyb].
have [] := @MVT f y x.
    by move=> z zxy; apply/fdrvbl/itvW; apply: subitvP zxy; rewrite /= !lerr.
  by move=> ? /itvW /fdrvbl /deriv1_diffP /differentiable_continuous.
by move=> ? /itvW /dfle0 ? ->; apply: mulr_le0 => //; rewrite subr_le0.
Qed.

Lemma le0r_derive1_ndecr (f : R^o -> R^o) (a b : R) :
  (forall x, x \in `[a, b] -> derivable f x 1) ->
  (forall x, x \in `[a, b] -> 0 <= derive1 f x) ->
  forall x y, a <= x -> x <= y -> y <= b -> f x <= f y.
Proof.
move=> fdrvbl dfge0 x y; rewrite -[f _ <= _]ler_opp2.
apply: (@ler0_derive1_nincr (- f)) => t tab; first exact/derivableN/fdrvbl.
rewrite derive1E deriveN; last exact: fdrvbl.
by rewrite oppr_le0 -derive1E; apply: dfge0.
Qed.