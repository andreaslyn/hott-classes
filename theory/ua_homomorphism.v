Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.implementations.ua_carrier_product
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.HSet
  HoTT.Types.Universe
  HoTT.Basics.PathGroupoids
  HoTT.Tactics
  HoTT.Types.Record.

Import algebra_notations.

Section ishomomorphism.
  Context {σ : Signature} {A B : Algebra σ} (f : ∀ s, A s → B s).

  Fixpoint OpPreserving {n : symboltype σ}
    : Operation A n → Operation B n → Type
    := match n with
       | [:s] => λ ao bo, f s ao = bo
       | s ::: y => λ ao bo, ∀ (x : A s), OpPreserving (ao x) (bo (f s x))
       end.

  Global Instance hprop_oppreserving `{Funext} {n : symboltype σ}
    (a : Operation A n) (b : Operation B n)
    : IsHProp (OpPreserving a b).
  Proof.
    intros. induction n; apply _.
  Defined.

  Class IsHomomorphism : Type :=
    op_preserving : ∀ (u : symbol σ), OpPreserving (u^^A) (u^^B).

  Global Instance hprop_ishomomorphism `{Funext} : IsHProp IsHomomorphism.
  Proof.
    intros. apply trunc_forall.
  Defined.

  Class IsIsomorphism `{!IsHomomorphism} : Type :=
    { injection_isomorphism : ∀ (s : sort σ), Injective (f s)
    ; surjection_isomorphism : ∀ (s : sort σ), IsSurjection (f s) }.

  Global Existing Instance injection_isomorphism.
  Global Existing Instance surjection_isomorphism.
End ishomomorphism.

Record Homomorphism {σ} {A B : Algebra σ} : Type := BuildHomomorphism
  { hom_def : ∀ s, A s → B s
  ; ishomomorphism_hom : IsHomomorphism hom_def }.

Arguments Homomorphism {σ} A B.
Arguments BuildHomomorphism {σ A B} hom_def {ishomomorphism_hom}.

Global Coercion hom_def : Homomorphism >-> Funclass.

Global Existing Instance ishomomorphism_hom.

Definition SigHomomorphism {σ} (A B : Algebra σ) : Type :=
  {hom_def : ∀ s, A s → B s | IsHomomorphism hom_def}.

Lemma issig_homomorphism {σ} (A B : Algebra σ)
  : Homomorphism A B <~> SigHomomorphism A B.
Proof.
  apply symmetric_equiv.
  unfold SigHomomorphism.
  issig (@BuildHomomorphism σ A B) (@hom_def σ A B) (@ishomomorphism_hom σ A B).
Defined.

Section homomorphism_cprod.
  Context {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B).

  Lemma path_homomorphism_apply_cprod' {w : symboltype σ}
    (a : CProd A (dom_symboltype w)) (ao : Operation A w) (bo : Operation B w)
    (P : OpPreserving f ao bo)
    : f (cod_symboltype w) (apply_cprod ao a) = apply_cprod bo (map_cprod f a).
  Proof.
    induction w.
    - assumption.
    - destruct a as [x a]. apply IHw. apply P.
  Defined.

  Lemma path_homomorphism_apply_cprod
    : ∀ (u : symbol σ) (a : CProd A (dom_symboltype (σ u))),
      f (cod_symboltype (σ u)) (apply_cprod (u^^A) a) =
       apply_cprod (u^^B) (map_cprod f a).
  Proof.
    intros u a.
    apply path_homomorphism_apply_cprod'.
    apply f.
  Defined.
End homomorphism_cprod.

Global Instance embedding_isomorphism {σ} {A B : Algebra σ}
    (f : Homomorphism A B) {Is : IsIsomorphism f}
  : ∀ s, IsEmbedding (f s).
Proof.
  intro s. apply isembedding_isinj_hset. apply Is.
Defined.

Global Instance isequiv_forgetful_iso {σ} {A B : Algebra σ}
  (f : Homomorphism A B) {Is : IsIsomorphism f}
  : ∀ s, IsEquiv (f s).
Proof.
  intro s. apply isequiv_surj_emb; exact _.
Defined.

Definition equiv_forgetful_iso {σ} {A B : Algebra σ}
    (f : Homomorphism A B) {Is : IsIsomorphism f}
    : ∀ s, A s <~> B s.
Proof.
  intro s. rapply (BuildEquiv _ _ (f s)).
Defined.

Global Instance ishomomorphism_id {σ} (A : Algebra σ)
  : @IsHomomorphism σ A A (λ _, idmap).
Proof.
 intro u. generalize (u^^A). intro w. induction (σ u).
 - reflexivity.
 - now intro x.
Qed.

Global Instance isisomorphism_id {σ} (A : Algebra σ)
  : @IsIsomorphism σ A A (λ _, idmap) (ishomomorphism_id A).
Proof.
  constructor; intro s.
  - intros x y. exact idmap.
  - apply BuildIsSurjection. intro y. exact (tr (y; idpath)).
Qed.

Definition hom_id {σ} {A : Algebra σ} : Homomorphism A A
  := BuildHomomorphism (λ _, idmap).

Global Instance ishomomorphism_inv {σ} (A B : Algebra σ)
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : IsHomomorphism (λ s, (f s)^-1).
Proof.
 intro u.
 generalize (u^^A) (u^^B) (op_preserving f u).
 intros a b P.
 induction (σ u).
 - rewrite <- P. apply (eissect (f t)).
 - intro. apply IHn.
   exact (
    transport (λ y, OpPreserving f _ (b y)) (eisretr (f t) x) (P (_^-1 x))).
Qed.

Global Instance isisomorphism_inv {σ} (A B : Algebra σ)
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : IsIsomorphism (λ s, (f s)^-1).
Proof.
  constructor.
  - intros s x y p.
    now rewrite <- (eisretr (f s) x), <- (eisretr (f s) y), p.
  - intro s.
    apply BuildIsSurjection.
    intro y.
    apply tr.
    exists (f s y).
    apply (eissect (f s) y).
Qed.

Definition hom_inv {σ} {A B : Algebra σ} (f : Homomorphism A B)
    `{!IsIsomorphism f}
    : Homomorphism B A
  := BuildHomomorphism (λ s, (f s)^-1).

Lemma oppreserving_compose {σ} {A B C : Algebra σ} {w : symboltype σ}
  {a : Operation A w} {b : Operation B w} {c : Operation C w}
  (g : Homomorphism B C) (f : Homomorphism A B)
  (G : OpPreserving g b c) (F : OpPreserving f a b)
  : OpPreserving (λ s (x : A s), g s (f s x)) a c.
Proof.
 induction w; simpl.
 - now rewrite F, G.
 - intro x. now apply (IHw _ (b (f _ x))).
Qed.

Global Instance ishomomorphism_compose {σ} {A B C : Algebra σ}
  (g : Homomorphism B C) (f : Homomorphism A B)
  : IsHomomorphism (λ s, g s ∘ f s).
Proof.
 intro u.
 exact (oppreserving_compose g f (op_preserving g u) (op_preserving f u)).
Qed.

Definition hom_compose {σ} {A B C : Algebra σ}
    (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
  := BuildHomomorphism (λ s, g s ∘ f s).

Global Instance isisomorphism_compose {σ} {A B C : Algebra σ}
  (g : Homomorphism B C) `{!IsIsomorphism g}
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : IsIsomorphism (λ s, g s ∘ f s).
Proof.
 constructor.
 - intros s x y p.
   apply (injection_isomorphism f).
   by apply (injection_isomorphism g).
 - intro s.
   apply BuildIsSurjection.
   intro z.
   apply tr.
   exists ((f s)^-1 ((g s)^-1 z)).
   unfold Compose.
   by rewrite (eisretr (f s)), (eisretr (g s)).
Qed.

Definition path_equiv_carriers `{Univalence} {σ} {A B : Algebra σ}
  (f : ∀ (s : sort σ), A s <~> B s)
  : carriers A = carriers B
  := path_forall A B (λ s : sort σ, path_universe (f s)).

Lemma path_transport_carriers_equiv `{Univalence} {σ} {A B : Algebra σ}
  {w : symboltype σ} (f : ∀ (s : sort σ), A s <~> B s)
  (ao : Operation A w) (bo : Operation B w) (P : OpPreserving f ao bo)
  : transport (λ s : Carriers σ, Operation s w)
      (path_equiv_carriers f) ao = bo.
Proof.
  unfold path_equiv_carriers.
  induction w; simpl in *.
  - transport_path_forall_hammer.
    rewrite <- P.
    by rewrite transport_idmap_path_universe.
  - funext y.
    specialize (P ((f t)^-1 y)).
    rewrite (eisretr (f t)) in P.
    transport_path_forall_hammer.
    rewrite transport_forall_constant.
    rewrite transport_forall.
    rewrite transport_const.
    rewrite (transport_path_universe_V (f t)).
    destruct (path_universe (f t)).
    exact (IHw (ao ((f t)^-1 y)) (bo y) P).
Qed.

Lemma path_transport_carriers_isomorphism `{Univalence} {σ} {A B : Algebra σ}
  (f : Homomorphism A B) `{!IsIsomorphism f} (u : symbol σ)
  : transport (λ s : Carriers σ, Operation s (σ u))
      (path_equiv_carriers (equiv_forgetful_iso f)) (u^^A) = u^^B.
Proof.
  apply path_transport_carriers_equiv. apply (op_preserving f).
Defined.

Theorem path_isomorphism `{Univalence} {σ} {A B : Algebra σ}
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : A = B.
Proof.
  apply path_algebra.
  exists (path_equiv_carriers (equiv_forgetful_iso f)).
  funext u.
  refine (transport (λ x : Operation B (σ u), x = u^^B)
            (transport_forall_constant _ _ u)^
            (path_transport_carriers_isomorphism f u)).
Defined.
