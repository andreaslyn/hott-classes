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
  HoTT.Types.Record
  HoTT.Types.Sigma.

Import algebra_notations.

Section is_homomorphism.
  Context {σ : Signature} {A B : Algebra σ} (f : ∀ s, A s → B s).

  Fixpoint OpPreserving {w : SymbolType σ}
    : Operation A w → Operation B w → Type
    := match w with
       | [:s] => λ ao bo, f s ao = bo
       | s ::: y => λ ao bo, ∀ (x : A s), OpPreserving (ao x) (bo (f s x))
       end.

  Global Instance hprop_oppreserving `{Funext} {w : SymbolType σ}
    (a : Operation A w) (b : Operation B w)
    : IsHProp (OpPreserving a b).
  Proof.
    intros. induction w; exact _.
  Defined.

  Class IsHomomorphism : Type :=
    op_preserving : ∀ (u : Symbol σ), OpPreserving (u^^A) (u^^B).

  Global Instance hprop_is_homomorphism `{Funext} : IsHProp IsHomomorphism.
  Proof.
    intros. apply trunc_forall.
  Defined.
End is_homomorphism.

Record Homomorphism {σ} {A B : Algebra σ} : Type := BuildHomomorphism
  { def_hom : ∀ s, A s → B s
  ; is_homomorphism_hom : IsHomomorphism def_hom }.

Arguments Homomorphism {σ} A B.
Arguments BuildHomomorphism {σ A B} def_hom {is_homomorphism_hom}.

Global Coercion def_hom : Homomorphism >-> Funclass.

Global Existing Instance is_homomorphism_hom.

Definition SigHomomorphism {σ} (A B : Algebra σ) : Type :=
  {def_hom : ∀ s, A s → B s | IsHomomorphism def_hom}.

Lemma issig_homomorphism {σ} (A B : Algebra σ)
  : Homomorphism A B <~> SigHomomorphism A B.
Proof.
  apply symmetric_equiv.
  unfold SigHomomorphism.
  issig (@BuildHomomorphism σ A B) (@def_hom σ A B)
    (@is_homomorphism_hom σ A B).
Defined.

Ltac change_issig_homomorphism f :=
  match type of f with
  | @Homomorphism ?σ ?A ?B =>
      change (@is_homomorphism_hom σ A B f)
        with (issig_homomorphism A B f).2 in *;
      change (@def_hom σ A B f) with (issig_homomorphism A B f).1 in *
  | _ => idtac
  end.

Lemma path_homomorphism `{Funext} {σ} {A B : Algebra σ}
  (f g : Homomorphism A B) (p : def_hom f = def_hom g) : f = g.
Proof.
  apply (ap (issig_homomorphism A B))^-1. by apply path_sigma_hprop.
Defined.

Class IsIsomorphism {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B)
  := BuildIsIsomorphism
    { injection_isomorphism : ∀ (s : Sort σ), Injective (f s)
    ; surjection_isomorphism : ∀ (s : Sort σ), IsSurjection (f s) }.

Global Existing Instance injection_isomorphism.
Global Existing Instance surjection_isomorphism.

Definition SigIsIsomorphism {σ} {A B : Algebra σ} (f : Homomorphism A B) : Type
  := { injection_isomorphism : ∀ (s : Sort σ), Injective (f s)
     | ∀ (s : Sort σ), IsSurjection (f s) }.

Lemma issig_is_isomorphism {σ : Signature} {A B : Algebra σ}
  (f : Homomorphism A B)
  : IsIsomorphism f <~> SigIsIsomorphism f.
Proof.
  apply symmetric_equiv.
  unfold SigIsIsomorphism.
  issig (@BuildIsIsomorphism σ A B f) (@injection_isomorphism σ A B f)
    (@surjection_isomorphism σ A B f).
Defined.

Global Instance hprop_is_isomorphism `{Funext} {σ} {A B : Algebra σ}
  (f : Homomorphism A B)
  : IsHProp (IsIsomorphism f).
Proof.
  apply HProp.equiv_hprop_allpath.
  intros i j.
  apply (ap (issig_is_isomorphism f))^-1.
  apply path_sigma_hprop.
  funext s x y p.
  apply set_path2.
Defined.

Section equiv_forgetful_isomorphism.
  Context {σ} {A B : Algebra σ} (f : Homomorphism A B) {Is : IsIsomorphism f}.

  Global Instance embedding_isomorphism : ∀ s, IsEmbedding (f s).
  Proof.
    intro s. apply isembedding_isinj_hset. apply Is.
  Defined.

  Global Instance isequiv_forgetful_isomorphism : ∀ s, IsEquiv (f s).
  Proof.
    intro s. apply isequiv_surj_emb; exact _.
  Defined.

  Definition equiv_forgetful_isomorphism : ∀ s, A s <~> B s.
  Proof.
    intro s. rapply (BuildEquiv _ _ (f s)).
  Defined.
End equiv_forgetful_isomorphism.

Section homomorphism_apply_cprod.
  Context {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B).

  Lemma path_homomorphism_apply_cprod' {w : SymbolType σ}
    (a : CProd A (dom_symboltype w)) (ao : Operation A w) (bo : Operation B w)
    (P : OpPreserving f ao bo)
    : f (cod_symboltype w) (apply_cprod ao a) = apply_cprod bo (map_cprod f a).
  Proof.
    induction w.
    - assumption.
    - destruct a as [x a]. apply IHw. apply P.
  Defined.

  Lemma path_homomorphism_apply_cprod
    : ∀ (u : Symbol σ) (a : CProd A (dom_symboltype (σ u))),
      f (cod_symboltype (σ u)) (apply_cprod (u^^A) a) =
       apply_cprod (u^^B) (map_cprod f a).
  Proof.
    intros u a.
    apply path_homomorphism_apply_cprod'.
    apply f.
  Defined.
End homomorphism_apply_cprod.

Section hom_id.
  Context {σ} (A : Algebra σ).

  Global Instance is_homomorphism_id : @IsHomomorphism σ A A (λ _, idmap).
  Proof.
   intro u. generalize (u^^A). intro w. induction (σ u).
   - reflexivity.
   - now intro x.
  Qed.

  Definition hom_id : Homomorphism A A
    := BuildHomomorphism (λ _, idmap).

  Global Instance is_isomorphism_id : IsIsomorphism hom_id.
  Proof.
    constructor; intro s.
    - intros x y. exact idmap.
    - apply BuildIsSurjection. intro y. exact (tr (y; idpath)).
  Qed.
End hom_id.

Section hom_inv.
  Context {σ} {A B : Algebra σ}.

  Global Instance is_homomorphism_inv (f : Homomorphism A B) `{!IsIsomorphism f}
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

  Definition hom_inv (f : Homomorphism A B) `{!IsIsomorphism f}
    : Homomorphism B A
    := BuildHomomorphism (λ s, (f s)^-1).

  Global Instance is_isomorphism_inv (f : Homomorphism A B) `{!IsIsomorphism f}
    : IsIsomorphism (hom_inv f).
  Proof.
    constructor.
    - intros s x y p.
      rewrite <- (eisretr (f s) x), <- (eisretr (f s) y).
      auto.
    - intro s.
      apply BuildIsSurjection.
      intro y.
      apply tr.
      exists (f s y).
      apply (eissect (f s) y).
  Qed.
End hom_inv.

Section hom_compose.
  Context {σ} {A B C : Algebra σ}.

  Lemma oppreserving_compose {w : SymbolType σ}
    {a : Operation A w} {b : Operation B w} {c : Operation C w}
    (g : Homomorphism B C) (f : Homomorphism A B)
    (G : OpPreserving g b c) (F : OpPreserving f a b)
    : OpPreserving (λ s (x : A s), g s (f s x)) a c.
  Proof.
   induction w; simpl.
   - now rewrite F, G.
   - intro x. now apply (IHw _ (b (f _ x))).
  Qed.

  Global Instance is_homomorphism_compose (g : Homomorphism B C)
    (f : Homomorphism A B)
    : IsHomomorphism (λ s, g s ∘ f s).
  Proof.
   intro u.
   exact (oppreserving_compose g f (op_preserving g u) (op_preserving f u)).
  Qed.

  Definition hom_compose (g : Homomorphism B C) (f : Homomorphism A B)
      : Homomorphism A C
    := BuildHomomorphism (λ s, g s ∘ f s).

  Global Instance is_isomorphism_compose
    (g : Homomorphism B C) `{!IsIsomorphism g}
    (f : Homomorphism A B) `{!IsIsomorphism f}
    : IsIsomorphism (hom_compose g f).
  Proof.
   constructor.
   - intros s x y p.
     by do 2 apply injection_isomorphism.
   - intro s.
     apply BuildIsSurjection.
     intro z.
     apply tr.
     exists ((f s)^-1 ((g s)^-1 z)).
     unfold hom_compose, def_hom, Compose.
     by rewrite (eisretr (f s)), (eisretr (g s)).
  Qed.
End hom_compose.

Section path_isomorphism.
  Context `{Univalence} {σ} {A B : Algebra σ}.

  Definition path_equiv_carriers (f : ∀ (s : Sort σ), A s <~> B s)
    : carriers A = carriers B
    := path_forall A B (λ s : Sort σ, path_universe (f s)).

  Lemma path_transport_carriers_equiv (f : ∀ (s : Sort σ), A s <~> B s)
    {w : SymbolType σ} (ao : Operation A w) (bo : Operation B w)
    (P : OpPreserving f ao bo)
    : transport (λ s, Operation s w) (path_equiv_carriers f) ao = bo.
  Proof.
    unfold path_equiv_carriers.
    induction w; simpl in *.
    - transport_path_forall_hammer.
      exact (apD10 (transport_idmap_path_universe (f t)) ao @ P).
    - funext y.
      transport_path_forall_hammer.
      specialize (P ((f t)^-1 y)).
      rewrite (eisretr (f t)) in P.
      rewrite transport_forall_constant.
      rewrite transport_forall.
      rewrite transport_const.
      rewrite (transport_path_universe_V (f t)).
      destruct (path_universe (f t)).
      exact (IHw (ao ((f t)^-1 y)) (bo y) P).
  Qed.

  Lemma path_transport_carriers_isomorphism (f : Homomorphism A B)
    `{!IsIsomorphism f} (u : Symbol σ)
    : transport (λ s : Carriers σ, Operation s (σ u))
        (path_equiv_carriers (equiv_forgetful_isomorphism f)) (u^^A) = u^^B.
  Proof.
    apply path_transport_carriers_equiv. apply (op_preserving f).
  Defined.

  Theorem path_isomorphism (f : Homomorphism A B) `{!IsIsomorphism f} : A = B.
  Proof.
    apply path_algebra.
    exists (path_equiv_carriers (equiv_forgetful_isomorphism f)).
    funext u.
    refine (transport (λ x : Operation B (σ u), x = u^^B)
              (transport_forall_constant _ _ u)^
              (path_transport_carriers_isomorphism f u)).
  Defined.
End path_isomorphism.
