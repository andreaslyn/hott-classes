Require Import
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.interfaces.ua_congruence
  HoTTClasses.theory.ua_homomorphism
  HoTTClasses.theory.ua_subalgebra
  HoTTClasses.theory.ua_quotient_algebra.

Import algebra_notations quotient_algebra_notations subalgebra_notations.

Section kernel.
  Context {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B).

  Definition relation_ker (s : Sort σ) : relation (A s)
    := λ (x y : A s), f s x = f s y.

  Global Instance equivalence_ker (s : Sort σ)
    : Equivalence (relation_ker s).
  Proof.
   repeat constructor.
   - intros x y h. exact (h^ @ idpath).
   - intros x y z h1 h2. exact (h1 @ h2).
  Defined.

  Lemma path_ker_hom_ap_operation {w : SymbolType σ}
    (β : Operation B w) (a b : FamilyProd A (dom_symboltype w))
    (R : for_all_2_family_prod A A relation_ker a b)
    : ap_operation β (map_family_prod f a)
      = ap_operation β (map_family_prod f b).
  Proof.
    induction w.
    - reflexivity.
    - destruct a as [x a], b as [y b], R as [r R].
      simpl.
      rewrite r.
      now apply IHw.
  Qed.

  Global Instance has_congruence_property_ker
    : HasCongruenceProperty A relation_ker.
  Proof.
    intros u a b R.
    unfold relation_ker.
    repeat rewrite (path_homomorphism_ap_operation f).
    now apply path_ker_hom_ap_operation.
  Qed.

  Definition cong_ker : Congruence A
    := BuildCongruence relation_ker.

End kernel.

Section subalgebra_predicate_in_image_hom.
  Context `{Funext} {σ} {A B : Algebra σ} (f : Homomorphism A B).

  Definition def_in_image_hom (s : Sort σ) (y : B s) : hProp
    := merely (hfiber (f s) y).

  Lemma closed_under_subalgebra_in_image_hom {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) (P : OpPreserving f α β)
    : ClosedUnderOp B def_in_image_hom β.
  Proof.
    induction w.
    - exact (tr (α; P)).
    - intro y.
      refine (Trunc_rec _). intros [x p].
      apply (IHw (α x)).
      now refine (transport (λ y, OpPreserving f (α x) (β y)) p _).
  Defined.

  Global Instance subalgebra_predicate_in_image_hom
    : IsClosedUnderOps B def_in_image_hom.
  Proof.
    intro u. eapply closed_under_subalgebra_in_image_hom, f.
  Defined.

  Definition in_image_hom : SubalgebraPredicate B
    := BuildSubalgebraPredicate def_in_image_hom.

End subalgebra_predicate_in_image_hom.

Section first_isomorphism.
  Context `{Univalence} {σ} {A B : Algebra σ} (f : Homomorphism A B).

  Definition def_first_isomorphism (s : Sort σ)
    : (A / cong_ker f) s → (B & in_image_hom f) s.
  Proof.
    refine (quotient_rec (cong_ker f s) (λ x, (f s x; tr (x; idpath))) _).
    intros x y ?.
    now apply path_sigma_hprop.
  Defined.

  Lemma oppreserving_first_isomorphism {w : SymbolType σ}
    (γ : Operation (A / cong_ker f) w) (α : Operation A w) (β : Operation B w)
    (P : OpPreserving f α β) (G : QuotientOpProperty A (cong_ker f) α γ)
    : OpPreserving def_first_isomorphism γ
        (op_subalgebra B (in_image_hom f) β
          (closed_under_subalgebra_in_image_hom f α β P)).
  Proof.
    unfold QuotientOpProperty in G.
    induction w.
    - apply path_sigma_hprop.
      generalize dependent γ.
      refine (quotient_ind_prop (cong_ker f t) _ _). intros x G.
      rewrite <- P.
      apply (classes_eq_related (cong_ker f t) _ _ (G tt)).
    - refine (quotient_ind_prop (cong_ker f t) _ _). intro x.
      apply (IHw (γ (class_of (cong_ker f t) x)) (α x) (β (f t x)) (P x)).
      intro a.
      apply (G (x,a)).
  Qed.

  Global Instance is_homomorphism_first_isomorphism
    : IsHomomorphism def_first_isomorphism.
  Proof.
    intro u.
    apply oppreserving_first_isomorphism.
    apply quotient_op_property.
  Qed.

  Definition hom_first_isomorphism
    : Homomorphism (A / cong_ker f) (B & in_image_hom f)
    := BuildHomomorphism def_first_isomorphism.

  Global Instance injection_first_isomorphism (s : Sort σ)
    : Injective (hom_first_isomorphism s).
  Proof.
    refine (quotient_ind_prop (cong_ker f s) _ _). intro x.
    refine (quotient_ind_prop (cong_ker f s) _ _). intros y p.
    apply related_classes_eq.
    exact (pr1_path p).
  Qed.

  Global Instance surjection_first_isomorphism (s : Sort σ)
    : IsSurjection (hom_first_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    intros [x X].
    refine (Trunc_rec _ X). intros [y Y].
    apply tr.
    exists (class_of _ y).
    now apply path_sigma_hprop.
  Qed.

  Theorem is_isomorphism_first_isomorphism
    : IsIsomorphism hom_first_isomorphism.
  Proof.
    constructor; exact _.
  Defined.

  Global Existing Instance is_isomorphism_first_isomorphism.

  Corollary path_first_isomorphism : A / cong_ker f = B & in_image_hom f.
  Proof.
    exact (path_isomorphism hom_first_isomorphism).
  Defined.
End first_isomorphism.

Section surjective_first_isomorphism.
  Context
    `{Univalence} {σ} {A B : Algebra σ}
    (f : Homomorphism A B) {Su : ∀ s, IsSurjection (f s)}.

  Global Instance is_isomorphism_inclusion_surjective_first_isomorphism
    : IsIsomorphism (hom_inclusion_subalgebra B (in_image_hom f)).
  Proof.
    apply is_isomorphism_inclusion_subalgebra.
    intros s y.
    destruct (Su s y) as [p P].
    refine (Trunc_rec _ p).
    intros [y' Y'].
    apply tr.
    by exists y'.
  Qed.

  Definition hom_surjective_first_isomorphism : Homomorphism (A / cong_ker f) B
  := BuildHomomorphism (λ (s : Sort σ),
      hom_inclusion_subalgebra B (in_image_hom f) s ∘ hom_first_isomorphism f s).

  Corollary path_surjective_first_isomorphism : (A / cong_ker f) = B.
  Proof.
    exact (path_isomorphism hom_surjective_first_isomorphism).
  Defined.
End surjective_first_isomorphism.
