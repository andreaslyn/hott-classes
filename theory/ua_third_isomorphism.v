Require Import
  HoTT.Types.Universe
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.interfaces.ua_congruence
  HoTTClasses.theory.ua_quotient_algebra
  HoTTClasses.theory.ua_homomorphism
  HoTTClasses.theory.ua_first_isomorphism.

Import algebra_notations quotient_algebra_notations.

Section cong_quotient.
  Context
    `{Univalence}
    {σ : Signature}
    {A : Algebra σ}
    (Φ : Congruence A)
    (Ψ : Congruence A)
    (is_subrel : ∀ s x y, Ψ s x y → Φ s x y).

  Definition relation_quotient (s : Sort σ) (a b : (A/Ψ) s) : Type
    := ∀ (x y : A s), in_class (Ψ s) a x → in_class (Ψ s) b y → Φ s x y.

  Global Instance equivalence_relation_quotient (s : Sort σ)
    : Equivalence (relation_quotient s).
  Proof.
    constructor.
    - refine (quotient_ind_prop (Ψ s) _ _). intros x y z P Q.
      apply is_subrel.
      by transitivity x.
    - refine (quotient_ind_prop (Ψ s) _ _). intro x1.
      refine (quotient_ind_prop (Ψ s) _ _). intros x2 C y1 y2 P Q.
      symmetry.
      by apply C.
    - refine (quotient_ind_prop (Ψ s) _ _). intro x1.
      refine (quotient_ind_prop (Ψ s) _ _). intro x2.
      refine (quotient_ind_prop (Ψ s) _ _). intros x3 C D y1 y2 P Q.
      transitivity x2.
      + exact (C y1 x2 P (Equivalence_Reflexive x2)).
      + exact (D x2 y2 (Equivalence_Reflexive x2) Q).
  Defined.

  Lemma for_all_relation_quotient {w : list (Sort σ)} (a b : FamilyProd A w)
    : for_all_2_family_prod (A/Ψ) (A/Ψ) relation_quotient
        (map_family_prod (λ s, class_of (Ψ s)) a)
        (map_family_prod (λ s, class_of (Ψ s)) b) →
      for_all_2_family_prod A A Φ a b.
  Proof.
    intro F.
    induction w; simpl in *.
    - constructor.
    - destruct a as [x a], b as [y b], F as [Q F].
      split.
      + apply Q; simpl; reflexivity.
      + by apply IHw.
  Qed.

  Global Instance has_congruence_property_relation_quotient
    : HasCongruenceProperty (A/Ψ) relation_quotient.
  Proof.
    intros u.
    refine (quotient_ind_prop_family_prod A Ψ _ _). intro a.
    refine (quotient_ind_prop_family_prod A Ψ _ _). intros b R x y P Q.
    rewrite (quotient_op_property A Ψ u a) in P.
    rewrite (quotient_op_property A Ψ u b) in Q.
    apply is_subrel in P.
    apply is_subrel in Q.
    transitivity (ap_operation (u^^A) a).
    - by symmetry.
    - transitivity (ap_operation (u^^A) b); try assumption.
      apply (property_congruence Φ u).
      by apply for_all_relation_quotient.
  Qed.

  Definition cong_quotient : Congruence (A/Ψ)
    := BuildCongruence relation_quotient.

End cong_quotient.

Section third_isomorphism.
  Context
    `{Univalence}
    {σ : Signature}
    {A : Algebra σ}
    (Φ : Congruence A)
    (Ψ : Congruence A)
    (is_subrel : ∀ s x y, Ψ s x y → Φ s x y).

  Local Notation Θ := (cong_quotient Φ Ψ is_subrel).

  Lemma third_isomorphism_well_def_1 (s : Sort σ)
    (x y : A s) (P : Ψ s x y)
    : class_of (Φ s) x = class_of (Φ s) y.
  Proof.
    apply related_classes_eq. exact (is_subrel s x y P).
  Defined.

  Lemma third_isomorphism_well_def_2 (s : Sort σ) P
    : ∀ (x y : (A/Ψ) s), Θ s x y →
        quotient_rec (Ψ s) (class_of (Φ s)) P x
        = quotient_rec (Ψ s) (class_of (Φ s)) P y.
  Proof.
    refine (quotient_ind_prop (Ψ s) _ _).
    intro x.
    refine (quotient_ind_prop (Ψ s) _ _).
    intros y C.
    apply related_classes_eq.
    exact (C x y (Equivalence_Reflexive x) (Equivalence_Reflexive y)).
  Defined.

  Definition def_third_isomorphism (s : Sort σ) : (A/Ψ/Θ) s → (A/Φ) s
    := quotient_rec (Θ s)
         (quotient_rec (Ψ s) (class_of (Φ s)) (third_isomorphism_well_def_1 s))
         (third_isomorphism_well_def_2 s _).

  Lemma oppreserving_third_isomorphism {w : SymbolType σ} (f : Operation A w)
    : ∀ (α : Operation (A/Φ) w) (Qα : QuotientOpProperty A Φ f α)
        (β : Operation (A/Ψ) w) (Qβ : QuotientOpProperty A Ψ f β)
        (γ : Operation (A/Ψ/Θ) w) (Qγ : QuotientOpProperty (A/Ψ) Θ β γ),
      OpPreserving def_third_isomorphism γ α.
  Proof.
    induction w.
    - refine (quotient_ind_prop (Φ t) _ _). intros α Qα.
      refine (quotient_ind_prop (Ψ t) _ _). intros β Qβ.
      refine (quotient_ind_prop (Θ t) _ _).
      refine (quotient_ind_prop (Ψ t) _ _). intros γ Qγ.
      apply related_classes_eq.
      transitivity f.
      + apply (classes_eq_related (Θ t) _ _ (Qγ tt)).
        * simpl. reflexivity.
        * apply (classes_eq_related (Ψ t)). exact (Qβ tt).
      + apply (classes_eq_related (Φ t)). symmetry. exact (Qα tt).
    - intros α Qα β Qβ γ Qγ.
      refine (quotient_ind_prop (Θ t) _ _).
      refine (quotient_ind_prop (Ψ t) _ _).
      intro x.
      apply (IHw (f x) (α (class_of (Φ t) x)) (λ a, Qα (x,a))
               (β (class_of (Ψ t) x)) (λ a, Qβ (x,a))).
      intro a.
      exact (Qγ (class_of (Ψ t) x, a)).
  Qed.

 Global Instance is_homomorphism_third_isomorphism
    : IsHomomorphism def_third_isomorphism.
  Proof with apply quotient_op_property.
    intro u.
    eapply oppreserving_third_isomorphism...
  Qed.

  Definition hom_third_isomorphism
    : Homomorphism (A/Ψ/Θ) (A/Φ)
    := BuildHomomorphism def_third_isomorphism.

  Global Instance surjection_third_isomorphism (s : Sort σ)
    : IsSurjection (hom_third_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    refine (quotient_ind_prop (Φ s) _ _).
    intro y.
    apply tr.
    by exists (class_of (Θ s) (class_of (Ψ s) y)).
  Qed.

  Global Instance injection_third_isomorphism (s : Sort σ)
    : Injective (hom_third_isomorphism s).
  Proof.
    refine (quotient_ind_prop (Θ s) _ _).
    refine (quotient_ind_prop (Ψ s) _ _). intro x.
    refine (quotient_ind_prop (Θ s) _ _).
    refine (quotient_ind_prop (Ψ s) _ _). intros y p.
    apply related_classes_eq.
    intros x' y' P Q.
    apply is_subrel in P. apply is_subrel in Q.
    apply (classes_eq_related (Φ s)) in p.
    transitivity x.
    - by symmetry.
    - by transitivity y.
  Qed.

  Theorem is_isomorphism_third_isomorphism
    : IsIsomorphism hom_third_isomorphism.
  Proof.
    constructor; exact _.
  Qed.

  Global Existing Instance is_isomorphism_third_isomorphism.

  Corollary path_third_isomorphism : A/Ψ/Θ = A/Φ.
  Proof.
    exact (path_isomorphism hom_third_isomorphism).
  Defined.
End third_isomorphism.

Section third_isomorphism'.
  Context
    `{Univalence}
    {σ : Signature}
    {A : Algebra σ}
    (Φ : Congruence A)
    (Ψ : Congruence A)
    (is_subrel : ∀ s x y, Ψ s x y → Φ s x y).

  Definition def_third_surjection (s : Sort σ) : (A/Ψ) s → (A/Φ) s
    := quotient_rec (Ψ s) (class_of (Φ s))
        (third_isomorphism_well_def_1 Φ Ψ is_subrel s).

  Lemma oppreserving_third_surjection {w : SymbolType σ} (f : Operation A w)
    : ∀ (α : Operation (A/Φ) w) (Qα : QuotientOpProperty A Φ f α)
        (β : Operation (A/Ψ) w) (Qβ : QuotientOpProperty A Ψ f β),
      OpPreserving def_third_surjection β α.
  Proof.
    induction w.
    - refine (quotient_ind_prop (Φ t) _ _). intros α Qα.
      refine (quotient_ind_prop (Ψ t) _ _). intros β Qβ.
      apply related_classes_eq.
      transitivity f.
      + apply is_subrel. apply (classes_eq_related (Ψ t)). exact (Qβ tt).
      + apply (classes_eq_related (Φ t)). symmetry. exact (Qα tt).
    - intros α Qα β Qβ.
      refine (quotient_ind_prop (Ψ t) _ _).
      intro x.
      exact (IHw (f x) (α (class_of (Φ t) x)) (λ a, Qα (x,a))
               (β (class_of (Ψ t) x)) (λ a, Qβ (x,a))).
  Qed.

 Global Instance is_homomorphism_third_surjection
    : IsHomomorphism def_third_surjection.
  Proof with apply quotient_op_property.
    intro u.
    eapply oppreserving_third_surjection...
  Qed.

  Definition hom_third_surjection : Homomorphism (A/Ψ) (A/Φ)
    := BuildHomomorphism def_third_surjection.

  Global Instance surjection_third_surjection (s : Sort σ)
    : IsSurjection (hom_third_surjection s).
  Proof.
    apply BuildIsSurjection.
    refine (quotient_ind_prop (Φ s) _ _).
    intro x.
    apply tr.
    by exists (class_of (Ψ s) x).
  Qed.

  Local Notation Θ := (cong_quotient Φ Ψ is_subrel).

  Lemma iff_third_surjection_cong_ker_quotient (s : Sort σ) (x y : (A/Ψ) s)
    : cong_ker hom_third_surjection s x y ↔ Θ s x y.
  Proof.
    split; generalize dependent y; generalize dependent x;
           refine (quotient_ind_prop (Ψ s) _ _); intro x;
           refine (quotient_ind_prop (Ψ s) _ _); intro y.
    - intros K x' y' Cx Cy.
      apply is_subrel in Cx. apply is_subrel in Cy.
      apply (classes_eq_related (Φ s)) in K.
      transitivity x.
      + by symmetry.
      + by transitivity y.
    - intro T.
      apply related_classes_eq.
      exact (T x y (Equivalence_Reflexive x) (Equivalence_Reflexive y)).
  Defined.

  Lemma path_third_surjection_cong_ker_quotient
    : cong_ker hom_third_surjection = Θ.
  Proof.
    apply path_congruence; try exact _.
    exact iff_third_surjection_cong_ker_quotient.
  Defined.

  Definition hom_third_isomorphism' : Homomorphism (A/Ψ/Θ) (A/Φ)
    := transport (λ C, Homomorphism (A/Ψ/C) (A/Φ))
          path_third_surjection_cong_ker_quotient
          (hom_surjective_first_isomorphism hom_third_surjection).

  Theorem is_isomorphism_third_isomorphism'
    : IsIsomorphism hom_third_isomorphism'.
  Proof.
    unfold hom_third_isomorphism'.
    destruct path_third_surjection_cong_ker_quotient.
    exact _.
  Qed.

  Global Existing Instance is_isomorphism_third_isomorphism'.

  Corollary path_third_isomorphism' : A/Ψ/Θ = A/Φ.
  Proof.
    exact (path_isomorphism hom_third_isomorphism').
  Defined.

  Lemma path_hom_third_isomorphisms
    : hom_third_isomorphism Φ Ψ is_subrel = hom_third_isomorphism'.
  Proof.
    apply path_homomorphism.
    funext s x.
    generalize dependent x.
    refine (quotient_ind_prop (Θ s) _ _).
    refine (quotient_ind_prop (Ψ s) _ _). intro x.
    unfold hom_third_isomorphism'.
    by induction path_third_surjection_cong_ker_quotient.
  Defined.
End third_isomorphism'.
