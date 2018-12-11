Require Import
  Coq.Unicode.Utf8
  HoTT.Types.Universe
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.interfaces.ua_congruence
  HoTTClasses.theory.ua_quotient_algebra
  HoTTClasses.theory.ua_homomorphism.

Import algebra_notations quotient_algebra_notations.

Section quotient_congruence.
  Context
    `{Univalence}
    {σ : Signature}
    (A : Algebra σ)
    (Φ : ∀ s, relation (A s))
    `{!∀ s, is_mere_relation (A s) (Φ s)}
    `{!∀ s, Equivalence (Φ s)}
    `{!IsCongruence A Φ}
    (Ψ : ∀ s, relation (A s))
    `{!∀ s, is_mere_relation (A s) (Ψ s)}
    `{!∀ s, Equivalence (Ψ s)}
    `{!IsCongruence A Ψ}
    (is_subrel : ∀ s x y, Ψ s x y → Φ s x y).

  Definition quotient_congruence (s : Sort σ) (a b : (A/Ψ) s) : Type
    := ∀ (x y : A s), in_class (Ψ s) a x → in_class (Ψ s) b y → Φ s x y.

  Global Instance equivalence_quotient_congruence (s : Sort σ)
    : Equivalence (quotient_congruence s).
  Proof.
    constructor.
    - refine (quotient_ind_prop (Ψ s) _ _). intros x y z P Q.
      apply is_subrel.
      by apply (Equivalence_Transitive y x z).
    - refine (quotient_ind_prop (Ψ s) _ _). intro x1.
      refine (quotient_ind_prop (Ψ s) _ _). intros x2 C y1 y2 P Q.
      apply Equivalence_Symmetric.
      by apply C.
    - refine (quotient_ind_prop (Ψ s) _ _). intro x1.
      refine (quotient_ind_prop (Ψ s) _ _). intro x2.
      refine (quotient_ind_prop (Ψ s) _ _). intros x3 C D y1 y2 P Q.
      apply (Equivalence_Transitive y1 x2 y2).
      + exact (C y1 x2 P (Equivalence_Reflexive x2)).
      + exact (D x2 y2 (Equivalence_Reflexive x2) Q).
  Defined.

  Lemma for_all_quotient_congruence {w : list (Sort σ)} (a b : FamilyProd A w)
    : for_all_2_family_prod (A/Ψ) (A/Ψ) quotient_congruence
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
  Defined.

  Global Instance congruence_trace_congruence
    : IsCongruence (A/Ψ) quotient_congruence.
  Proof.
    intros u.
    refine (quotient_ind_prop_family_prod A Ψ _ _). intro a.
    refine (quotient_ind_prop_family_prod A Ψ _ _). intros b R x y P Q.
    rewrite (quotient_op_property_quotient_algebra A Ψ u a) in P.
    rewrite (quotient_op_property_quotient_algebra A Ψ u b) in Q.
    apply is_subrel in P.
    apply is_subrel in Q.
    apply (Equivalence_Transitive _ (ap_operation (u^^A) a)).
    - by apply Equivalence_Symmetric.
    - apply (Equivalence_Transitive _ (ap_operation (u^^A) b)); try assumption.
      apply (congruence_properties A Φ u).
      by apply for_all_quotient_congruence.
  Qed.

  Lemma third_isomorphism_well_def_1 (s : Sort σ)
    (x y : A s) (P : Ψ s x y)
    : class_of (Φ s) x = class_of (Φ s) y.
  Proof.
    apply related_classes_eq. exact (is_subrel s x y P).
  Defined.

  Lemma third_isomorphism_well_def_2 (s : Sort σ) P
    : ∀ (x y : (A / Ψ) s),
      quotient_congruence s x y →
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

  Definition def_third_isomorphism (s : Sort σ)
    : (A/Ψ / quotient_congruence) s → (A/Φ) s
    := quotient_rec (quotient_congruence s)
         (quotient_rec (Ψ s) (class_of (Φ s)) (third_isomorphism_well_def_1 s))
         (third_isomorphism_well_def_2 s _).

  Lemma oppreserving_third_isomorphism {w : SymbolType σ} (f : Operation A w)
    : ∀ (α : Operation (A/Φ) w)
        (Qα : QuotientOpProperty A Φ f α)
        (β : Operation (A/Ψ) w)
        (Qβ : QuotientOpProperty A Ψ f β)
        (γ : Operation (A/Ψ / quotient_congruence) w)
        (Qγ : QuotientOpProperty (A/Ψ) quotient_congruence β γ),
      OpPreserving def_third_isomorphism γ α.
  Proof.
    induction w.
    - refine (quotient_ind_prop (Φ t) _ _). intros α Qα.
      refine (quotient_ind_prop (Ψ t) _ _). intros β Qβ.
      refine (quotient_ind_prop (quotient_congruence t) _ _).
      refine (quotient_ind_prop (Ψ t) _ _). intros γ Qγ.
      apply related_classes_eq.
      apply (Equivalence_Transitive γ f α).
      + apply (classes_eq_related (quotient_congruence t) _ _ (Qγ tt)).
        * simpl. reflexivity.
        * apply (classes_eq_related (Ψ t)). exact (Qβ tt).
      + apply (classes_eq_related (Φ t)). symmetry. exact (Qα tt).
    - intros α Qα β Qβ γ Qγ.
      refine (quotient_ind_prop (quotient_congruence t) _ _).
      refine (quotient_ind_prop (Ψ t) _ _).
      intro x.
      apply (IHw (f x) (α (class_of (Φ t) x)) (λ a, Qα (x,a))
               (β (class_of (Ψ t) x)) (λ a, Qβ (x,a))).
      intro a.
      exact (Qγ (class_of (Ψ t) x, a)).
  Qed.

 Global Instance ishomomorphism_third_isomorphism
    : IsHomomorphism def_third_isomorphism.
  Proof with apply quotient_op_property_quotient_algebra.
    intro u.
    eapply oppreserving_third_isomorphism...
  Qed.
End quotient_congruence.
