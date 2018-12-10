Require Import
  Coq.Unicode.Utf8
  HoTT.Types.Universe
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.interfaces.ua_congruence
  HoTTClasses.theory.ua_quotient_algebra.

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
    (is_subcong : ∀ s x y, Ψ s x y → Φ s x y).

  Definition quotient_congruence (s : Sort σ) (a b : (A/Ψ) s) : Type
    := ∀ (x y : A s), in_class (Ψ s) a x → in_class (Ψ s) b y → Φ s x y.

  Global Instance equivalence_quotient_congruence (s : Sort σ)
    : Equivalence (quotient_congruence s).
  Proof.
    constructor.
    - refine (quotient_ind_prop (Ψ s) _ _).
      intros x y z P Q.
      apply is_subcong.
      by apply (Equivalence_Transitive y x z).
    - refine (quotient_ind_prop (Ψ s) _ _).
      intro x1.
      refine (quotient_ind_prop (Ψ s) _ _).
      intros x2 C y1 y2 P Q.
      apply Equivalence_Symmetric.
      by apply C.
    - refine (quotient_ind_prop (Ψ s) _ _).
      intro x1.
      refine (quotient_ind_prop (Ψ s) _ _).
      intro x2.
      refine (quotient_ind_prop (Ψ s) _ _).
      intros x3 C D y1 y2 P Q.
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
      + apply Q; simpl; apply Equivalence_Reflexive.
      + by apply IHw.
  Defined.

  Global Instance congruence_trace_congruence
    : IsCongruence (A/Ψ) quotient_congruence.
  Proof.
    intros u.
    refine (quotient_ind_prop_family_prod A Ψ _ _).
    intro a.
    refine (quotient_ind_prop_family_prod A Ψ _ _).
    intros b R x y P Q.
    rewrite (quotient_op_property_quotient_algebra A Ψ u a) in P.
    rewrite (quotient_op_property_quotient_algebra A Ψ u b) in Q.
    apply is_subcong in P.
    apply is_subcong in Q.
    apply (Equivalence_Transitive _ (ap_operation (u^^A) a)).
    - by apply Equivalence_Symmetric.
    - apply (Equivalence_Transitive _ (ap_operation (u^^A) b)); try assumption.
      apply (congruence_properties A Φ u).
      by apply for_all_quotient_congruence.
  Qed.

End quotient_congruence.
