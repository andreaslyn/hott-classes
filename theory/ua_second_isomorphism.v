Require Import
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.interfaces.ua_congruence
  HoTTClasses.theory.ua_homomorphism
  HoTTClasses.theory.ua_subalgebra
  HoTTClasses.theory.ua_quotient_algebra
  HoTTClasses.theory.ua_first_isomorphism.

Import algebra_notations quotient_algebra_notations subalgebra_notations.

Local Notation i := (def_inclusion_subalgebra _ _).

Section cong_trace.
  Context
    {σ : Signature}
    {A : Algebra σ}
    (P : SubalgebraPredicate A)
    (Φ : Congruence A).

  Definition relation_trace (s : Sort σ) (x : (A&P) s) (y : (A&P) s) : Type
    := Φ s (i s x) (i s y).

  Global Instance equivalence_trace_congruence (s : Sort σ)
    : Equivalence (relation_trace s).
  Proof.
    unfold relation_trace.
    constructor.
    - intros [y Y]. reflexivity.
    - intros [y1 Y1] [y2 Y2] S. by symmetry.
    - intros [y1 Y1] [y2 Y2] [y3 Y3] S T. by transitivity y2.
  Defined.

  Lemma for_all_2_family_prod_trace_congruence {w : SymbolType σ}
    (a b : FamilyProd (A&P) (dom_symboltype w))
    (R : for_all_2_family_prod (A&P) (A&P) relation_trace a b)
    : for_all_2_family_prod A A Φ
        (map_family_prod i a) (map_family_prod i b).
  Proof with try assumption.
    induction w...
    destruct a as [x a], b as [y b], R as [C R].
    split...
    apply IHw...
  Qed.

  Global Instance has_congruence_property_trace
    : HasCongruenceProperty (A&P) relation_trace.
  Proof.
    intros u a b R.
    refine (transport (λ X, Φ _ X (i _ (ap_operation (u ^^ A&P) b)))
              (path_ap_operation_inclusion_subalgebra A P a (u^^A) _) _).
    refine (transport (λ X, Φ _ (ap_operation (u^^A) (map_family_prod i a)) X)
              (path_ap_operation_inclusion_subalgebra A P b (u^^A) _) _).
    apply (property_congruence Φ).
    exact (for_all_2_family_prod_trace_congruence a b R).
  Qed.

  Definition cong_trace : Congruence (A&P)
    := BuildCongruence relation_trace.

End cong_trace.

Section in_subquotient.
  Context
    `{Univalence}
    {σ : Signature}
    {A : Algebra σ}
    (P : SubalgebraPredicate A)
    (Φ : Congruence A).

  Definition def_in_subquotient (s : Sort σ) (x : (A/Φ) s) : hProp
    := hexists (λ (y : (A&P) s), in_class (Φ s) x (i s y)).

  Lemma op_closed_subalgebra_in_subquotient {w : SymbolType σ}
    (γ : Operation (A/Φ) w)
    (α : Operation A w)
    (Q : QuotientOpProperty A Φ α γ)
    (C : ClosedUnderOp A P α)
    : ClosedUnderOp (A/Φ) def_in_subquotient γ.
  Proof.
    induction w.
    - specialize (Q tt). simpl in Q.
      apply tr.
      exists (α; C).
      unfold i, def_inclusion_subalgebra.
      rewrite Q.
      exact (Equivalence_Reflexive α).
    - refine (quotient_ind_prop (Φ t) _ _). intro x.
      refine (Trunc_rec _).
      intros [y R].
      apply (IHw (γ (class_of (Φ t) x)) (α (i t y))).
      intro a.
      rewrite (related_classes_eq (Φ t) R).
      apply (Q (i t y,a)).
      apply C.
      exact y.2.
  Qed.

  Global Instance is_closed_under_ops_in_subquotient
    : IsClosedUnderOps (A/Φ) def_in_subquotient.
  Proof.
    intro u.
    eapply op_closed_subalgebra_in_subquotient.
    apply quotient_op_property.
    apply closed_under_ops.
    exact _.
  Qed.

  Definition in_subquotient : SubalgebraPredicate (A/Φ)
    := BuildSubalgebraPredicate def_in_subquotient.

End in_subquotient.

Section second_isomorphism.
  Context
    `{Univalence}
    {σ : Signature}
    {A : Algebra σ}
    (P : SubalgebraPredicate A)
    (Φ : Congruence A).

  Local Notation Ψ := (cong_trace P Φ).

  Local Notation Q := (in_subquotient P Φ).

  Definition def_second_isomorphism (s : Sort σ) : ((A&P) / Ψ) s → ((A/Φ) & Q) s
  := quotient_rec (Ψ s)
      (λ (x : (A&P) s),
       (class_of (Φ s) (i s x); tr (x; Equivalence_Reflexive x)))
      (λ (x y : (A&P) s) (T : Ψ s x y),
       path_sigma_hprop (class_of (Φ s) (i s x); _) (class_of (Φ s) (i s y); _)
         (related_classes_eq (Φ s) T)).

  Lemma oppreserving_second_isomorphism {w : SymbolType σ}
    (α : Operation A w)
    (γ : Operation (A/Φ) w)
    (ζ : Operation ((A&P) / Ψ) w)
    (CA : ClosedUnderOp (A/Φ) Q γ)
    (CB : ClosedUnderOp A P α)
    (QA : QuotientOpProperty A Φ α γ)
    (QB : QuotientOpProperty (A&P) Ψ (op_subalgebra A P α CB) ζ)
    : OpPreserving def_second_isomorphism ζ
        (op_subalgebra (A/Φ) Q γ CA).
  Proof.
    unfold QuotientOpProperty in *.
    induction w; simpl in *.
    - apply path_sigma_hprop.
      rewrite (QB tt), (QA tt).
      by apply related_classes_eq.
    - refine (quotient_ind_prop (Ψ t) _ _). intro x.
      apply (IHw (α (i t x)) (γ (class_of (Φ t) (i t x)))
              (ζ (class_of (Ψ t) x))
              (CA (class_of (Φ t) (i t x)) (tr (x; Equivalence_Reflexive x)))
              (CB (i t x) x.2)).
      + intro a. exact (QA (i t x, a)).
      + intro a. exact (QB (x, a)).
  Qed.

  Global Instance ishomomorphism_second_isomorphism
    : IsHomomorphism def_second_isomorphism.
  Proof.
    intro u.
    eapply oppreserving_second_isomorphism.
    apply (quotient_op_property A).
    apply (quotient_op_property (A&P)).
  Qed.

  Definition hom_second_isomorphism : Homomorphism ((A&P) / Ψ) ((A/Φ) & Q)
    := BuildHomomorphism def_second_isomorphism.

  Global Instance injection_second_isomorphism (s : Sort σ)
    : Injective (hom_second_isomorphism s).
  Proof.
    refine (quotient_ind_prop (Ψ s) _ _). intro x.
    refine (quotient_ind_prop (Ψ s) _ _). intros y p.
    apply related_classes_eq.
    exact (classes_eq_related (Φ s) (i s x) (i s y) (p..1)).
  Qed.

  Global Instance surjection_second_isomorphism (s : Sort σ)
    : IsSurjection (hom_second_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    intros [y S].
    generalize dependent S.
    generalize dependent y.
    refine (quotient_ind_prop (Φ s) _ _). intros y S.
    refine (Trunc_rec _ S). intros [y' S'].
    apply tr.
    exists (class_of _ y').
    apply path_sigma_hprop.
    by apply related_classes_eq.
  Qed.

  Theorem is_isomorphism_second_isomorphism
    : IsIsomorphism hom_second_isomorphism.
  Proof.
    constructor; exact _.
  Qed.

  Global Existing Instance is_isomorphism_second_isomorphism.

  Corollary path_second_isomorphism : (A&P) / Ψ = (A/Φ) & Q.
  Proof.
    exact (path_isomorphism hom_second_isomorphism).
  Defined.
End second_isomorphism.

Section second_isomorphism'.
  Context
    `{Univalence}
    {σ : Signature}
    (A : Algebra σ)
    (P : SubalgebraPredicate A)
    (Φ : Congruence A).

  Local Notation Ψ := (cong_trace P Φ).

  Local Notation Q := (in_subquotient P Φ).

  Definition def_second_surjection (s : Sort σ) (x : (A&P) s) : ((A/Φ) & Q) s
    := (class_of (Φ s) (i s x); tr (x; Equivalence_Reflexive x)).

  Lemma oppreserving_second_surjection {w : SymbolType σ}
    (α : Operation A w)
    (γ : Operation (A/Φ) w)
    (Cγ : ClosedUnderOp (A/Φ) Q γ)
    (Cα : ClosedUnderOp A P α)
    (R : QuotientOpProperty A Φ α γ)
    : OpPreserving def_second_surjection (op_subalgebra A P α Cα)
        (op_subalgebra (A/Φ) Q γ Cγ).
  Proof.
    unfold QuotientOpProperty in *.
    induction w; simpl in *.
    - apply path_sigma_hprop. symmetry. apply (R tt).
    - intro x.
      by specialize (IHw (α (i t x)) (γ (class_of (Φ t) (i t x)))
              (Cγ (class_of (Φ t) (i t x)) (tr (x; Equivalence_Reflexive x)))
              (Cα (i t x) x.2) (λ a, R (i t x, a))).
  Qed.

  Global Instance is_homomorphism_second_surjection
    : IsHomomorphism def_second_surjection.
  Proof.
    intro u.
    apply oppreserving_second_surjection.
    apply (quotient_op_property A).
  Qed.

  Definition hom_second_surjection : Homomorphism (A&P) ((A/Φ) & Q)
    := BuildHomomorphism def_second_surjection.

  Global Instance surjection_second_surjection (s : Sort σ)
    : IsSurjection (hom_second_surjection s).
  Proof.
    apply BuildIsSurjection.
    intros [y Y].
    generalize dependent Y.
    generalize dependent y.
    refine (quotient_ind_prop (Φ s) _ _).
    intros y Y.
    refine (Trunc_rec _ Y).
    intros [y' Y'].
    apply tr.
    exists y'.
    apply path_sigma_hprop.
    by apply related_classes_eq.
  Qed.

  Lemma iff_second_surjection_cong_ker_trace (s : Sort σ) (x y : (A&P) s)
    : cong_ker hom_second_surjection s x y ↔ Ψ s x y.
  Proof.
    split.
    - intro K. apply (classes_eq_related (Φ s)). apply (K..1).
    - intro T. apply path_sigma_hprop. by apply related_classes_eq.
  Defined.

  Lemma path_second_surjection_cong_ker_trace
    : cong_ker hom_second_surjection = Ψ.
  Proof.
    apply path_congruence; try exact _.
    apply iff_second_surjection_cong_ker_trace.
  Defined.

  Definition hom_second_isomorphism' : Homomorphism ((A&P) / Ψ) ((A/Φ) & Q)
    := transport (λ C, Homomorphism ((A&P) / C) (A/Φ & Q))
          path_second_surjection_cong_ker_trace
          (hom_surjective_first_isomorphism hom_second_surjection).

  Theorem is_isomorphism_second_isomorphism'
    : IsIsomorphism hom_second_isomorphism'.
  Proof.
    unfold hom_second_isomorphism'.
    destruct path_second_surjection_cong_ker_trace.
    exact _.
  Qed.

  Global Existing Instance is_isomorphism_second_isomorphism'.

  Corollary path_second_isomorphism' : (A&P) / Ψ = (A/Φ) & Q.
  Proof.
    exact (path_isomorphism hom_second_isomorphism').
  Defined.

  Lemma path_hom_second_isomorphisms
    : hom_second_isomorphism P Φ = hom_second_isomorphism'.
  Proof.
    apply path_homomorphism.
    funext s x.
    generalize dependent x.
    refine (quotient_ind_prop (Ψ s) _ _). intros [x E].
    apply path_sigma_hprop.
    unfold hom_second_isomorphism'.
    by induction path_second_surjection_cong_ker_trace.
  Defined.
End second_isomorphism'.
