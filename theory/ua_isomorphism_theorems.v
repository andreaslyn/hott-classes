Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.interfaces.ua_congruence
  HoTTClasses.theory.ua_homomorphism
  HoTTClasses.theory.ua_subalgebra
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.HIT.quotient
  HoTT.Types.Arrow
  HoTT.Types.Forall
  HoTT.Classes.implementations.list
  HoTT.Spaces.Nat
  HoTT.Basics.Equivalences
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.Basics.Overture
  HoTTClasses.theory.ua_quotient_algebra.

Import algebra_notations.
Import quotient_algebra_notations.
Import subalgebra_notations.

Section first_isomorphism_theorem.
  Context
    `{Univalence}
    {σ : Signature}
    {A B : Algebra σ}
    (f : Homomorphism A B).

  Definition kernel_hom (s : Sort σ) : relation (A s)
    := λ x y, f s x = f s y.

  Global Instance equivalence_kernel (s : Sort σ)
    : Equivalence (kernel_hom s).
  Proof.
   unfold kernel_hom.
   repeat constructor.
   - intros x y h. exact (h^ @ idpath).
   - intros x y z h1 h2. exact (h1 @ h2).
  Defined.

  Lemma path_kernel_ap_operation {w : SymbolType σ}
    (bo : Operation B w) (a b : FamilyProd A (dom_symboltype w))
    (R : for_all_2_family_prod A A kernel_hom a b)
    : ap_operation bo (map_family_prod f a) = ap_operation bo (map_family_prod f b).
  Proof.
    induction w.
    - reflexivity.
    - destruct a as [x a], b as [y b], R as [r R].
      simpl.
      rewrite r.
      now apply IHw.
  Qed.

  Instance congruence_kernel : IsCongruence A kernel_hom.
  Proof.
    intros u a b R.
    unfold kernel_hom.
    repeat rewrite (path_homomorphism_ap_operation f).
    now apply path_kernel_ap_operation.
  Qed.

  Definition in_image_hom (s : Sort σ) (y : B s) : Type
    := merely (hfiber (f s) y).

  Lemma op_closed_subalgebra_image {w : SymbolType σ}
    (ao : Operation A w) (bo : Operation B w) (P : OpPreserving f ao bo)
    : ClosedUnderOp B in_image_hom bo.
  Proof.
    induction w.
    - exact (tr (ao; P)).
    - intro y.
      refine (Trunc_rec _).
      intros [x p].
      apply (IHw (ao x)).
      now refine (transport (λ y, OpPreserving f (ao x) (bo y)) p _).
  Defined.

  Global Instance closedsubalg_image : IsClosedUnderOps B in_image_hom.
  Proof.
    intro u. eapply op_closed_subalgebra_image, f.
  Defined.

  Definition def_first_isomorphism (s : Sort σ)
    : (A / kernel_hom) s → (B & in_image_hom) s.
  Proof.
    refine (
      quotient_rec (kernel_hom s) (λ x : A s, (f s x ; tr (x ; idpath))) _).
    intros x y ?.
    now apply path_sigma_hprop.
  Defined.

  Lemma oppreserving_first_isomorphism {w : SymbolType σ}
    (g : Operation (A / kernel_hom) w)
    (ao : Operation A w) (bo : Operation B w)
    (P : OpPreserving f ao bo)
    (G : QuotientOpProperty A kernel_hom ao g)
    : OpPreserving def_first_isomorphism g
        (op_subalgebra B in_image_hom bo (op_closed_subalgebra_image ao bo P)).
  Proof.
    unfold QuotientOpProperty in G.
    induction w.
    - apply path_sigma_hprop.
      generalize dependent g.
      refine (quotient_ind_prop (kernel_hom t) _ _).
      intros x G.
      rewrite <- P.
      apply (classes_eq_related (kernel_hom t) _ _ (G tt)).
    - refine (quotient_ind_prop (kernel_hom t) _ _).
      intro x.
      apply (IHw (g (class_of (kernel_hom t) x)) (ao x) (bo (f t x)) (P x)).
      intro a.
      apply (G (x,a)).
  Qed.

  Global Instance is_homomorphism_first_isomorphism
    : IsHomomorphism def_first_isomorphism.
  Proof.
    intro u.
    apply oppreserving_first_isomorphism.
    apply quotient_op_property_quotient_algebra.
  Qed.

  Definition hom_first_isomorphism
    : Homomorphism (A / kernel_hom) (B & in_image_hom)
    := BuildHomomorphism def_first_isomorphism.

  Global Instance injection_first_isomorphism (s : Sort σ)
    : Injective (hom_first_isomorphism s).
  Proof.
    refine (quotient_ind_prop (kernel_hom s) _ _).
    intro x.
    refine (quotient_ind_prop (kernel_hom s) _ _).
    intros y p.
    apply related_classes_eq.
    exact (pr1_path p).
  Qed.

  Global Instance surjection_first_isomorphism (s : Sort σ)
    : IsSurjection (hom_first_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    intros [x X].
    refine (Trunc_rec _ X).
    intros [y Y].
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

  Corollary path_first_isomorphism 
    : A / kernel_hom = B & in_image_hom.
  Proof.
    exact (path_isomorphism hom_first_isomorphism).
  Defined.

End first_isomorphism_theorem.

Section second_isomorphism_theorem.
  Context
    `{Univalence}
    {σ : Signature}
    (A : Algebra σ)
    (P : ∀ s, A s → Type)
    `{!∀ s (x : A s), IsHProp (P s x)}
    `{!IsClosedUnderOps A P}
    (Φ : ∀ s, A s → A s → Type)
    `{!∀ s, is_mere_relation (A s) (Φ s)}
    `{!∀ s, Equivalence (Φ s)}
    `{!IsCongruence A Φ}.

  Let i {s} : (A&P) s → A s := def_inclusion_subalgebra A P s.

  Definition trace_congruence (s : Sort σ) (x : (A&P) s) (y : (A&P) s) : Type
    := Φ s (i x) (i y).

  Lemma for_all_2_family_prod_trace_congruence {w : SymbolType σ}
    (a b : FamilyProd (A&P) (dom_symboltype w))
    (R : for_all_2_family_prod (A&P) (A&P) trace_congruence a b)
    : for_all_2_family_prod A A Φ
        (map_family_prod (@i) a) (map_family_prod (@i) b).
  Proof with try assumption.
    induction w...
    destruct a as [x a], b as [y b], R as [C R].
    split...
    apply IHw...
  Defined.

  Global Instance equivalence_trace_congruence (s : Sort σ)
    : Equivalence (trace_congruence s).
  Proof.
    unfold trace_congruence.
    constructor.
    - intros [y Y].
      apply Equivalence_Reflexive.
    - intros [y1 Y1] [y2 Y2] S.
      apply Equivalence_Symmetric. assumption.
    - intros [y1 Y1] [y2 Y2] [y3 Y3] S T.
      apply (Equivalence_Transitive _ _ _ S T).
  Defined.

  Global Instance congruence_trace_congruence
    : IsCongruence (A&P) trace_congruence.
  Proof.
    intros u a b R.
    refine (transport (λ X, Φ _ X (i (ap_operation (u ^^ A&P) b)))
              (path_ap_operation_inclusion_subalgebra A P a (u^^A) _) _).
    refine (transport (λ X, Φ _ (ap_operation (u^^A) (map_family_prod (@i) a)) X)
              (path_ap_operation_inclusion_subalgebra A P b (u^^A) _) _).
    apply (congruence_properties A Φ).
    exact (for_all_2_family_prod_trace_congruence a b R).
  Defined.

  Definition in_subquotient (s : Sort σ) (x : (A/Φ) s)
    : Type
    := hexists (λ (y : (A&P) s), in_class (Φ s) x (i y)).

  Lemma op_closed_subalgebra_in_subquotient {w : SymbolType σ}
    (qo : Operation (A/Φ) w)
    (ao : Operation A w)
    (Q : QuotientOpProperty A Φ ao qo)
    (C : ClosedUnderOp A P ao)
    : ClosedUnderOp (A/Φ) in_subquotient qo.
  Proof.
    induction w.
    - specialize (Q tt). simpl in Q.
      apply tr.
      exists (ao; C).
      unfold i, def_inclusion_subalgebra.
      rewrite Q.
      exact (Equivalence_Reflexive ao).
    - refine (quotient_ind_prop (Φ t) _ _).
      intro x.
      refine (Trunc_rec _).
      intros [y R].
      apply (IHw (qo (class_of (Φ t) x)) (ao (i y))).
      intro a.
      rewrite (related_classes_eq (Φ t) R).
      apply (Q (i y,a)).
      apply C.
      exact y.2.
  Qed.

  Global Instance closed_subalgebra_in_subquotient
    : IsClosedUnderOps (A/Φ) in_subquotient.
  Proof.
    intro u.
    apply op_closed_subalgebra_in_subquotient with (ao := u^^A).
    apply quotient_op_property_quotient_algebra.
    apply closed_subalgebra.
    exact _.
  Qed.

  Definition def_second_isomorphism (s : Sort σ)
    : ((A&P) / trace_congruence) s → ((A/Φ) & in_subquotient) s
  := quotient_rec (trace_congruence s)
      (λ (x : (A&P) s),
        (class_of (Φ s) (i x); tr (x; Equivalence_Reflexive x)))
      (λ x y T,
        path_sigma_hprop (class_of (Φ s) (i x); _) (class_of (Φ s) (i y); _)
          (related_classes_eq (Φ s) T)).

  Lemma oppreserving_second_isomorphism {w : SymbolType σ}
    (ao : Operation A w)
    (bqo : Operation ((A&P) / trace_congruence) w)
    (aqo : Operation (A/Φ) w)
    (CB : ClosedUnderOp A P ao)
    (CA : ClosedUnderOp (A/Φ) in_subquotient aqo)
    (QA : QuotientOpProperty A Φ ao aqo)
    (QB : QuotientOpProperty (A&P) trace_congruence (op_subalgebra A P ao CB) bqo)
    : OpPreserving def_second_isomorphism bqo
        (op_subalgebra (A/Φ) in_subquotient aqo CA).
  Proof.
    unfold QuotientOpProperty in *.
    induction w; simpl in *.
    - apply path_sigma_hprop.
      rewrite (QB tt), (QA tt).
      by apply related_classes_eq.
    - refine (quotient_ind_prop (trace_congruence t) _ _).
      intro x.
      apply (IHw (ao (i x)) (bqo (class_of (trace_congruence t) x))
               (aqo (class_of (Φ t) (i x))) (CB (i x) x.2)).
      + intro a. exact (QA (i x, a)).
      + intro a. exact (QB (x, a)).
  Qed.

  Global Instance ishomomorphism_second_isomorphism
    : IsHomomorphism def_second_isomorphism.
  Proof.
    intro u.
    eapply oppreserving_second_isomorphism.
    apply (quotient_op_property_quotient_algebra A).
    apply (quotient_op_property_quotient_algebra (A&P)).
  Qed.

  Definition hom_second_isomorphism
    : Homomorphism ((A&P) / trace_congruence) ((A/Φ) & in_subquotient)
    := BuildHomomorphism def_second_isomorphism.

  Global Instance injection_second_isomorphism (s : Sort σ)
    : Injective (hom_second_isomorphism s).
  Proof.
    refine (quotient_ind_prop (trace_congruence s) _ _).
    intro x.
    refine (quotient_ind_prop (trace_congruence s) _ _).
    intros y p.
    apply related_classes_eq.
    exact (classes_eq_related (Φ s) (i x) (i y) (p..1)).
  Qed.

  Global Instance surjection_second_isomorphism (s : Sort σ)
    : IsSurjection (hom_second_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    intros [y S].
    generalize dependent S.
    generalize dependent y.
    refine (quotient_ind_prop (Φ s) _ _).
    intros y S.
    refine (Trunc_rec _ S).
    intros [y' S'].
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

  Corollary path_second_isomorphism
    : (A&P) / trace_congruence = ((A/Φ) & in_subquotient).
  Proof.
    exact (path_isomorphism hom_second_isomorphism).
  Defined.
End second_isomorphism_theorem.
