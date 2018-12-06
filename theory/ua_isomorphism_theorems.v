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
  HoTTClasses.implementations.ua_carrier_product
  HoTT.Spaces.Nat
  HoTT.Basics.Equivalences
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.Basics.Overture
  HoTTClasses.theory.ua_quotientalgebra.

Import algebra_notations.

Section first_isomorphism_theorem.
  Context
    `{Univalence}
    {σ : Signature}
    {A B : Algebra σ}
    (f : Homomorphism A B).

  Definition hom_kernel (s : sort σ) : relation (A s)
    := λ x y, f s x = f s y.

  Global Instance equivalence_kernel (s : sort σ)
    : Equivalence (hom_kernel s).
  Proof.
   unfold hom_kernel.
   repeat constructor.
   - intros x y h. refine (h^ @ idpath).
   - intros x y z h1 h2. exact (h1 @ h2).
  Defined.

  Lemma path_kernel_cprod_apply {w : symboltype σ}
    (bo : Operation B w) (a b : CProd A (dom_symboltype w))
    (R : for_all_2_cprod hom_kernel a b)
    : apply_cprod bo (map_cprod f a) = apply_cprod bo (map_cprod f b).
  Proof.
    induction w.
    - reflexivity.
    - destruct a as [x a], b as [y b], R as [r R].
      simpl.
      rewrite r.
      now apply IHw.
  Qed.

  Instance congruence_kernel : IsCongruence A hom_kernel.
  Proof.
    intros u a b R.
    unfold hom_kernel.
    repeat rewrite (path_homomorphism_apply_cprod f).
    now apply path_kernel_cprod_apply.
  Qed.

  Definition in_hom_image (s : sort σ) (y : B s) : Type
    := merely (hfiber (f s) y).

  Lemma op_closed_subalgabra_image {w : symboltype σ}
    (ao : Operation A w) (bo : Operation B w) (P : OpPreserving f ao bo)
    : op_closed_subalgebra in_hom_image bo.
  Proof.
    induction w.
    - exact (tr (ao; P)).
    - intro y.
      refine (Trunc_rec _).
      intros [x p].
      apply (IHw (ao x)).
      now refine (transport (λ y, OpPreserving f (ao x) (bo y)) p _).
  Defined.

  Global Instance closedsubalg_image : ClosedSubalgebra in_hom_image.
  Proof.
    intro u. eapply op_closed_subalgabra_image, f.
  Defined.

  Definition def_first_isomorphism (s : sort σ)
    : QuotientAlgebra A hom_kernel s → Subalgebra in_hom_image s.
  Proof.
    refine (
      quotient_rec (hom_kernel s) (λ x : A s, (f s x ; tr (x ; idpath))) _).
    intros x y ?.
    now apply path_sigma_hprop.
  Defined.

  Lemma oppreserving_first_isomorphism {w : symboltype σ}
    (g : Operation (QuotientAlgebra A hom_kernel) w)
    (ao : Operation A w) (bo : Operation B w)
    (P : OpPreserving f ao bo)
    (G : quotient_op_property A hom_kernel ao g)
    : OpPreserving def_first_isomorphism g
        (op_subalgebra in_hom_image bo (op_closed_subalgabra_image ao bo P)).
  Proof.
    unfold quotient_op_property in G.
    induction w.
    - apply path_sigma_hprop.
      generalize dependent g.
      refine (quotient_ind_prop (hom_kernel t) _ _).
      intros x G.
      rewrite <- P.
      apply (classes_eq_related (hom_kernel t) _ _ (G tt)).
    - refine (quotient_ind_prop (hom_kernel t) _ _).
      intro x.
      apply (IHw (g (class_of (hom_kernel t) x)) (ao x) (bo (f t x)) (P x)).
      intro a.
      apply (G (x,a)).
  Qed.

  Global Instance ishomomorphism_first_isomorphism
    : IsHomomorphism def_first_isomorphism.
  Proof.
    intro u.
    apply oppreserving_first_isomorphism.
    apply quotient_op_property_quotientalgebra.
  Qed.

  Definition hom_first_isomorphism
    : Homomorphism (QuotientAlgebra A hom_kernel) (Subalgebra in_hom_image)
    := BuildHomomorphism def_first_isomorphism.

  Global Instance injection_first_isomorphism (s : sort σ)
    : Injective (hom_first_isomorphism s).
  Proof.
    refine (quotient_ind_prop (hom_kernel s) _ _).
    intro x.
    refine (quotient_ind_prop (hom_kernel s) _ _).
    intros y p.
    apply related_classes_eq.
    exact (pr1_path p).
  Qed.

  Global Instance surjection_first_isomorphism (s : sort σ)
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

  Global Instance isomorphism_first_isomorphism
    : IsIsomorphism hom_first_isomorphism.
  Proof.
    constructor; exact _.
  Defined.

  Corollary path_first_isomorphism 
    : QuotientAlgebra A hom_kernel = Subalgebra in_hom_image.
  Proof.
    exact (path_isomorphism hom_first_isomorphism).
  Defined.

End first_isomorphism_theorem.
