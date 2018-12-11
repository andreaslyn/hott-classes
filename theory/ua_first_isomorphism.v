Require Import
  Coq.Unicode.Utf8
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

  Definition ker_hom (s : Sort σ) : relation (A s)
    := λ x y, f s x = f s y.

  Global Instance equivalence_ker_hom (s : Sort σ)
    : Equivalence (ker_hom s).
  Proof.
   unfold ker_hom.
   repeat constructor.
   - intros x y h. exact (h^ @ idpath).
   - intros x y z h1 h2. exact (h1 @ h2).
  Defined.

  Lemma path_ker_hom_ap_operation {w : SymbolType σ}
    (β : Operation B w) (a b : FamilyProd A (dom_symboltype w))
    (R : for_all_2_family_prod A A ker_hom a b)
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

  Global Instance congruence_ker_hom : IsCongruence A ker_hom.
  Proof.
    intros u a b R.
    unfold ker_hom.
    repeat rewrite (path_homomorphism_ap_operation f).
    now apply path_ker_hom_ap_operation.
  Qed.
End kernel.

Definition in_im_hom {σ : Signature} {A B : Algebra σ}
  (f : Homomorphism A B) (s : Sort σ) (y : B s) : Type
  := merely (hfiber (f s) y).

Section is_closed_under_ops_im_hom.
  Context `{Funext} {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B).

  Lemma closed_under_op_subalgebra_im_hom {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) (P : OpPreserving f α β)
    : ClosedUnderOp B (in_im_hom f) β.
  Proof.
    induction w.
    - exact (tr (α; P)).
    - intro y.
      refine (Trunc_rec _). intros [x p].
      apply (IHw (α x)).
      now refine (transport (λ y, OpPreserving f (α x) (β y)) p _).
  Defined.

  Global Instance is_closed_under_ops_im_hom
    : IsClosedUnderOps B (in_im_hom f).
  Proof.
    intro u. eapply closed_under_op_subalgebra_im_hom, f.
  Defined.
End is_closed_under_ops_im_hom.

Section first_isomorphism.
  Context
    `{Univalence}
    {σ : Signature}
    {A B : Algebra σ}
    (f : Homomorphism A B).

  Definition def_first_isomorphism (s : Sort σ)
    : (A / ker_hom f) s → (B & in_im_hom f) s.
  Proof.
    refine (
      quotient_rec (ker_hom f s) (λ x : A s, (f s x ; tr (x ; idpath))) _).
    intros x y ?.
    now apply path_sigma_hprop.
  Defined.

  Lemma oppreserving_first_isomorphism {w : SymbolType σ}
    (γ : Operation (A / ker_hom f) w)
    (α : Operation A w) (β : Operation B w)
    (P : OpPreserving f α β)
    (G : QuotientOpProperty A (ker_hom f) α γ)
    : OpPreserving def_first_isomorphism γ
        (op_subalgebra B (in_im_hom f) β
          (closed_under_op_subalgebra_im_hom f α β P)).
  Proof.
    unfold QuotientOpProperty in G.
    induction w.
    - apply path_sigma_hprop.
      generalize dependent γ.
      refine (quotient_ind_prop (ker_hom f t) _ _). intros x G.
      rewrite <- P.
      apply (classes_eq_related (ker_hom f t) _ _ (G tt)).
    - refine (quotient_ind_prop (ker_hom f t) _ _). intro x.
      apply (IHw (γ (class_of (ker_hom f t) x)) (α x) (β (f t x)) (P x)).
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
    : Homomorphism (A / ker_hom f) (B & in_im_hom f)
    := BuildHomomorphism def_first_isomorphism.

  Global Instance injection_first_isomorphism (s : Sort σ)
    : Injective (hom_first_isomorphism s).
  Proof.
    refine (quotient_ind_prop (ker_hom f s) _ _). intro x.
    refine (quotient_ind_prop (ker_hom f s) _ _). intros y p.
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

  Corollary path_first_isomorphism : A / ker_hom f = B & in_im_hom f.
  Proof.
    exact (path_isomorphism hom_first_isomorphism).
  Defined.
End first_isomorphism.
