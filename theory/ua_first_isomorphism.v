(** This files proves the first isomorphism theorem. *)

Require Import
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.canonical_names
  HoTTClasses.theory.ua_homomorphism
  HoTTClasses.theory.ua_subalgebra
  HoTTClasses.theory.ua_quotient_algebra.

Import algebra_notations quotient_algebra_notations subalgebra_notations.

(** The following section defines the kernel of a homomorphism [cong_ker]. *)

Section cong_ker.
  Context
    {σ : Signature} {A B : Algebra σ} `{IsHSetAlgebra B}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f}.

  Definition cong_ker (s : Sort σ) : relation (A s)
    := λ (x y : A s), f s x = f s y.

  Global Instance equiv_rel_ker (s : Sort σ)
    : EquivRel (cong_ker s).
  Proof.
   repeat constructor.
   - intros x y h. exact (h^ @ idpath).
   - intros x y z h1 h2. exact (h1 @ h2).
  Defined.

  Lemma path_ap_operation_ker_related {w : SymbolType σ}
    (β : Operation B w) (a b : FamilyProd A (dom_symboltype w))
    (R : for_all_2_family_prod A A cong_ker a b)
    : ap_operation β (map_family_prod f a)
      = ap_operation β (map_family_prod f b).
  Proof.
    induction w.
    - reflexivity.
    - destruct a as [x a], b as [y b], R as [r R].
      cbn. destruct r. by apply IHw.
  Defined.

  Global Instance ops_compatible_ker
    : OpsCompatible A cong_ker.
  Proof.
    intros u a b R.
    unfold cong_ker.
    destruct (path_homomorphism_ap_operation f u a)^.
    destruct (path_homomorphism_ap_operation f u b)^.
    by apply path_ap_operation_ker_related.
  Defined.

  Global Instance is_congruence_ker : IsCongruence A cong_ker
    := BuildIsCongruence A cong_ker.

End cong_ker.

(** The next section defines an "in homomorphic image predicate"
    [in_image_hom]. *)

Section subalgebra_predicate_in_image_hom.
  Context
    `{Funext} {σ : Signature} {A B : Algebra σ}
    (f : ∀ s, A s → B s) {ishom : IsHomomorphism f}.

  Definition in_image_hom (s : Sort σ) (y : B s) : hProp
    := merely (hfiber (f s) y).

  Lemma closed_under_op_in_image_hom {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) (P : OpPreserving f α β)
    : ClosedUnderOp B in_image_hom β.
  Proof.
    induction w.
    - exact (tr (α; P)).
    - intro y.
      refine (Trunc_rec _). intros [x p].
      apply (IHw (α x)).
      now refine (transport (λ y, OpPreserving f (α x) (β y)) p _).
  Qed.

  Global Instance is_closed_under_ops_in_image_hom
    : IsClosedUnderOps B in_image_hom.
  Proof.
    intro u. eapply closed_under_op_in_image_hom, ishom.
  Qed.

End subalgebra_predicate_in_image_hom.

(** The first isomorphism theorem. *)

Section first_isomorphism.
  Context
    `{Univalence} {σ} {A B : Algebra σ} `{IsHSetAlgebra B}
    (f : ∀ s, A s → B s) {ishom : IsHomomorphism f}.

  Definition def_first_isomorphism (s : Sort σ)
    : (A / cong_ker f) s → (B & in_image_hom f) s.
  Proof.
    refine (quotient_rec (cong_ker f s) (λ x, (f s x; tr (x; idpath))) _).
    intros x y ?.
    now apply path_sigma_hprop.
  Defined.

  Lemma oppreserving_first_isomorphism {w : SymbolType σ}
    (α : Operation A w)
    (β : Operation B w)
    (γ : Operation (A / cong_ker f) w)
    (C : ClosedUnderOp B (in_image_hom f) β)
    (P : OpPreserving f α β)
    (G : ComputeOpQuotient A (cong_ker f) α γ)
    : OpPreserving def_first_isomorphism γ
        (op_subalgebra B (in_image_hom f) β C).
  Proof.
    induction w.
    - apply path_sigma_hprop.
      generalize dependent γ.
      refine (quotient_ind_prop (cong_ker f t) _ _). intros x G.
      destruct P.
      apply (classes_eq_related (cong_ker f t) _ _ (G tt)).
    - refine (quotient_ind_prop (cong_ker f t) _ _). intro x.
      apply (IHw (α x) (β (f t x)) (γ (class_of (cong_ker f t) x))).
      + exact (P x).
      + intro a. exact (G (x,a)).
  Defined.

  Global Instance is_homomorphism_first_isomorphism
    : IsHomomorphism def_first_isomorphism.
  Proof.
    intro u.
    apply (oppreserving_first_isomorphism (u^^A)).
    - apply ishom.
    - apply compute_op_quotient.
  Defined.

  Definition hom_first_isomorphism
    : Homomorphism (A / cong_ker f) (B & in_image_hom f)
    := BuildHomomorphism def_first_isomorphism.

  Global Instance embedding_first_isomorphism (s : Sort σ)
    : IsEmbedding (hom_first_isomorphism s).
  Proof.
    intro z.
    apply ishprop_sigma_disjoint.
    refine (quotient_ind_prop (cong_ker f s) _ _). intro x.
    refine (quotient_ind_prop (cong_ker f s) _ _). intros y p1 p2.
    apply related_classes_eq.
    unfold cong_ker.
    exact ((p1 @ p2^)..1).
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
    intro s. apply isequiv_surj_emb; exact _.
  Qed.

  Global Existing Instance is_isomorphism_first_isomorphism.

  Corollary path_first_isomorphism : A / cong_ker f = B & in_image_hom f.
  Proof.
    exact (path_isomorphism hom_first_isomorphism).
  Qed.
End first_isomorphism.

(** A version of the first isomorphism theorem where the homomorphism
    is surjective. *)

Section first_isomorphism_surjection.
  Context
    `{Univalence} {σ} {A B : Algebra σ} `{IsHSetAlgebra B}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f} {Su : ∀ s, IsSurjection (f s)}.

  Global Instance is_isomorphism_inc_first_isomorphism_surjection
    : IsIsomorphism (hom_inc_subalgebra B (in_image_hom f)).
  Proof.
    apply @is_isomorphism_inc_improper_subalgebra; [exact _|].
    intros s y.
    destruct (Su s y) as [p P].
    refine (Trunc_rec _ p).
    intros [y' Y'].
    apply tr.
    by exists y'.
  Qed.

  Definition hom_first_isomorphism_surjection
    : Homomorphism (A / cong_ker f) B
    := hom_compose
          (hom_inc_subalgebra B (in_image_hom f))
          (hom_first_isomorphism f).

  Corollary path_first_isomorphism_surjection : (A / cong_ker f) = B.
  Proof.
    exact (path_isomorphism hom_first_isomorphism_surjection).
  Defined.
End first_isomorphism_surjection.
