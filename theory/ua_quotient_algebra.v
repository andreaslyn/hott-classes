Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Arrow
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.Spaces.Nat
  HoTT.HIT.quotient
  HoTT.Classes.implementations.list
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.interfaces.relation
  HoTTClasses.interfaces.ua_congruence
  HoTTClasses.theory.ua_homomorphism
  HoTTClasses.theory.ua_subalgebra.

Import algebra_notations ne_list.notations.

Section quotient_algebra.
  Context {σ : Signature} (A : Algebra σ) (Φ : Congruence A).

  (* The family of sets in the quotient algebra. *)

  Definition carriers_quotient_algebra : Carriers σ
    := λ s, quotient (Φ s).

  (** Specialization of [quotient_ind_prop]. *)

  Fixpoint quotient_ind_prop_family_prod `{Funext} {w : list (Sort σ)}
    : ∀ (P : FamilyProd carriers_quotient_algebra w -> Type)
        `{!∀ a, IsHProp (P a)}
        (dclass : ∀ x, P (map_family_prod (λ s, class_of (Φ s)) x))
        (a : FamilyProd carriers_quotient_algebra w), P a
    := match w with
       | nil => λ P _ dclass 'tt, dclass tt
       | s :: w' => λ P a dclass a,
         quotient_ind_prop (Φ s) (λ a, ∀ b, P (a,b))
           (λ a, quotient_ind_prop_family_prod
                  (λ c, P (class_of (Φ s) a, c)) (λ c, dclass (a, c)))
           (fst a) (snd a)
       end.

  Definition QuotientOpProperty {w : SymbolType σ}
    (f : Operation A w) (g : Operation carriers_quotient_algebra w)
    : Type
    := ∀ (a : FamilyProd A (dom_symboltype w)),
         ap_operation g (map_family_prod (λ s, class_of (Φ s)) a)
         = class_of (Φ (cod_symboltype w)) (ap_operation f a).

  Local Notation Ξ w :=
    (∀ (f : Operation A w),
     CongruenceProperty A Φ f →
     ∃ g : Operation carriers_quotient_algebra w,
     QuotientOpProperty f g).

  Lemma op_quotient_algebra_well_def `{Funext}
    (q : ∀ (w : SymbolType σ), Ξ w)
    (s : Sort σ) (w : SymbolType σ) (f : Operation A (s ::: w))
    (P : CongruenceProperty A Φ f) (x y : A s) (C : Φ s x y)
    : (q w (f x) (congruence_property_cons Φ f x P)).1
      = (q w (f y) (congruence_property_cons Φ f y P)).1.
  Proof.
    apply (@path_forall_ap_operation _ σ).
    apply quotient_ind_prop_family_prod; try exact _.
    intro a.
    destruct (q _ _ (congruence_property_cons Φ f x P)) as [g1 P1].
    destruct (q _ _ (congruence_property_cons Φ f y P)) as [g2 P2].
    refine ((P1 a) @ _ @ (P2 a)^).
    apply related_classes_eq.
    exact (P (x,a) (y,a) (C, reflexive_for_all_2_family_prod A Φ a)).
  Defined.

  Fixpoint op_quotient_algebra `{Funext} {w : SymbolType σ} : Ξ w.
  Proof. refine (
      match w return Ξ w with
      | [:s:] => λ (f : A s) P, (class_of (Φ s) f; λ a, idpath)
      | s ::: w' => λ (f : A s → Operation A w') P,
        (quotient_rec (Φ s)
          (λ (x : A s), (op_quotient_algebra _ w' (f x)
                            (congruence_property_cons Φ f x P)).1)
          (op_quotient_algebra_well_def
              (op_quotient_algebra _) s w' f P)
        ; _)
      end
    ).
    intros [x a].
    apply (op_quotient_algebra _ w' (f x)
             (congruence_property_cons Φ f x P)).
  Defined.

  Definition ops_quotient_algebra `{Funext} (u : Symbol σ)
    : Operation carriers_quotient_algebra (σ u)
    := (op_quotient_algebra (u^^A) (property_congruence Φ u)).1.

  Definition QuotientAlgebra `{Funext} : Algebra σ
    := BuildAlgebra carriers_quotient_algebra ops_quotient_algebra.

  Global Instance hset_quotient_algebra `{Funext}
    : IsHSetAlgebra QuotientAlgebra.
  Proof.
    intro s. exact _.
  Defined.

  Lemma quotient_op_property `{Funext} (u : Symbol σ)
    : QuotientOpProperty (u^^A) (operations QuotientAlgebra u).
  Proof.
    apply op_quotient_algebra.
  Defined.
End quotient_algebra.

Module quotient_algebra_notations.

  Global Notation "A / Φ" := (QuotientAlgebra A Φ)
                             (at level 40, left associativity)
                             : Algebra_scope.

End quotient_algebra_notations.

Import quotient_algebra_notations.

Section hom_quotient.
  Context `{Funext} {σ} {A : Algebra σ} (Φ : Congruence A).
  
  Definition def_quotient : ∀ (s : Sort σ), A s → (A/Φ) s :=
    λ s x, class_of (Φ s) x.

  Lemma oppreserving_quotient `{Funext} (w : SymbolType σ)
      (g : Operation (A/Φ) w) (α : Operation A w)
      (G : QuotientOpProperty A Φ α g)
      : OpPreserving def_quotient α g.
    unfold QuotientOpProperty in G.
    induction w; simpl in *.
    - rewrite (G tt). reflexivity.
    - intro x. apply IHw. intro a. apply (G (x,a)).
  Qed.

  Definition is_homomorphism_quotient `{Funext}
    : IsHomomorphism def_quotient.
  Proof.
    intro u.
    apply oppreserving_quotient, quotient_op_property.
  Qed.

  Definition hom_quotient : Homomorphism A (A/Φ)
    := BuildHomomorphism def_quotient is_homomorphism_quotient.

  Global Instance surjection_quotient
    : ∀ s, IsSurjection (hom_quotient s).
  Proof.
    intro s. apply quotient_surjective.
  Qed.
End hom_quotient.

(** This section develops the universal mapping property
    [ump_quotient_algebra] of the quotient algebra. *)

Section ump_quotient_algebra.
  Context
    `{Univalence}
    {σ : Signature}
    {A B : Algebra σ}
    `{!IsHSetAlgebra B}
    (Φ : Congruence A).

(** In the nested section below we show that for [f : Homomorphism A B]
    respecting the congruence [Φ], there is a homomorphism
    [Homomorphism (A/Φ) B] out of the quotient algebra satisfying
    [compute_ump_quotient_algebra_mapout] below. *)

  Section ump_quotient_algebra_mapout.
    Context
      (f : Homomorphism A B)
      (R : ∀ s (x y : A s), Φ s x y → f s x = f s y).

    Definition def_ump_quotient_algebra_mapout
      : ∀ (s : Sort σ), (A/Φ) s → B s
      := λ s, (quotient_ump (Φ s) (BuildhSet (B s)))^-1 (f s; R s).

    Lemma oppreserving_ump_quotient_algebra_mapout {w : SymbolType σ}
        (g : Operation (A/Φ) w)
        (α : Operation A w) (β : Operation B w)
        (G : QuotientOpProperty A Φ α g) (P : OpPreserving f α β)
        : OpPreserving def_ump_quotient_algebra_mapout g β.
    Proof.
      unfold QuotientOpProperty in G.
      induction w; simpl in *.
      - rewrite (G tt). apply P.
      - refine (quotient_ind_prop (Φ t) _ _). intro x.
        apply (IHw (g (class_of (Φ t) x)) (α x) (β (f t x))).
        + intro a. apply (G (x,a)).
        + apply P.
    Qed.

    Definition is_homomorphism_ump_quotient_algebra_mapout
      : IsHomomorphism def_ump_quotient_algebra_mapout.
    Proof.
      intro u.
      eapply oppreserving_ump_quotient_algebra_mapout.
      - apply quotient_op_property.
      - apply f.
    Qed.

    Definition hom_ump_quotient_algebra_mapout
      : Homomorphism (A/Φ) B
      := BuildHomomorphism
          def_ump_quotient_algebra_mapout
          is_homomorphism_ump_quotient_algebra_mapout.

(** The computation rule for [hom_ump_quotient_algebra_mapout] is

<<
      [g s (class x) = f s x],
>>

    where [class x] is the equivalence class of [x]. *)

    Lemma compute_ump_quotient_algebra_mapout
      : ∀ (s : Sort σ) (x : A s),
        hom_ump_quotient_algebra_mapout s (class_of (Φ s) x) = f s x.
    Proof.
      reflexivity.
    Defined.

  End ump_quotient_algebra_mapout.

(** Suppose [g : Homomorphism (A/Φ) B] is a homomorphism out of the
    quotient algebra. There is a homomorphism induced by the family of
    functions [λ s, g s ∘ hom_quotient σ Φ s]. *)

  Definition hom_ump_quotient_algebra_factoring (g : Homomorphism (A/Φ) B)
    : Homomorphism A B
    := hom_compose g (hom_quotient Φ).

  Lemma ump_quotient_algebra_lr :
    (∃ (f : Homomorphism A B), ∀ s (x y : A s), Φ s x y → f s x = f s y)
    → Homomorphism (A/Φ) B.
  Proof.
    intros [f P].
    exists (hom_ump_quotient_algebra_mapout f P).
    apply is_homomorphism_ump_quotient_algebra_mapout.
  Defined.

  Lemma ump_quotient_algebra_rl :
    Homomorphism (A/Φ) B →
    ∃ (f : Homomorphism A B), ∀ s (x y : A s), Φ s x y → f s x = f s y.
  Proof.
    intro g.
    refine ((hom_ump_quotient_algebra_factoring g ; _)).
    intros s x y E.
    exact (transport (λ z, g s (class_of (Φ s) x) = g s z)
            (related_classes_eq (Φ s) E) idpath).
  Defined.

(** The universal property of the quotient algebra. For each homomorphism
    [f : Homomorphism A B] respecting the congruence [Φ], there is a unique
    homomorphism [g : Homomorphism (A/Φ) B] out of the quotient algebra. *)

  Lemma ump_quotient_algebra
    : (∃ (f : Homomorphism A B), ∀ s (x y : A s), Φ s x y → f s x = f s y)
     <~>
      Homomorphism (A/Φ) B.
  Proof.
    apply (equiv_adjointify
             ump_quotient_algebra_lr ump_quotient_algebra_rl).
    - intro G.
      apply path_hset_homomorphism.
      funext s.
      exact (eissect (quotient_ump (Φ s) _) (G s)).
    - intro F.
      apply path_sigma_hprop.
      by apply path_hset_homomorphism.
  Defined.
End ump_quotient_algebra.
