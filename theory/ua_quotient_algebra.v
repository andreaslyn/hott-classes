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
  HoTT.Basics.Overture.

Import algebra_notations ne_list.notations.

Section quotient_algebra.
  Context
    {σ : Signature}
    (A : Algebra σ)
    (Φ : ∀ s, relation (A s))
    `{!∀ s, is_mere_relation (A s) (Φ s)}
    `{!∀ s, Equivalence (Φ s)}
    `{!IsCongruence A Φ}.

  (** If a congruence [Φ] satisfies the [CongruenceProperty f] for
      [f : A s1 → A s2 → ... → A (s(n+1))], then [Φ] satisfies
      the [CongruenceProperty (f x)] for any [x : A s1]. *)
  Lemma congruence_property_cons {s : Sort σ} {w : SymbolType σ}
      : ∀ (f : Operation A (s ::: w)) (x : A s),
        CongruenceProperty Φ f → CongruenceProperty Φ (f x).
  Proof.
    intros f x P a b R.
    exact (P (x,a) (x,b) (Equivalence_Reflexive x, R)).
  Defined.

  (* The family of sets in the quotient algebra. *)

  Definition carriers_quotient_algebra : Carriers σ := λ s, quotient (Φ s).

  (** Specialization of [quotient_ind_prop]. *)

  Fixpoint quotient_ind_prop_family_prod `{Funext} {w : list (Sort σ)}
      : ∀ (P : FamilyProd carriers_quotient_algebra w -> Type)
          `{!∀ a, IsHProp (P a)}
          (dclass : ∀ x, P (map_family_prod (λ s, class_of (Φ s)) x))
          (a : FamilyProd carriers_quotient_algebra w), P a :=
    match w with
    | nil => λ P _ dclass 'tt, dclass tt
    | s :: w' => λ P _ dclass a,
      quotient_ind_prop (Φ s) (λ a0, ∀ a1, P (a0, a1))
        (λ a0, quotient_ind_prop_family_prod
                 (λ c, P (class_of (Φ s) a0, c)) (λ c, dclass (a0, c)))
        (fst a) (snd a)
    end.

  (** Suppose [f : A s1 → A s2 → ... → A sn] is an algebra operation and
      [g : carrier s1 → carrier s2 → ... → carrier sn] is a quotient algebra
      operation. Then [g] has the [QuotientOpProperty] with respect to [f] if

        [g (class x1) (class x2) ... (class xn) = class (f x1 x2 .. xn)],

      where [class xi] is the quotient algebra equivalence class of [xi]. *)

  Definition QuotientOpProperty {w : SymbolType σ}
    (f : Operation A w) (g : Operation carriers_quotient_algebra w) : Type
    := ∀ (a : FamilyProd A (dom_symboltype w)),
         ap_operation g (map_family_prod (λ s, class_of (Φ s)) a) =
           class_of (Φ (cod_symboltype w)) (ap_operation f a).

  Lemma op_quotient_algebra_unique `{Funext}
    (q : ∀ (w : SymbolType σ) (f : Operation A w),
         CongruenceProperty Φ f →
         ∃ g : Operation carriers_quotient_algebra w, QuotientOpProperty f g)
    (s : Sort σ) (w : SymbolType σ) (f : Operation A (s ::: w))
    (P : CongruenceProperty Φ f) (x y : A s) (C : Φ s x y)
    : (q w (f x) (congruence_property_cons f x P)).1
      = (q w (f y) (congruence_property_cons f y P)).1.
  Proof.
    apply (@path_forall_ap_operation _ σ).
    apply quotient_ind_prop_family_prod; try exact _.
    intro a.
    destruct (q _ _ (congruence_property_cons f x P)) as [g1 P1].
    destruct (q _ _ (congruence_property_cons f y P)) as [g2 P2].
    refine ((P1 a) @ _ @ (P2 a)^).
    apply related_classes_eq.
    exact (P (x,a) (y,a) (C, reflexive_for_all_2_family_prod A Φ a)).
  Defined.

  (** Quotient algebra operations induced from congruence [Φ]. For each
      operation [algebra_op u] in algebra [A], there is a quotient algebra
      operation [g] satisfying the [QuotientOpProperty f g] with respect to f. *)

  Fixpoint op_quotient_algebra `{Funext} {w : SymbolType σ}
    : ∀ (f : Operation A w),
      CongruenceProperty Φ f ->
      ∃ (g : Operation carriers_quotient_algebra w), QuotientOpProperty f g.
  Proof. refine (
      match w with
      | [:s:] => λ (f : A s) P, (class_of (Φ s) f; λ a, idpath)
      | s ::: w' => λ (f : A s → Operation A w') P,
        (quotient_rec (Φ s)
          (λ (x : A s),
            (op_quotient_algebra _ w' (f x) (congruence_property_cons f x P)).1)
          (op_quotient_algebra_unique (op_quotient_algebra _) s w' f P)
        ; _)
      end
    ).
    intros [x a].
    apply (op_quotient_algebra _ w' (f x) (congruence_property_cons f x P)).
  Defined.

  Definition ops_quotient_algebra `{Funext} (u : Symbol σ)
    : Operation carriers_quotient_algebra (σ u)
    := (op_quotient_algebra (u^^A) (congruence_properties A Φ u)).1.

  Definition QuotientAlgebra `{Funext} : Algebra σ
    := BuildAlgebra carriers_quotient_algebra ops_quotient_algebra.

  Lemma quotient_op_property_quotient_algebra `{Funext} (u : Symbol σ)
    : QuotientOpProperty (u^^A) (operations QuotientAlgebra u).
  Proof.
    apply op_quotient_algebra.
  Defined.
End quotient_algebra.

Module quotient_algebra_notations.
  Global Notation "A / Φ" := (QuotientAlgebra A Φ) (at level 40, left associativity)
    : Algebra_scope.
End quotient_algebra_notations.

Import quotient_algebra_notations.

(** This section defines the quotient homomorphism [hom_quotient] satisfying

      [hom_quotient _ x = class x],

    where [class x] is the quotient algebra equivalence class of [x]. *)

Section hom_quotient.
  Context
    `{Funext}
    {σ : Signature}
    (A : Algebra σ)
    (Φ : ∀ s, relation (A s))
    `{!∀ s, is_mere_relation _ (Φ s)}
    `{!∀ s, Equivalence (Φ s)}
    `{!IsCongruence A Φ}.
  
  Definition def_quotient : ∀ s, A s → (A/Φ) s :=
    λ s x, class_of (Φ s) x.

  Lemma oppreserving_quotient `{Funext} (w : SymbolType σ)
      (g : Operation (A/Φ) w) (ao : Operation A w)
      (G : QuotientOpProperty A Φ ao g)
      : OpPreserving def_quotient ao g.
    unfold QuotientOpProperty in G.
    induction w; simpl in *.
    - rewrite (G tt). reflexivity.
    - intro x. apply IHw. intro a. apply (G (x,a)).
  Qed.

  Global Instance is_homomorphism_quotient `{Funext}
    : IsHomomorphism def_quotient.
  Proof.
    intro u.
    apply oppreserving_quotient, quotient_op_property_quotient_algebra.
  Qed.

  Definition hom_quotient : Homomorphism A (A/Φ)
    := BuildHomomorphism def_quotient.

  Global Instance surjection_quotient : ∀ s, IsSurjection (hom_quotient s).
  Proof.
    intro s. apply quotient_surjective.
  Defined.
End hom_quotient.

(** This section develops the universal mapping property [ump_quotient_algebra]
    of the quotient algebra. *)

Section ump_quotient_algebra.
  Context
    `{Univalence}
    {σ : Signature}
    {A B : Algebra σ}
    (Φ : ∀ s, relation (A s))
    `{!∀ s, is_mere_relation (A s) (Φ s)}
    `{!∀ s, Equivalence (Φ s)}
    `{!IsCongruence A Φ}.

(** Given a homomorphism [f : ∀ s, A s → B s] respecting the congruence [Φ],
    there is a homomorphism [g : ∀ s, carrier σ Φ s → B s] out of the quotient
    algebra satisfynig [ump_quotient_algebra_mapout_compute] below. *)

  Section ump_quotient_algebra_mapout.
    Context
      (f : Homomorphism A B)
      (R : ∀ s x y, Φ s x y → f s x = f s y).

    Definition def_ump_quotient_algebra_mapout : ∀ s, (A/Φ) s → B s
      := λ (s : Sort σ), (quotient_ump (Φ s) (BuildhSet (B s)))^-1 (f s; R s).

    Lemma ump_quotient_algebra_mapout_preservation {w : SymbolType σ}
        (g : Operation (A/Φ) w)
        (ao : Operation A w) (bo : Operation B w)
        (G : QuotientOpProperty A Φ ao g) (P : OpPreserving f ao bo)
        : OpPreserving def_ump_quotient_algebra_mapout g bo.
    Proof.
      unfold QuotientOpProperty in G.
      induction w; simpl in *.
      - rewrite (G tt). apply P.
      - refine (quotient_ind_prop (Φ t) _ _).
        intro x.
        apply (IHw (g (class_of (Φ t) x)) (ao x) (bo (f t x))).
        + intro a. apply (G (x,a)).
        + apply P.
    Qed.

    Global Instance ump_quotient_algebra_mapout_homomorphism
      : IsHomomorphism def_ump_quotient_algebra_mapout.
    Proof.
      intro u.
      eapply ump_quotient_algebra_mapout_preservation.
      - apply quotient_op_property_quotient_algebra.
      - apply f.
    Qed.

    Definition hom_ump_quotient_algebra_mapout
      : Homomorphism (A/Φ) B
      := BuildHomomorphism def_ump_quotient_algebra_mapout.

    (** The computation rule for the homomorphism [g : ∀ s, carrier σ Φ s → B s]
        defined by the [ump_quotient_algebra_mapout] is

          [g s (class x) = f s x],

        where [class x] is the quotient algebra equivalence class of [x]. *)

    Lemma ump_quotient_algebra_mapout_compute
      : ∀ s (x : A s),
        hom_ump_quotient_algebra_mapout s (class_of (Φ s) x) = f s x.
    Proof. reflexivity. Defined.

  End ump_quotient_algebra_mapout.

  (** Suppose [g : ∀ s, carrier σ Φ s → B s] is a homomorphism out of the
      quotient algebra. There is a homomorphism [λ s, g s ∘ hom_quotient σ Φ s]
      factoring through the [hom_quotient] and [g]. *)

  Definition hom_ump_quotient_algebra_factoring (g : Homomorphism (A/Φ) B)
    : Homomorphism A B
    := BuildHomomorphism (λ s, g s ∘ hom_quotient A Φ s).

  (** The left to right direction of the quotient algebra universal mapping
      property [ump_quotient_algebra]. The resulting homomorphism [g] is given by
      the [ump_quotient_algebra_mapout] above. *)

  Lemma ump_quotient_algebra_rl :
    (∃ (f : Homomorphism A B), ∀ s x y, Φ s x y → f s x = f s y) →
    Homomorphism (A/Φ) B.
  Proof.
    intros [f P].
    exists (hom_ump_quotient_algebra_mapout f P).
    exact _.
  Defined.

  (** The right to left direction of the quotient algebra universal mapping
      property [ump_quotient_algebra]. The resulting homomorphism [f] is given by
      the [ump_quotient_algebra_factoring] above. The homomorphism [f] respects the
      congruence [Φ]. *)

  Lemma ump_quotient_algebra_lr :
    Homomorphism (A/Φ) B →
    ∃ (f : Homomorphism A B), ∀ s x y, Φ s x y → f s x = f s y.
  Proof.
    intro g.
    refine ((hom_ump_quotient_algebra_factoring g ; _)).
    intros s x y E.
    exact (transport (λ z, g s (class_of (Φ s) x) = g s z)
            (related_classes_eq (Φ s) E) idpath).
  Defined.

  (** The universal property of the quotient algebra. For each homomorphism
      [f : ∀ s, A s → B s] respecting the congruence [Φ], there is a unique
      homomorphism [g : ∀ s, carrier σ Φ s → B s] out of the quotient algebra.
      In one direction, the homomorphism [g] is given by the
      [ump_quotient_algebra_mapout]. In the other direction, the homomorphism [f]
      is given by the [ump_quotient_algebra_factoring]. *)

  Lemma ump_quotient_algebra
    : Homomorphism (A/Φ) B
     <~>
      ∃ (f : Homomorphism A B), ∀ s (x y : A s), Φ s x y → f s x = f s y.
  Proof.
    apply (equiv_adjointify ump_quotient_algebra_lr ump_quotient_algebra_rl).
    - intros F.
      apply path_sigma_hprop.
      apply path_homomorphism.
      funext s.
      now apply path_forall.
    - intros G.
      apply path_homomorphism.
      funext s.
      refine (eissect (quotient_ump (Φ s) (BuildhSet (B s))) (G s)).
  Defined.
End ump_quotient_algebra.
