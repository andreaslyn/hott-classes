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
  HoTT.Basics.Overture.

Import algebra_notations.

Section quotientalgebra.
  Context
    {σ : Signature}
    (A : Algebra σ)
    (Φ : ∀ s, relation (A s))
    `{!∀ s, is_mere_relation (A s) (Φ s)}
    `{!∀ s, Equivalence (Φ s)}
    `{!IsCongruence A Φ}.

  (** If a congruence [Φ] satisfies the [congruence_property f] for
      [f : A s1 → A s2 → ... → A (s(n+1))], then [Φ] satisfies
      the [congruence_property (f x)] for any [x : A s1]. *)
  Lemma congruence_property_cons {s : sort σ} {w : symboltype σ}
      : ∀ (f : Operation A (s ::: w)) (x : A s),
        congruence_property Φ f → congruence_property Φ (f x).
  Proof.
    intros f x P a b R.
    exact (P (x,a) (x,b) (Equivalence_Reflexive x, R)).
  Defined.

  (* The family of sets in the quotient algebra. *)

  Definition carriers_quotientalgebra : Carriers σ := λ s, quotient (Φ s).

  Lemma cprod_for_all_2_reflexive : ∀ w (a : CProd A w), for_all_2_cprod Φ a a.
  Proof.
    induction w; intros.
    - reflexivity.
    - by split.
  Defined.

  (** Specialization of [quotient_ind_prop]. *)

  Fixpoint cprod_quotient_ind_prop `{Funext} {w : list (sort σ)}
      : ∀ (P : CProd carriers_quotientalgebra w -> Type) `{!∀ a, IsHProp (P a)}
          (dclass : ∀ x, P (map_cprod (λ s, class_of (Φ s)) x))
          (a : CProd carriers_quotientalgebra w), P a :=
    match w with
    | nil => λ P sP dclass 'tt, dclass tt
    | s :: w' => λ P _ dclass a,
      quotient_ind_prop (Φ s) (λ a0, ∀ a1, P (a0, a1))
        (λ a0, cprod_quotient_ind_prop
                 (λ c, P (class_of (Φ s) a0, c)) (λ c, dclass (a0, c)))
        (fst a) (snd a)
    end.

  (** Suppose [f : A s1 → A s2 → ... → A sn] is an algebra operation and
      [g : carrier s1 → carrier s2 → ... → carrier sn] is a quotient algebra
      operation. Then [g] has the [quotient_op_property] with respect to [f] if

        [g (class x1) (class x2) ... (class xn) = class (f x1 x2 .. xn)],

      where [class xi] is the quotient algebra equivalence class of [xi]. *)

  Definition quotient_op_property {w : symboltype σ}
    (f : Operation A w) (g : Operation carriers_quotientalgebra w) :=
    ∀ (a : CProd A (dom_symboltype w)),
      apply_cprod g (map_cprod (λ s, class_of (Φ s)) a) =
      class_of (Φ (cod_symboltype w)) (apply_cprod f a).

  (** Quotient algebra operations induced from congruence [Φ]. For each
      operation [algebra_op u] in algebra [A], there is a quotient algebra
      operation [g] satisfying the [quotient_op_property f g] with respect to f. *)

  Fixpoint op_quotientalgebra `{Funext} {w : symboltype σ} :
    ∀ (f : Operation A w),
    congruence_property Φ f ->
    ∃ (g : Operation carriers_quotientalgebra w), quotient_op_property f g.
  Proof. refine (
      match w with
      | [:s] => λ f P, (class_of (Φ s) f; λ a, idpath)
      | s ::: w' => λ f P,
        (quotient_rec (Φ s) (λ x, (op_quotientalgebra _ w' (f x)
                                   (congruence_property_cons f x P)).1) _ ; _)
      end
    ).
    intros [x a].
    apply (op_quotientalgebra _ w' (f x) (congruence_property_cons f x P)).
    Grab Existential Variables.
    intros x y E.
    apply (@path_forall_apply_cprod σ _).
    apply cprod_quotient_ind_prop; try apply _.
    intro a.
    destruct (op_quotientalgebra _ _ _ (congruence_property_cons f x P))
      as [g1 P1].
    destruct (op_quotientalgebra _ _ _ (congruence_property_cons f y P))
      as [g2 P2].
    refine ((P1 a) @ _ @ (P2 a)^).
    apply related_classes_eq.
    exact (P (x,a) (y,a) (E, cprod_for_all_2_reflexive (dom_symboltype w') a)).
  Defined.

  Definition ops_quotientalgebra `{Funext} (u : symbol σ)
    : Operation carriers_quotientalgebra (σ u)
    := (op_quotientalgebra (u^^A) (congruence_property_family A Φ u)).1.

  Definition QuotientAlgebra `{Funext} : Algebra σ
    := BuildAlgebra carriers_quotientalgebra ops_quotientalgebra.
End quotientalgebra.

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

  Definition def_quotient : ∀ s, A s → QuotientAlgebra A Φ s :=
    λ s x, class_of (Φ s) x.

  Lemma oppreserving_quotient `{Funext} (w : symboltype σ)
      (g : Operation (carriers_quotientalgebra A Φ) w) (ao : Operation A w)
      (G : quotient_op_property A Φ ao g)
      : OpPreserving def_quotient ao g.
    unfold quotient_op_property in G.
    induction w; simpl in *.
    - rewrite (G tt). reflexivity.
    - intro x. apply IHw. intro a. apply (G (x,a)).
  Qed.

  Global Instance ishomomorphism_quotient `{Funext}
    : IsHomomorphism def_quotient.
  Proof.
    intro u.
    apply oppreserving_quotient, op_quotientalgebra.
  Qed.

  Definition hom_quotient : Homomorphism A (QuotientAlgebra A Φ)
    := BuildHomomorphism def_quotient.

  Global Instance surjection_quotient : ∀ s, IsSurjection (hom_quotient s).
  Proof.
    intro s. apply quotient_surjective.
  Defined.
End hom_quotient.

(** This section develops the universal mapping property [quotient_property]
    of the quotient algebra. *)

Section quotient_property.
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
    algebra satisfynig [quotient_property_mapout_compute] below. *)

  Section quotient_property_mapout.
    Context
      (f : Homomorphism A B)
      (R : ∀ s x y, Φ s x y → f s x = f s y).

    Definition def_quotient_property_mapout : ∀ s, QuotientAlgebra A Φ s → B s
      := λ (s : sort σ), (quotient_ump (Φ s) (BuildhSet (B s)))^-1 (f s; R s).

    Lemma quotient_property_mapout_preservation {w : symboltype σ}
        (g : Operation (QuotientAlgebra A Φ) w)
        (ao : Operation A w) (bo : Operation B w)
        (G : quotient_op_property A Φ ao g) (P : OpPreserving f ao bo)
        : OpPreserving def_quotient_property_mapout g bo.
    Proof.
      unfold quotient_op_property in G.
      induction w; simpl in *.
      - rewrite (G tt). apply P.
      - refine (quotient_ind_prop (Φ t) _ _).
        intro x.
        apply (IHw (g (class_of (Φ t) x)) (ao x) (bo (f t x))).
        + intro a. apply (G (x,a)).
        + apply P.
    Qed.

    Global Instance quotient_property_mapout_homomorphism
      : IsHomomorphism def_quotient_property_mapout.
    Proof.
      intro u.
      eapply quotient_property_mapout_preservation.
      - apply op_quotientalgebra.
      - apply f.
    Qed.

    Definition hom_quotient_property_mapout
      : Homomorphism (QuotientAlgebra A Φ) B
      := BuildHomomorphism def_quotient_property_mapout.

    (** The computation rule for the homomorphism [g : ∀ s, carrier σ Φ s → B s]
        defined by the [quotient_property_mapout] is

          [g s (class x) = f s x],

        where [class x] is the quotient algebra equivalence class of [x]. *)

    Lemma quotient_property_mapout_compute
      : ∀ s (x : A s), hom_quotient_property_mapout s (class_of (Φ s) x) = f s x.
    Proof. reflexivity. Defined.

  End quotient_property_mapout.

  (** Suppose [g : ∀ s, carrier σ Φ s → B s] is a homomorphism out of the
      quotient algebra. There is a homomorphism [λ s, g s ∘ hom_quotient σ Φ s]
      factoring through the [hom_quotient] and [g]. *)

  Definition hom_quotient_property_factoring
    (g : Homomorphism (QuotientAlgebra A Φ) B)
    : Homomorphism A B
    := BuildHomomorphism (λ s, g s ∘ hom_quotient A Φ s).

  (** The left to right direction of the quotient algebra universal mapping
      property [quotient_property]. The resulting homomorphism [g] is given by
      the [quotient_property_mapout] above. *)

  Lemma quotient_peoperty_rl :
    (∃ (f : Homomorphism A B), ∀ s x y, Φ s x y → f s x = f s y) →
    Homomorphism (QuotientAlgebra A Φ) B.
  Proof.
    intros [f P].
    exists (hom_quotient_property_mapout f P).
    apply _.
  Defined.

  (** The right to left direction of the quotient algebra universal mapping
      property [quotient_property]. The resulting homomorphism [f] is given by
      the [quotient_property_factoring] above. The homomorphism [f] respects the
      congruence [Φ]. *)

  Lemma quotient_property_lr :
    Homomorphism (QuotientAlgebra A Φ) B →
    ∃ (f : Homomorphism A B), ∀ s x y, Φ s x y → f s x = f s y.
  Proof.
    intro g.
    refine ((hom_quotient_property_factoring g ; _)).
    intros s x y E.
    exact (transport (λ z, g s (class_of (Φ s) x) = g s z)
            (related_classes_eq (Φ s) E) idpath).
  Defined.

  (** The universal property of the quotient algebra. For each homomorphism
      [f : ∀ s, A s → B s] respecting the congruence [Φ], there is a unique
      homomorphism [g : ∀ s, carrier σ Φ s → B s] out of the quotient algebra.
      In one direction, the homomorphism [g] is given by the
      [quotient_property_mapout]. In the other direction, the homomorphism [f]
      is given by the [quotient_property_factoring]. *)

  Lemma quotient_property
    : Homomorphism (QuotientAlgebra A Φ) B
     <~>
      ∃ (f : Homomorphism A B), ∀ s (x y : A s), Φ s x y → f s x = f s y.
  Proof.
    apply (equiv_adjointify quotient_property_lr quotient_peoperty_rl).
    - intros [[f F] P].
      repeat apply path_sigma_hprop.
      funext s.
      now apply path_forall.
    - intros [g G].
      apply path_sigma_hprop.
      funext s.
      refine (eissect (quotient_ump (Φ s) (BuildhSet (B s))) (g s)).
  Defined.
End quotient_property.
