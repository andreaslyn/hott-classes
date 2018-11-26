Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_basic
  HoTTClasses.theory.ua_homomorphisms
  HoTT.Classes.interfaces.canonical_names
  HoTTClasses.theory.ua_subalgebra
  HoTT.HIT.quotient
  HoTT.Types.Arrow
  HoTT.Types.Forall
  Classes.implementations.list
  HoTT.Spaces.Nat
  HoTT.Basics.Equivalences
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTTClasses.interfaces.ua_basic.

Import ne_list.notations.

(** The following section implements a datatype [argprod] intended to represent
    a product/tuple of algebra operation arguments. Suppose [σ : Signature] is
    a signature and [A : sorts σ → Type] an algebra. An algebra operation
    [f := algebra_op u] has type [f : op_type A (σ u)], for [u : operation σ] a
    function symbol. The type [op_type A (σ u)] is a curried function type
    [A s1 -> A s2 -> ... -> A sn], where [[s1,s2,...,sn] = σ u] (or the type of
    a constant when length of [σ u] is 1). The [argprod_apply] function below
    can be used to uncurry [f], so that

      [argprod_apply f (x1,x2,...,xn) = f x1 x2 ... xn]. *)

Section argprod.
  Context (σ : Signature).

  (** A product type [argprod A [s1,s2,...,sn] = A s1 * A s2 * ... * A sn]. *)

  Fixpoint argprod (A : sorts σ → Type) (w : list (sorts σ)) : Type :=
    match w with
    | nil => Unit
    | s :: w' => A s * argprod A w'
    end.

  (** Map function for [argprod]

        [argprod_map f (x1,x2,...,xn) = (f x1, f x2, ..., f xn)]. *)

  Fixpoint argprod_map {A : sorts σ → Type} {B : sorts σ → Type}
      {w : list (sorts σ)} (f : ∀ s, A s → B s)
      : argprod A w → argprod B w :=
    match w with
    | nil => const tt
    | s :: w' => λ '(x,l), (f s x, argprod_map f l)
    end.

  (** Test whether [P s1 x1 ∧ P s2 x2 ∧ ... ∧ P sn xn] holds, where
      [(x1,...,xn) : A s1 * A s2 * ... * S xn]. *)

  Fixpoint argprod_for_all {A : sorts σ → Type} {w : list (sorts σ)}
      (P : ∀ s, A s -> Type) : argprod A w → Type :=
    match w with
    | nil => λ _, True
    | s :: w' => λ '(x,l), P s x * argprod_for_all P l
    end.

  (** Test whether [R s1 x1 y1 ∧ R s2 x2 y2 ∧ ... ∧ P sn xn yn] holds, where
      [(x1,...,xn) : A s1 * A s2 * ... * S xn] and
      [(y1,...,yn) : B s1 * B s2 * ... * B xn] *)

  Fixpoint argprod_for_all_2 {A B : sorts σ → Type} {w : list (sorts σ)}
      (R : ∀ s, A s -> B s -> Type) : argprod A w → argprod B w → Type :=
    match w with
    | nil => λ _ _, True
    | s :: w' => λ '(x1,l1) '(x2,l2), R s x1 x2 * argprod_for_all_2 R l1 l2
    end.

  (** Uncurry of [op_type], such that

        [argprod_apply f (x1,x2,...,xn) = f x1 x2 ... xn]. *)

  Fixpoint argprod_apply {A : sorts σ → Type} {w : OpType (sorts σ)}
      : op_type A w → argprod A (ne_list.front w) → A (result _ w) :=
    match w with
    | neone s => λ a _, a
    | s ::: w' => λ f '(x, l), argprod_apply (f x) l
    end.

  (** Funext for uncurried [op_type]s. If

        [argprod_apply f (x1,x2,...,xn) = argprod_apply g (x1,x2,...,xn)],

      for all [(x1,x2,...,xn) : A s1 * A s2 * ... A sn], then [f = g].
  *)

  Fixpoint argprod_apply_forall `{Funext} {A : sorts σ → Type} {w : OpType (sorts σ)}
      : ∀ (f g : op_type A w), (∀ a : argprod A (ne_list.front w),
                                argprod_apply f a = argprod_apply g a) -> f = g
  := match w with
     | neone s => λ f g h, h tt
     | s ::: w' =>
         λ f g h, path_forall f g (λ x,
                   argprod_apply_forall (f x) (g x) (λ a, h (x,a)))
     end.

End argprod.

Section argprod_homomorphism.
  Context
    (σ : Signature)
    {A B  : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
    {AA : Algebra σ A} {BB : Algebra σ B}
    (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}.

  Lemma argprod_homomorphism_preserves' {w : OpType (sorts σ)}
    (a : argprod σ A (ne_list.front w)) (ao : op_type A w) (bo : op_type B w)
    (P : Preservation σ A B f ao bo)
    : f (result (sorts σ) w) (argprod_apply σ ao a) =
      argprod_apply σ bo (argprod_map σ f a).
  Proof.
    induction w.
    - assumption.
    - destruct a as [x a]. apply IHw. apply P.
  Defined.

  Lemma argprod_homomorphism_preserves :
      ∀ (u : σ) (a : argprod σ A (ne_list.front (σ u))),
      f (result (sorts σ) (σ u)) (argprod_apply σ (algebra_op u) a) =
      argprod_apply σ (algebra_op u) (argprod_map σ f a).
  Proof. intros u a. now apply argprod_homomorphism_preserves'. Defined.
End argprod_homomorphism.

(** This section develops the [quotient_algebra] instance of the [Algebra] type
    class. *)

Section quotient_algebra.
  Context
    (σ : Signature)
    {A : sorts σ → Type} {As : AlgebraOps σ A} {AA : Algebra σ A}
    (Φ : ∀ s, relation (A s)).

  (** The relation family [Φ] satisfies the [congruence_property f] with respect
      to the algebra operation [f : A s1 → A s2 → ... → A (s(n+1))] if

        [Φ s1 x1 y1 ∧ Φ s2 x2 y2 ∧ ... ∧ Φ sn xn yn] implies
        [Φ (s(n+1)) (f x1 x2 ... xn) (f y1 y2 ... yn)]. *)

  Definition congruence_property {w : OpType (sorts σ)} (f : op_type A w) :=
    ∀ (a b : argprod σ A (ne_list.front w)),
    argprod_for_all_2 σ Φ a b ->
    Φ (result (sorts σ) w) (argprod_apply σ f a) (argprod_apply σ f b).

  (** The relation family [Φ] is a [Congruence] if [Φ s] it is a family of
      mere equivalence relations and [Φ] has the [congruence_property f]
      for all the algebra operations [f]. *)

  Class Congruence {MereRel : ∀ s, is_mere_relation _ (Φ s)}
      {EqRel : ∀ (s : sorts σ), Equivalence (Φ s)} : Type :=
    congruence_respect_ops : ∀ (u : σ), congruence_property (algebra_op u).

  (** Suppose [Φ] is a congruence from now on. *)
  Context `{Congruence}.

  (** If a congruence [Φ] satisfies the [congruence_property f] for
      [f : A s1 → A s2 → ... → A (s(n+1))], then [Φ] satisfies
      the [congruence_property (f x)] for any [x : A s1]. *)
  Lemma congruence_property_from_cons {s : sorts σ} {w : OpType (sorts σ)}
      : ∀ (f : op_type A (s ::: w)) (x : A s),
        congruence_property f → congruence_property (f x).
  Proof.
    intros f x P a b R.
    exact (P (x,a) (x,b) (Equivalence_Reflexive x, R)).
  Defined.

  (* The family of sets in the quotient algebra. *)

  Definition carrier (s : sorts σ) : Type := quotient (Φ s).

  Lemma argprod_for_all_2_reflexive
      : ∀ w (a : argprod σ A w), argprod_for_all_2 σ Φ a a.
  Proof.
    induction w; intros.
    - reflexivity.
    - by split.
  Defined.

  (** Specialization of [quotient_ind_prop]. *)

  Fixpoint argprod_quotient_ind_prop `{Funext} {w : list (sorts σ)}
      : ∀ (P : argprod σ carrier w -> Type) {sP : ∀ a, IsHProp (P a)}
          (dclass : ∀ x, P (argprod_map σ (λ s, class_of (Φ s)) x))
          (a : argprod σ carrier w), P a :=
    match w with
    | nil => λ P sP dclass 'tt, dclass tt
    | s :: w' => λ P sP dclass a,
      quotient_ind_prop (Φ s) (λ a0, ∀ a1, P (a0, a1))
        (λ a0, argprod_quotient_ind_prop
                (λ c, P (class_of (Φ s) a0, c)) (λ c, dclass (a0, c)))
        (fst a) (snd a)
    end.

  (** Suppose [f : A s1 → A s2 → ... → A sn] is an algebra operation and
      [g : carrier s1 → carrier s2 → ... → carrier sn] is a quotient algebra
      operation. Then [g] has the [quotient_op_property] with respect to [f] if

        [g (class x1) (class x2) ... (class xn) = class (f x1 x2 .. xn)],

      where [class xi] is the quotient algebra equivalence class of [xi]. *)

  Definition quotient_op_property {w : OpType (sorts σ)}
    (f : op_type A w) (g : op_type carrier w) :=
    ∀ (a : argprod σ A (ne_list.front w)),
      argprod_apply σ g (argprod_map σ (λ s, class_of (Φ s)) a) =
      class_of (Φ (result (sorts σ) w)) (argprod_apply σ f a).

  (** Quotient algebra operations induced from congruence [Φ]. For each
      operation [algebra_op u] in algebra [A], there is a quotient algebra
      operation [g] satisfying the [quotient_op_property f g] with respect to f. *)

  Fixpoint quotient_op `{Funext} {w : OpType (sorts σ)} :
    ∀ (f : op_type A w),
    congruence_property f ->
    ∃ (g : op_type carrier w), quotient_op_property f g.
  Proof. refine (
      match w with
      | neone s => λ f P, (class_of (Φ s) f; λ a, idpath)
      | s ::: w' => λ f P,
        (quotient_rec (Φ s) (λ x, (quotient_op _ w' (f x)
                (congruence_property_from_cons f x P)).1) _ ; _)
      end
    ).
    intros [x a].
    apply (quotient_op _ w' (f x) (congruence_property_from_cons f x P)).
    Grab Existential Variables.
      intros x y E.
      apply (@argprod_apply_forall σ _), argprod_quotient_ind_prop; try apply _.
      intro a.
      destruct (quotient_op _ _ _ (congruence_property_from_cons f x P)) as [g1 P1].
      destruct (quotient_op _ _ _ (congruence_property_from_cons f y P)) as [g2 P2].
      unfold proj1_sig.
      rewrite P1, P2.
      apply related_classes_eq.
      set (v := argprod_for_all_2_reflexive (ne_list.front w') a).
      exact (P (x,a) (y,a) (E,v)).
  Defined.

  Global Instance quotient_ops `{Funext} : AlgebraOps σ carrier :=
    λ (u : σ), (quotient_op (algebra_op u) (congruence_respect_ops u)).1.

  Global Instance quotient_algebra `{Funext} : Algebra σ carrier :=
    λ s, quotient_set (Φ s).
End quotient_algebra.

(** This section defines the quotient homomorphism [quotient_map] satisfying

      [quotient_map _ x = class x],

    where [class x] is the quotient algebra equivalence class of [x]. *)

Section quotient_map.
  Context
    (σ : Signature)
    {A : sorts σ → Type} {As : AlgebraOps σ A} {AA : Algebra σ A}
    (Φ : ∀ s, relation (A s)) {MereRel : ∀ s, is_mere_relation _ (Φ s)}
    {EqRel : ∀ s, Equivalence (Φ s)} {Cong : Congruence σ Φ}.

  Definition quotient_map : ∀ s, A s → carrier σ Φ s :=
    λ s x, class_of (Φ s) x.

  Lemma quotient_map_preservation `{Funext} (w : OpType (sorts σ))
      (g : op_type (carrier σ Φ) w) (ao : op_type A w)
      (G : quotient_op_property σ Φ ao g)
      : Preservation σ A (carrier σ Φ) quotient_map ao g.
    unfold quotient_op_property in G.
    induction w; simpl in *.
    - rewrite (G tt). reflexivity.
    - intro x. apply IHw. intro a. apply (G (x,a)).
  Qed.

  Global Instance quotient_map_homomorphism `{Funext}
    : HomoMorphism σ A (carrier σ Φ) quotient_map.
  Proof.
    intro u.
    apply quotient_map_preservation, quotient_op.
  Qed.
End quotient_map.

(** This section develops the universal mapping property [quotient_property]
    of the quotient algebra. *)

Section quotient_property.
  Context
    {U : Univalence}
    (σ : Signature)
    {A B : sorts σ → Type}
    {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
    {AA : Algebra σ A} {BB : Algebra σ B}
    (Φ : ∀ s, relation (A s)) {MereRel : ∀ s, is_mere_relation _ (Φ s)}
    {EqRel : ∀ s, Equivalence (Φ s)} {Cong : Congruence σ Φ}.

(** Given a homomorphism [f : ∀ s, A s → B s] respecting the congruence [Φ],
    there is a homomorphism [g : ∀ s, carrier σ Φ s → B s] out of the quotient
    algebra satisfynig [quotient_property_mapout_compute] below. *)

  Section quotient_property_mapout.
    Context
      (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}
      (R : ∀ s x y, Φ s x y → f s x = f s y).

    Definition quotient_property_mapout : ∀ s, carrier σ Φ s → B s :=
      λ s, (quotient_ump (Φ s) (BuildhSet (B s)))^-1 (f s; R s).

    Lemma quotient_property_mapout_preservation {w : OpType (sorts σ)}
        (g : op_type (carrier σ Φ) w) (ao : op_type A w) (bo : op_type B w)
        (G : quotient_op_property σ Φ ao g) (P : Preservation σ A B f ao bo)
        : Preservation σ (carrier σ Φ) B quotient_property_mapout g bo.
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
      : HomoMorphism σ (carrier σ Φ) B quotient_property_mapout.
    Proof.
      intro u.
      eapply quotient_property_mapout_preservation.
      - apply quotient_op.
      - apply F.
    Qed.

    (** The computation rule for the homomorphism [g : ∀ s, carrier σ Φ s → B s]
        defined by the [quotient_property_mapout] is

          [g s (class x) = f s x],

        where [class x] is the quotient algebra equivalence class of [x]. *)

    Lemma quotient_property_mapout_compute
      : ∀ s (x : A s), quotient_property_mapout s (class_of (Φ s) x) = f s x.
    Proof. reflexivity. Defined.

  End quotient_property_mapout.

  (** Suppose [g : ∀ s, carrier σ Φ s → B s] is a homomorphism out of the
      quotient algebra. There is a homomorphism [λ s, g s ∘ quotient_map σ Φ s]
      factoring through the [quotient_map] and [g]. *)

  Definition quotient_property_factoring (g : ∀ s, carrier σ Φ s → B s)
      `{HomoMorphism σ (carrier σ Φ) B g} : ∀ s, A s → B s
    := λ s, g s ∘ quotient_map σ Φ s.

  (** The left to right direction of the quotient algebra universal mapping
      property [quotient_property]. The resulting homomorphism [g] is given by
      the [quotient_property_mapout] above. *)

  Lemma quotient_property_lr :
    (∃ (f : ∀ s, A s → B s) (F : HomoMorphism σ A B f),
      ∀ s x y, Φ s x y → f s x = f s y) →
     ∃ (g : ∀ s, carrier σ Φ s → B s), HomoMorphism σ (carrier σ Φ) B g.
  Proof.
    intros [f [F P]].
    exists (quotient_property_mapout f P).
    apply _.
  Defined.

  (** The right to left direction of the quotient algebra universal mapping
      property [quotient_property]. The resulting homomorphism [f] is given by
      the [quotient_property_factoring] above. The homomorphism [f] respects the
      congruence [Φ]. *)

  Lemma quotient_property_rl
    : (∃ (g : ∀ s, carrier σ Φ s → B s), HomoMorphism σ (carrier σ Φ) B g) →
      ∃ (f : ∀ s, A s → B s) (F : HomoMorphism σ A B f),
        ∀ s x y, Φ s x y → f s x = f s y.
  Proof.
    intros [g G].
    exact (( quotient_property_factoring g
           ; compose_homomorphisms σ A _ B g (quotient_map σ Φ)
           ; λ s x y E, transport (λ z, g s (class_of (Φ s) x) = g s z)
                          (related_classes_eq (Φ s) E) idpath)).
  Defined.

  Lemma quotient_property_lr_sect : Sect quotient_property_rl quotient_property_lr.
  Proof.
    intros [g G].
    apply path_sigma_hprop, path_forall.
    intro s.
    apply (eissect (quotient_ump (Φ s) (BuildhSet (B s)))).
  Defined.

  Lemma quotient_property_rl_sect : Sect quotient_property_lr quotient_property_rl.
  Proof.
    intros [h [H1 H2]].
    apply path_sigma_hprop, path_forall.
    intro s.
    now apply path_forall.
  Defined.

  (** The universal property of the quotient algebra. For each homomorphism
      [f : ∀ s, A s → B s] respecting the congruence [Φ], there is a unique
      homomorphism [g : ∀ s, carrier σ Φ s → B s] out of the quotient algebra.
      In one direction, the homomorphism [g] is given by the
      [quotient_property_mapout]. In the other direction, the homomorphism [f]
      is given by the [quotient_property_factoring]. *)

  Lemma quotient_property
    : (∃ (f : ∀ s, A s → B s) (F : HomoMorphism σ A B f),
       ∀ s (x y : A s), Φ s x y → f s x = f s y)
      <~>
       ∃ (g : ∀ s, carrier σ Φ s → B s), HomoMorphism σ (carrier σ Φ) B g.
  Proof.
    apply (equiv_adjointify quotient_property_lr quotient_property_rl).
    - exact quotient_property_lr_sect.
    - exact quotient_property_rl_sect.
  Defined.
End quotient_property.

Section first_isomorphism_theorem.
  Context
    {U : Univalence}
    (σ : Signature)
    {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
    {AA : Algebra σ A} {BB : Algebra σ B}
    (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}.

  Definition kernel (s : sorts σ) : relation (A s) := λ x y, f s x = f s y.

  Global Instance kernel_equivalence (s : sorts σ) : Equivalence (kernel s).
  Proof.
   unfold kernel.
   repeat constructor.
   - intros x y h. by symmetry.
   - intros x y z h1 h2. exact (h1 @ h2).
  Defined.

  Lemma kernel_congruence' {w : OpType (sorts σ)}
    (bo : op_type B w) (a b : argprod σ A (ne_list.front w))
    (R : argprod_for_all_2 σ kernel a b)
    : argprod_apply σ bo (argprod_map σ f a) =
      argprod_apply σ bo (argprod_map σ f b).
  Proof.
    induction w.
    - reflexivity.
    - destruct a as [x a], b as [y b], R as [r R].
      simpl.
      unfold kernel in r.
      rewrite r.
      now apply IHw.
  Qed.

  Instance kernel_congruence : Congruence σ kernel.
  Proof.
    intros u a b R.
    unfold kernel.
    rewrite (argprod_homomorphism_preserves σ f u a).
    rewrite (argprod_homomorphism_preserves σ f u b).
    now apply kernel_congruence'.
  Qed.

  Definition in_image (s : sorts σ) (y : B s) : Type := merely (hfiber (f s) y).

  Lemma image_subalgebra' {w : OpType (sorts σ)}
    (ao : op_type A w) (bo : op_type B w) (P : Preservation σ A B f ao bo)
    : op_closed σ in_image bo.
  Proof.
    induction w.
    - exact (tr (ao; P)).
    - intro y.
      refine (Trunc_rec _).
      intros [x p].
      apply (IHw (ao x)).
      now refine (transport (λ y, Preservation σ A B f (ao x) (bo y)) p _).
  Defined.

  Global Instance image_subalgebra : ClosedSubset σ in_image.
  Proof. intro u. eapply image_subalgebra', F. Defined.

  Definition first_isomorphism (s : sorts σ)
    : carrier σ kernel s → ua_subalgebra.carrier σ in_image s.
  Proof.
    refine (quotient_rec (kernel s) (λ x : A s, (f s x ; tr (x ; idpath))) _).
    intros x y H.
    now apply path_sigma_hprop.
  Defined.

  Lemma first_isomorphism_preservation {w : OpType (sorts σ)}
    (g : op_type (carrier σ kernel) w)
    (ao : op_type A w) (bo : op_type B w)
    (P : Preservation σ A B f ao bo)
    (G : quotient_op_property σ kernel ao g)
    : Preservation σ (carrier σ kernel) (ua_subalgebra.carrier σ in_image)
        first_isomorphism g (close_op σ in_image bo (image_subalgebra' ao bo P)).
  Proof.
    unfold quotient_op_property in G.
    induction w.
    - apply path_sigma_hprop.
      generalize dependent g.
      refine (quotient_ind_prop (kernel t) _ _).
      intros x G.
      rewrite <- P.
      apply (classes_eq_related (kernel t) _ _ (G tt)).
    - refine (quotient_ind_prop (kernel t) _ _).
      intro x.
      apply (IHw (g (class_of (kernel t) x)) (ao x) (bo (f t x)) (P x)).
      intro a.
      apply (G (x,a)).
  Qed.

  Global Instance first_isomorphism_homomorphism
    : HomoMorphism σ (carrier σ kernel) (ua_subalgebra.carrier σ in_image)
          first_isomorphism.
  Proof.
    intro u.
    apply first_isomorphism_preservation.
    apply (quotient_op σ kernel (As u) (congruence_respect_ops σ kernel u)).
  Qed.

  Global Instance first_isomorphism_is_embedding (s : sorts σ)
    : IsEmbedding (first_isomorphism s).
  Proof.
    intros [y H].
    apply ishprop_sigma_disjoint.
    refine (quotient_ind_prop (kernel s) _ _).
    intro x1.
    refine (quotient_ind_prop (kernel s) _ _).
    intros x2 h1 h2.
    apply related_classes_eq.
    exact ((pr1_path h1) @ (pr1_path h2)^).
  Qed.

  Global Instance first_isomorphism_is_surjection (s : sorts σ)
    : IsSurjection (first_isomorphism s).
  Proof.
    apply BuildIsSurjection.
    intros [x X].
    refine (Trunc_rec _ X).
    intros [y Y].
    apply tr.
    exists (class_of _ y).
    now apply path_sigma_hprop.
  Qed.

  Global Instance first_isomorphism_is_equiv (s : sorts σ)
    : IsEquiv (first_isomorphism s).
  Proof.
    apply isequiv_surj_emb.
    apply first_isomorphism_is_surjection.
    apply first_isomorphism_is_embedding.
  Qed.

  Theorem first_isomorphism_theorem (s : sorts σ)
    : carrier σ kernel s <~> ua_subalgebra.carrier σ in_image s.
  Proof. apply (BuildEquiv _ _ (first_isomorphism s)), _. Defined.

  Theorem first_identification_theorem
    : carrier σ kernel = ua_subalgebra.carrier σ in_image.
  Proof.
    apply path_forall.
    intro s.
    apply equiv_path_universe, first_isomorphism_theorem.
  Defined.
End first_isomorphism_theorem.
