Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_algebra
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

Import algebra_notations.

(* TODO Fix documentation. *)

(** The following section implements a datatype [argprod] intended to represent
    a product/tuple of algebra operation arguments. Suppose [σ : Signature] is
    a signature and [A : Algebra σ] an algebra. An algebra operation
    [u^^A] has type [u^^U : op_type A (σ u)], for [u : symbol σ] a function
    symbol. The type [op_type A (σ u)] is a curried function type
    [A s1 -> A s2 -> ... -> A sn], where [[:s1,s2,...,sn:] = σ u]. The
    [argprod_apply] function below can be used to uncurry [f], so that

      [argprod_apply f (x1,x2,...,xn) = f x1 x2 ... xn]. *)

Section argprod.
  Context {σ : Signature}.

  (** A product type [argprod A [s1,s2,...,sn] = A s1 * A s2 * ... * A sn]. *)

  Fixpoint argprod (A : Carriers σ) (w : list (sort σ)) : Type :=
    match w with
    | nil => Unit
    | s :: w' => A s * argprod A w'
    end.

  (** Map function for [argprod]

        [argprod_map f (x1,x2,...,xn) = (f x1, f x2, ..., f xn)]. *)

  Fixpoint argprod_map {A : Carriers σ} {B : sort σ → Type}
      {w : list (sort σ)} (f : ∀ s, A s → B s)
      : argprod A w → argprod B w :=
    match w with
    | nil => const tt
    | s :: w' => λ '(x,l), (f s x, argprod_map f l)
    end.

  (** Test whether [P s1 x1 ∧ P s2 x2 ∧ ... ∧ P sn xn] holds, where
      [(x1,...,xn) : A s1 * A s2 * ... * S xn]. *)

  Fixpoint argprod_for_all {A : Carriers σ} {w : list (sort σ)}
      (P : ∀ s, A s -> Type) : argprod A w → Type :=
    match w with
    | nil => λ _, True
    | s :: w' => λ '(x,l), P s x * argprod_for_all P l
    end.

  (** Test whether [R s1 x1 y1 ∧ R s2 x2 y2 ∧ ... ∧ P sn xn yn] holds, where
      [(x1,...,xn) : A s1 * A s2 * ... * S xn] and
      [(y1,...,yn) : B s1 * B s2 * ... * B xn] *)

  Fixpoint argprod_for_all_2 {A B : Carriers σ} {w : list (sort σ)}
      (R : ∀ s, A s -> B s -> Type) : argprod A w → argprod B w → Type :=
    match w with
    | nil => λ _ _, True
    | s :: w' => λ '(x1,l1) '(x2,l2), R s x1 x2 * argprod_for_all_2 R l1 l2
    end.

  (** Uncurry of [op_type], such that

        [argprod_apply f (x1,x2,...,xn) = f x1 x2 ... xn]. *)

  Fixpoint argprod_apply {A : Carriers σ} {w : symboltype σ}
      : op_type A w → argprod A (dom_symboltype w) → A (cod_symboltype w) :=
    match w with
    | [:s:] => λ a _, a
    | s ::: w' => λ f '(x, l), argprod_apply (f x) l
    end.

  (** Funext for uncurried [op_type]s. If

        [argprod_apply f (x1,x2,...,xn) = argprod_apply g (x1,x2,...,xn)],

      for all [(x1,x2,...,xn) : A s1 * A s2 * ... A sn], then [f = g].
  *)

  Fixpoint argprod_apply_forall `{Funext} {A : Carriers σ} {w : symboltype σ}
      : ∀ (f g : op_type A w), (∀ a : argprod A (dom_symboltype w),
                                argprod_apply f a = argprod_apply g a) -> f = g
  := match w with
     | [:s:] => λ f g h, h tt
     | s ::: w' =>
         λ f g h, path_forall f g (λ x,
                   argprod_apply_forall (f x) (g x) (λ a, h (x,a)))
     end.

End argprod.

Section argprod_homomorphism.
  Context {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B).

  Lemma path_homomorphism_argprod_apply' {w : symboltype σ}
    (a : argprod A (dom_symboltype w)) (ao : op_type A w) (bo : op_type B w)
    (P : OpPreserving f ao bo)
    : f (cod_symboltype w) (argprod_apply ao a) =
      argprod_apply bo (argprod_map f a).
  Proof.
    induction w.
    - assumption.
    - destruct a as [x a]. apply IHw. apply P.
  Defined.

  Lemma path_homomorphism_argprod_apply :
      ∀ (u : symbol σ) (a : argprod A (dom_symboltype (σ u))),
      f (cod_symboltype (σ u)) (argprod_apply (u^^A) a) =
      argprod_apply (u^^B) (argprod_map f a).
  Proof.
    intros u a.
    apply path_homomorphism_argprod_apply'.
    apply f.
  Defined.
End argprod_homomorphism.

(** This section develops the [quotient_algebra] instance of the [Algebra] type
    class. *)

Section congruence.
  Context
    {σ : Signature} (A : Algebra σ) (Φ : ∀ s, relation (A s)).

  (** The relation family [Φ] satisfies the [congruence_property f] with respect
      to the algebra operation [f : A s1 → A s2 → ... → A (s(n+1))] if

        [Φ s1 x1 y1 ∧ Φ s2 x2 y2 ∧ ... ∧ Φ sn xn yn] implies
        [Φ (s(n+1)) (f x1 x2 ... xn) (f y1 y2 ... yn)]. *)

  Definition congruence_property {w : symboltype σ} (f : op_type A w) :=
    ∀ (a b : argprod A (dom_symboltype w)),
    argprod_for_all_2 Φ a b ->
    Φ (cod_symboltype w) (argprod_apply f a) (argprod_apply f b).

  (** The relation family [Φ] is a [IsCongruence] if [Φ s] it is a family of
      mere equivalence relations and [Φ] has the [congruence_property f]
      for all the algebra operations [f]. *)

  Class IsCongruence `{!∀ s, is_mere_relation (A s) (Φ s)}
      `{!∀ s, Equivalence (Φ s)} : Type :=
    congruence_property_family : ∀ (u : symbol σ), congruence_property (u^^A).
End congruence.

Global Arguments congruence_property {σ} {A} Φ {w} f.

Section quotient_algebra.
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
  Lemma congruence_property_from_cons {s : sort σ} {w : symboltype σ}
      : ∀ (f : op_type A (s ::: w)) (x : A s),
        congruence_property Φ f → congruence_property Φ (f x).
  Proof.
    intros f x P a b R.
    exact (P (x,a) (x,b) (Equivalence_Reflexive x, R)).
  Defined.

  (* The family of sets in the quotient algebra. *)

  Definition carriers_quotient : Carriers σ := λ s, quotient (Φ s).

  Lemma argprod_for_all_2_reflexive
      : ∀ w (a : argprod A w), argprod_for_all_2 Φ a a.
  Proof.
    induction w; intros.
    - reflexivity.
    - by split.
  Defined.

  (** Specialization of [quotient_ind_prop]. *)

  Fixpoint argprod_quotient_ind_prop `{Funext} {w : list (sort σ)}
      : ∀ (P : argprod carriers_quotient w -> Type) `{!∀ a, IsHProp (P a)}
          (dclass : ∀ x, P (argprod_map (λ s, class_of (Φ s)) x))
          (a : argprod carriers_quotient w), P a :=
    match w with
    | nil => λ P sP dclass 'tt, dclass tt
    | s :: w' => λ P _ dclass a,
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

  Definition quotient_op_property {w : symboltype σ}
    (f : op_type A w) (g : op_type carriers_quotient w) :=
    ∀ (a : argprod A (dom_symboltype w)),
      argprod_apply g (argprod_map (λ s, class_of (Φ s)) a) =
      class_of (Φ (cod_symboltype w)) (argprod_apply f a).

  (** Quotient algebra operations induced from congruence [Φ]. For each
      operation [algebra_op u] in algebra [A], there is a quotient algebra
      operation [g] satisfying the [quotient_op_property f g] with respect to f. *)

  Fixpoint op_quotientalg `{Funext} {w : symboltype σ} :
    ∀ (f : op_type A w),
    congruence_property Φ f ->
    ∃ (g : op_type carriers_quotient w), quotient_op_property f g.
  Proof. refine (
      match w with
      | [:s:] => λ f P, (class_of (Φ s) f; λ a, idpath)
      | s ::: w' => λ f P,
        (quotient_rec (Φ s) (λ x, (op_quotientalg _ w' (f x)
                (congruence_property_from_cons f x P)).1) _ ; _)
      end
    ).
    intros [x a].
    apply (op_quotientalg _ w' (f x) (congruence_property_from_cons f x P)).
    Grab Existential Variables.
    intros x y E.
    apply (@argprod_apply_forall σ _), argprod_quotient_ind_prop; try apply _.
    intro a.
    destruct (op_quotientalg _ _ _ (congruence_property_from_cons f x P))
      as [g1 P1].
    destruct (op_quotientalg _ _ _ (congruence_property_from_cons f y P))
      as [g2 P2].
    refine ((P1 a) @ _ @ (P2 a)^).
    apply related_classes_eq.
    exact (P (x, a) (y, a) (E, argprod_for_all_2_reflexive (dom_symboltype w') a)).
  Defined.

  Definition opfamily_quotientalg `{Funext} (u : symbol σ)
    : op_type carriers_quotient (σ u)
    := (op_quotientalg (u^^A) (congruence_property_family A Φ u)).1.

  Definition quotientalg `{Funext} : Algebra σ
    := BuildAlgebra carriers_quotient opfamily_quotientalg.
End quotient_algebra.

(** This section defines the quotient homomorphism [quotient_map] satisfying

      [quotient_map _ x = class x],

    where [class x] is the quotient algebra equivalence class of [x]. *)

Section quotient_map.
  Context
    `{Funext}
    {σ : Signature}
    (A : Algebra σ)
    (Φ : ∀ s, relation (A s))
    `{!∀ s, is_mere_relation _ (Φ s)}
    `{!∀ s, Equivalence (Φ s)}
    `{!IsCongruence A Φ}.

  Definition fn_quotient : ∀ s, A s → quotientalg A Φ s :=
    λ s x, class_of (Φ s) x.

  Lemma oppreserving_quotient `{Funext} (w : symboltype σ)
      (g : op_type (carriers_quotient A Φ) w) (ao : op_type A w)
      (G : quotient_op_property A Φ ao g)
      : OpPreserving fn_quotient ao g.
    unfold quotient_op_property in G.
    induction w; simpl in *.
    - rewrite (G tt). reflexivity.
    - intro x. apply IHw. intro a. apply (G (x,a)).
  Qed.

  Global Instance ishomomorphism_quotient `{Funext}
    : IsHomomorphism fn_quotient.
  Proof.
    intro u.
    apply oppreserving_quotient, op_quotientalg.
  Qed.

  Definition hom_quotient : Homomorphism A (quotientalg A Φ)
    := BuildHomomorphism fn_quotient.

  (* TODO hom_quotient is surjective. *)
End quotient_map.

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

    Definition fn_quotient_property_mapout : ∀ s, quotientalg A Φ s → B s :=
      λ s, (quotient_ump (Φ s) (BuildhSet (B s)))^-1 (f s; R s).

    Lemma quotient_property_mapout_preservation {w : symboltype σ}
        (g : op_type (carriers_quotient A Φ) w)
        (ao : op_type A w) (bo : op_type B w)
        (G : quotient_op_property A Φ ao g) (P : OpPreserving f ao bo)
        : OpPreserving fn_quotient_property_mapout g bo.
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
      : IsHomomorphism fn_quotient_property_mapout.
    Proof.
      intro u.
      eapply quotient_property_mapout_preservation.
      - apply op_quotientalg.
      - apply f.
    Qed.

    Definition hom_quotient_property_mapout : Homomorphism (quotientalg A Φ) B
      := BuildHomomorphism fn_quotient_property_mapout.

    (** The computation rule for the homomorphism [g : ∀ s, carrier σ Φ s → B s]
        defined by the [quotient_property_mapout] is

          [g s (class x) = f s x],

        where [class x] is the quotient algebra equivalence class of [x]. *)

    Lemma quotient_property_mapout_compute
      : ∀ s (x : A s), hom_quotient_property_mapout s (class_of (Φ s) x) = f s x.
    Proof. reflexivity. Defined.

  End quotient_property_mapout.

  (** Suppose [g : ∀ s, carrier σ Φ s → B s] is a homomorphism out of the
      quotient algebra. There is a homomorphism [λ s, g s ∘ quotient_map σ Φ s]
      factoring through the [quotient_map] and [g]. *)

  Definition hom_quotient_property_factoring
    (g : Homomorphism (quotientalg A Φ) B)
    : Homomorphism A B
    := BuildHomomorphism (λ s, g s ∘ hom_quotient A Φ s).

  (** The left to right direction of the quotient algebra universal mapping
      property [quotient_property]. The resulting homomorphism [g] is given by
      the [quotient_property_mapout] above. *)

  Lemma quotient_property_lr :
    (∃ (f : Homomorphism A B), ∀ s x y, Φ s x y → f s x = f s y)
    → Homomorphism (quotientalg A Φ) B.
  Proof.
    intros [f P].
    exists (hom_quotient_property_mapout f P).
    apply _.
  Defined.

  (** The right to left direction of the quotient algebra universal mapping
      property [quotient_property]. The resulting homomorphism [f] is given by
      the [quotient_property_factoring] above. The homomorphism [f] respects the
      congruence [Φ]. *)

  Lemma quotient_property_rl :
    Homomorphism (quotientalg A Φ) B →
    ∃ (f : Homomorphism A B), ∀ s x y, Φ s x y → f s x = f s y.
  Proof.
    intro g.
    refine ((BuildHomomorphism (hom_quotient_property_factoring g) ; _)).
    intros s x y E.
    exact (transport (λ z, g s (class_of (Φ s) x) = g s z)
            (related_classes_eq (Φ s) E) idpath).
  Defined.

  Lemma quotient_property_lr_sect : Sect quotient_property_rl quotient_property_lr.
  Proof.
    intros [g G].
    apply path_sigma_hprop.
    funext s.
    refine (eissect (quotient_ump (Φ s) (BuildhSet (B s))) (g s)).
  Defined.

  Lemma quotient_property_rl_sect : Sect quotient_property_lr quotient_property_rl.
  Proof.
    intros [[f F] P].
    repeat apply path_sigma_hprop.
    funext s.
    now apply path_forall.
  Defined.

  (** The universal property of the quotient algebra. For each homomorphism
      [f : ∀ s, A s → B s] respecting the congruence [Φ], there is a unique
      homomorphism [g : ∀ s, carrier σ Φ s → B s] out of the quotient algebra.
      In one direction, the homomorphism [g] is given by the
      [quotient_property_mapout]. In the other direction, the homomorphism [f]
      is given by the [quotient_property_factoring]. *)

  Lemma quotient_property
    : (∃ (f : Homomorphism A B), ∀ s (x y : A s), Φ s x y → f s x = f s y)
      <~>
       Homomorphism (quotientalg A Φ) B.
  Proof.
    apply (equiv_adjointify quotient_property_lr quotient_property_rl).
    - exact quotient_property_lr_sect.
    - exact quotient_property_rl_sect.
  Defined.
End quotient_property.

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

  Lemma path_kernel_argprod_apply {w : symboltype σ}
    (bo : op_type B w) (a b : argprod A (dom_symboltype w))
    (R : argprod_for_all_2 hom_kernel a b)
    : argprod_apply bo (argprod_map f a) =
      argprod_apply bo (argprod_map f b).
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
    repeat rewrite (path_homomorphism_argprod_apply f).
    now apply path_kernel_argprod_apply.
  Qed.

  Definition in_hom_image (s : sort σ) (y : B s) : Type
    := merely (hfiber (f s) y).

  Lemma op_closed_subalg_in_hom_image {w : symboltype σ}
    (ao : op_type A w) (bo : op_type B w) (P : OpPreserving f ao bo)
    : op_closed_subalg in_hom_image bo.
  Proof.
    induction w.
    - exact (tr (ao; P)).
    - intro y.
      refine (Trunc_rec _).
      intros [x p].
      apply (IHw (ao x)).
      now refine (transport (λ y, OpPreserving f (ao x) (bo y)) p _).
  Defined.

  Global Instance closedsubalg_image : ClosedSubalg in_hom_image.
  Proof.
    intro u. eapply op_closed_subalg_in_hom_image, f.
  Defined.

  Definition def_first_isomorphism (s : sort σ)
    : quotientalg A hom_kernel s → subalg in_hom_image s.
  Proof.
    refine (
      quotient_rec (hom_kernel s) (λ x : A s, (f s x ; tr (x ; idpath))) _).
    intros x y ?.
    now apply path_sigma_hprop.
  Defined.

  Lemma oppreserving_first_isomorphism {w : symboltype σ}
    (g : op_type (carriers_quotient A hom_kernel) w)
    (ao : op_type A w) (bo : op_type B w)
    (P : OpPreserving f ao bo)
    (G : quotient_op_property A hom_kernel ao g)
    : OpPreserving def_first_isomorphism g
        (op_subalg in_hom_image bo (op_closed_subalg_in_hom_image ao bo P)).
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
    apply (op_quotientalg A hom_kernel (u^^A)
            (congruence_property_family A hom_kernel u)).
  Qed.

  Definition hom_first_isomorphism
    : Homomorphism (quotientalg A hom_kernel) (subalg in_hom_image)
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
    : quotientalg A hom_kernel = subalg in_hom_image.
  Proof.
    exact (path_isomorphism hom_first_isomorphism).
  Defined.
End first_isomorphism_theorem.
