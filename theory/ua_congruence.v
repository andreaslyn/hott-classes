Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.universal_algebra
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
    function symbol. The type [op_type A (σ u)] is a curried function type (or
    type of a constant). The [argprod_apply] function below can be used to
    uncurry [f], so that

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

        [argprod_map f (x1,x2,...,xn) = (f x1, f x2, ..., f xn)].
  *)

  Fixpoint argprod_map {A : sorts σ → Type} {B : sorts σ → Type}
      {w : list (sorts σ)} (f : ∀ s, A s → B s)
      : argprod A w → argprod B w :=
    match w with
    | nil => const tt
    | s :: w' => λ '(x,l), (f s x, argprod_map f l)
    end.

  (** Test whether [P s1 x1 * P s2 x2 * ... * P sn xn] holds, where
      [(x1,...,xn) : argprod A [s1,s2,...,sn]]. *)

  Fixpoint argprod_for_all {A : sorts σ → Type} {w : list (sorts σ)}
      (P : ∀ s, A s -> Type) : argprod A w → Type :=
    match w with
    | nil => λ _, True
    | s :: w' => λ '(x,l), P s x * argprod_for_all P l
    end.

  (** Test whether [R s1 x1 y1 * R s2 x2 y2 * ... * P sn xn yn] holds, where
      [(x1,...,xn) : argprod A [s1,s2,...,sn]] and
      [(y1,...,yn) : argprod B [s1,s2,...,sn]] *)

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

  (** Funext for uncurried [op_type]s. *)

  Fixpoint argprod_apply_forall `{Funext}
      {A : sorts σ → Type} {w : OpType (sorts σ)}
      : ∀ (f g : op_type A w), (∀ a : argprod A (ne_list.front w),
            argprod_apply f a = argprod_apply g a) ->
        f = g :=
    match w with
    | neone s => λ f g h, h tt
    | s ::: w' =>
        λ f g h, path_forall f g (λ x,
                   argprod_apply_forall (f x) (g x) (λ a, h (x,a)))
    end.
End argprod.

(** The next section implements the [quotient_algebra] type class. *)

Section quotient_algebra.
  Context
    (σ : Signature)
    {A : sorts σ → Type} {As : AlgebraOps σ A} {AA : Algebra σ A}
    (Φ : ∀ s, relation (A s)).

  (* The indexed relation [Φ] has the [congruence_property] if, for all
     operations [f : op_type A ([s1,s2,...,s(n+1)]],

       [Φ s1 x1 y1 * Φ s1 x1 y1 * ... * Φ sn xn yn] implies
       [Φ (s(n+1)) (f x1 x2 ... xn)) (f y1 y2 ... yn))]. *)

  Definition congruence_property (w : OpType (sorts σ)) :=
    ∀ (f : op_type A w) (a b : argprod σ A (ne_list.front w)),
    argprod_for_all_2 σ Φ a b ->
    Φ (result (sorts σ) w) (argprod_apply σ f a) (argprod_apply σ f b).

  (* The indexed relation [Φ] is a [Congruence] if for each sort [s : sorts σ]
     [Φ s] is a mere equivalence relation, and for all function symbols [u],
     [Φ] has the [congruence_property (σ u)]. *)

  Class Congruence `{∀ s, is_mere_relation _ (Φ s)} : Type :=
    { congruence_equivalence :> ∀ (s : sorts σ), Equivalence (Φ s)
    ; congruence_respect_ops : ∀ (u : σ), congruence_property (σ u) }.

  Context `{Congruence}.

  (* Sets of the quotient algebra indexed by the sorts of the signature. *)

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

  (* Suppose [f : op_type A w] is an [A] algebra operation and
     [g : op_type carrier w] is a quotient algebra operation. Then [g] has the
     [quotient_ops_property] with respect to [f] if

       [g (class_of x1) (class_of x2) ... (class_of xn) =
       class_of (f x1 x2 .. xn)],

     where [class_of xi] is the equivalence class of [xi] in the quotient
     algebra. *)

  Definition quotient_ops_property {w : OpType (sorts σ)}
    (f : op_type A w) (g : op_type carrier w) :=
    ∀ (a : argprod σ A (ne_list.front w)),
      argprod_apply σ g (argprod_map σ (λ s, class_of (Φ s)) a) =
      class_of (Φ (result (sorts σ) w)) (argprod_apply σ f a).

  Lemma congruence_property_from_cons {s : sorts σ} {w : OpType (sorts σ)}
      : congruence_property (s ::: w) → A s → congruence_property w.
  Proof.
    intros P x f' a b h.
    exact (P (λ _, f') (x,a) (x,b) (Equivalence_Reflexive x, h)).
  Defined.

  (** Operations induced from congruence [Φ]. For each [A] algebra operation
      [f : op_type A w], there is a quotient algebra operation [g] satisfying
      the [quotient_ops_property f g] with respect to f. *)

  Fixpoint rec_impl `{Funext} {w : OpType (sorts σ)} :
    congruence_property w ->
    ∀ (f : op_type A w), ∃ (g : op_type carrier w), quotient_ops_property f g.
  Proof. refine (
      match w with
      | neone s => λ P f, (class_of (Φ s) f; λ a, idpath)
      | s ::: w' => λ P f,
        (* Introduce lambda abstraction to obtain the correct obligations. *)
        (λ R, (quotient_rec (Φ s) (λ x, (rec_impl _ w'
                (congruence_property_from_cons P x) (f x)).1) R; _)) _
      end
    ).
    - intros [x a].
      apply (rec_impl _ w' (congruence_property_from_cons P x) (f x)).
    - intros x y E.
      apply (@argprod_apply_forall σ H1).
      apply argprod_quotient_ind_prop; try apply _.
      intro a.
      destruct (rec_impl _ w' (congruence_property_from_cons P x) (f x)) as [g1 P1].
      destruct (rec_impl _ w' (congruence_property_from_cons P y) (f y)) as [g2 P2].
      unfold proj1_sig.
      rewrite P1.
      rewrite P2.
      apply related_classes_eq.
      set (r := argprod_for_all_2_reflexive (ne_list.front w') a).
      exact (P f (x,a) (y,a) (E,r)).
  Defined.

  Global Instance quotient_ops `{Funext} : AlgebraOps σ carrier.
  Proof.
    intro u. apply rec_impl.
    - apply congruence_respect_ops.
    - apply (algebra_op u).
  Defined.

  Global Instance quotient_algebra `{Funext} : Algebra σ carrier.
  Proof. intro s. apply _. Defined.
End quotient_algebra.

(** This section defines the quotient homomorphism [quotient_map] satisfying

      [quotient_map _ x = class_of x],

    where [class_of x] is the equivalence class of [x] in the quotient algebra. *)

Section quotient_map.
  Context
    (σ : Signature)
    {A : sorts σ → Type} {As : AlgebraOps σ A} {AA : Algebra σ A}
    (Φ : ∀ s, relation (A s)) `{Congruence σ A Φ}.

  Definition quotient_map : ∀ s, A s → carrier σ Φ s :=
    λ s x, class_of (Φ s) x.

  Global Instance quotient_map_homomorphism `{Funext}
    : HomoMorphism σ A (carrier σ Φ) quotient_map.
  Proof.
    intro u.
    unfold quotient_ops, algebra_op.
    set (ao := As u).
    set (co := congruence_respect_ops _ _ u).
    clearbody ao co.
    induction (σ u); by simpl.
  Qed.
End quotient_map.

(** This section developes the universal mapping property [quotient_property]
    of the quotient algebra. *)

Section quotient_property.
  Context
    {U : Univalence}
    (σ : Signature)
    {A B : sorts σ → Type}
    {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
    {AA : Algebra σ A} {BB : Algebra σ B}
    (Φ : ∀ s, relation (A s)) `{Congruence σ A Φ}.

(** Given a homomorphism [f : ∀ s, A s → B s] respecting the congruence [Φ],
    there is a homomorphism [g : ∀ s, carrier σ Φ s → B s] out of the quotient
    algebra. See [quotient_property_mapout_compute] below. *)

Definition quotient_property_mapout (f : ∀ s, A s → B s) `{HomoMorphism σ A B f}
    (R : ∀ s x y, Φ s x y → f s x = f s y)
    : ∀ s, carrier σ Φ s → B s :=
  λ s, (quotient_ump (Φ s) (BuildhSet (B s)))^-1 (f s; R s).

Global Instance quotient_property_mapout_homomorphism
    (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}
    (R : ∀ s x y, Φ s x y → f s x = f s y)
    : HomoMorphism σ (carrier σ Φ) B (quotient_property_mapout f R).
Proof.
  intro u.
  unfold quotient_ops, algebra_op.
  generalize (preserves σ A B f u).
  set (ao := As u).
  set (bo := Bs u).
  set (co := congruence_respect_ops _ _ u).
  clearbody ao bo co.
  induction (σ u); intro Q.
  - assumption.
  - refine (quotient_ind_prop (Φ t) _ _).
    intro x.
    set (co' := congruence_property_from_cons σ Φ co x).
    exact (IHo (ao x) (bo (f t x)) co' (Q x)).
Qed.

(** The computation rule for the homomorphism [g : ∀ s, carrier σ Φ s → B s]
    defined by the [quotient_property_mapout] is

      [g s (class_of x) = f s x],

    where [class_of x] is the equivalence class of [x] in the quotient algebra. *)

Lemma quotient_property_mapout_compute (f : ∀ s, A s → B s)
    `{HomoMorphism σ A B f} (R : ∀ s x y, Φ s x y → f s x = f s y)
    : ∀ s (x : A s), quotient_property_mapout f R s (class_of (Φ s) x) = f s x.
Proof. reflexivity. Defined.

(** Suppose [g : ∀ s, carrier σ Φ s → B s] is a homomorphism out of the quotient
    algebra. There is a homomorphism [λ s, g s ∘ quotient_map σ Φ s]
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
    the [quotient_property_factoring] above. Moreover, the homomorphism [f]
    respects the congruence [Φ]. *)

Lemma quotient_property_rl
  : (∃ (g : ∀ s, carrier σ Φ s → B s), HomoMorphism σ (carrier σ Φ) B g) →
    ∃ (f : ∀ s, A s → B s) (F : HomoMorphism σ A B f),
      ∀ s x y, Φ s x y → f s x = f s y.
Proof.
  refine (λ '(g;G),
    (quotient_property_factoring g ;
     compose_homomorphisms σ A _ B g (quotient_map σ Φ) ;
     λ s x y E, transport (λ z, g s (class_of (Φ s) x) = g s z)
                 (related_classes_eq (Φ s) E) idpath)).
Defined.

Lemma quotient_property_lr_sect : Sect quotient_property_rl quotient_property_lr.
Proof.
  intros [g G].
  apply path_sigma_hprop.
  apply path_forall.
  intro s.
  apply (eissect (quotient_ump (Φ s) (BuildhSet (B s)))).
Defined.

Lemma quotient_property_rl_sect : Sect quotient_property_lr quotient_property_rl.
Proof.
  intros [h [H1 H2]].
  apply path_sigma_hprop.
  apply path_forall.
  intro s.
  now apply path_forall.
Defined.

(** The universal property of the quotient algebra. For each homomorphism
    [f : ∀ s, A s → B s] respecting the congruence [Φ], there is a unique
    homomorphism [g : ∀ s, carrier σ Φ s → B s] out of the quotient algebra.
    In one direction, the homomorphism [g] is given by the
    [quotient_property_mapout]. In the other direction, the homomorphism [f]
    is given by the [quotient_property_factoring]. *)

Lemma quotient_property :
    (∃ (f : ∀ s, A s → B s) (F : HomoMorphism σ A B f),
     ∀ s (x y : A s), Φ s x y → f s x = f s y)
  <~>
    ∃ (g : ∀ s, carrier σ Φ s → B s), HomoMorphism σ (carrier σ Φ) B g.
Proof.
  apply (equiv_adjointify quotient_property_lr quotient_property_rl).
  exact quotient_property_lr_sect.
  exact quotient_property_rl_sect.
Defined.

End quotient_property.

Section in_domain.

  Context {A B} (f: A → B).

  Definition in_domain : relation A := λ x y, f x = f y.

  Global Instance in_domain_equivalence: Equivalence in_domain.
  Proof.
   unfold in_domain.
   constructor.
   constructor.
   intros x y h. by symmetry.
   intros x y z h1 h2.
   exact (h1 @ h2).
  Qed.

End in_domain.

Section first_iso.

(* "If A and B are algebras, and f is a homomorphism from A to B, then
 the equivalence relation Φ on A defined by a~b if and only if f(a)=f(b) is
 a congruence on A, and the algebra A/Φ is isomorphic to the image
 of f, which is a subalgebra of B." *)

  Context σ `{Algebra σ A} `{Algebra σ B} `{!HomoMorphism σ A B f}.

  Notation Φ := (λ s, in_domain (f s)).

  Lemma square o0 x x' y y':
    Preservation σ A B f x x' →
    Preservation σ A B f y y' →
    op_type_equiv (sorts σ) B o0 x' y' →
    @op_type_equiv (sorts σ) A (λ s: sorts σ, @in_domain (A s) (B s) (e0 s) (f s)) o0 x y.
  Proof.
   induction o0.
    simpl.
    intros.
    unfold in_domain.
    rewrite H3, H4.
    assumption.
   simpl in *.
   repeat intro.
   unfold in_domain in H6.
   unfold respectful in H5.
   simpl in *.
   pose proof (H3 x0).
   pose proof (H3 y0). clear H3.
   pose proof (H4 x0).
   pose proof (H4 y0). clear H4.
   apply (IHo0 (x x0) (x' (f _ x0)) (y y0) (y' (f _ y0)) H7 H9).
   apply H5.
   assumption.
  Qed.

  Instance co: Congruence σ Φ.
  Proof with intuition.
   constructor.
    repeat intro.
    unfold in_domain.
    rewrite H3, H4...
   constructor; intro.
    unfold abstract_algebra.Setoid. apply _.
   unfold algebra_op.
   generalize (preserves σ A B f o).
   generalize (@algebra_propers σ B _ _ _ o).
   unfold algebra_op.
   generalize (H o), (H1 o).
   induction (σ o); simpl in *; repeat intro.
    apply _.
   apply (square _ _ _ _ _ (H4 x) (H4 y))...
  Qed.

  Definition image s (b: B s): Type := sigT (λ a, f s a = b).

  Lemma image_proper: ∀ s (x0 x' : B s), x0 = x' → iffT (image s x0) (image s x').
  Proof. intros ??? E. split; intros [v ?]; exists v; rewrite E in *; assumption. Qed.

  Instance: ClosedSubset image.
  Proof with intuition.
   constructor; repeat intro.
    split; intros [q p]; exists q; rewrite p...
   generalize (preserves σ A B f o).
   generalize (@algebra_propers σ B _ _ _ o).
   unfold algebra_op.
   generalize (H1 o), (H o).
   induction (σ o); simpl; intros.
    exists o1...
   destruct X.
   apply (@op_closed_proper σ B _ _ _ image image_proper _ (o1 z) (o1 (f _ x))).
    apply H3...
   apply IHo0 with (o2 x)...
   apply _.
  Qed.

  Definition quot_obj: algebras.Object σ := algebras.object σ A (algebra_equiv:=Φ). (* A/Φ *)
  Definition subobject: algebras.Object σ := algebras.object σ (ua_subalgebraT.carrier image).

  Program Definition back: subobject ⟶ quot_obj := λ _ X, projT1 (projT2 X).

  Next Obligation. Proof with try apply _; intuition.
   repeat constructor...
    intros [x [i E']] [y [j E'']] E.
    change (x = y) in E.
    change (f a i = f a j).
    rewrite E', E''...
   unfold ua_subalgebraT.impl.
   generalize (subset_closed image o).
   unfold algebra_op.
   generalize (H o) (H1 o) (preserves σ A B f o)
     (_: Proper (=) (H o)) (_: Proper (=) (H1 o)).
   induction (σ o); simpl; intros ? ? ? ? ?.
    intros [? E]. change (f _ x = f _ o0). rewrite E...
   intros ? [x [? E]]. apply IHo0... simpl in *. rewrite <- E...
  Defined.

  Program Definition forth: quot_obj ⟶ subobject :=
    λ a X, existT _ (f a X) (existT _ X (reflexivity _)).

  Next Obligation. Proof with try apply _; intuition.
   repeat constructor...
   unfold ua_subalgebraT.impl.
   generalize (subset_closed image o).
   unfold algebra_op.
   generalize (H o) (H1 o) (preserves σ A B f o)
     (_: Proper (=) (H o)) (_: Proper (=) (H1 o)).
   induction (σ o); simpl...
   apply IHo0...
  Qed.

  Theorem first_iso: categories.iso_arrows back forth.
  Proof.
   split. intro. reflexivity.
   intros ? [? [? ?]]. assumption.
  Qed.

End first_iso.
