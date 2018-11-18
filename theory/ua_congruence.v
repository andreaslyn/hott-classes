Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.universal_algebra
  HoTTClasses.theory.ua_homomorphisms
  HoTT.Classes.interfaces.canonical_names
  HoTTClasses.theory.ua_subalgebra
  HoTT.HIT.quotient
  HoTT.Types.Arrow
  HoTT.UnivalenceAxiom
  HoTT.Types.Forall
  Classes.implementations.list
  HoTT.Spaces.Nat
  HoTT.Basics.Equivalences
  HoTT.Types.Sigma.

Require HoTTClasses.theory.ua_products.

Import ne_list.notations.

Section contents.
  Local Generalizable Variable vo.
  Context σ `{@Algebra σ v vo}.

  Context (e: ∀ s, relation (v s)) `{∀ s, is_mere_relation _ (e s)}.

  Fixpoint argprod (c : sorts σ → Type) (w : list (sorts σ)) : Type :=
    match w with
    | nil => Unit
    | s :: w' => c s * argprod c w'
    end.

  Fixpoint argprod_map {c1 : sorts σ → Type} {c2 : sorts σ → Type}
      {w : list (sorts σ)} (f : ∀ s, c1 s → c2 s)
      : argprod c1 w → argprod c2 w :=
    match w with
    | nil => const tt
    | s :: w' => λ '(x,l), (f s x, argprod_map f l)
    end.

  Fixpoint argprod_for_all {c : sorts σ → Type} {w : list (sorts σ)}
      (P : ∀ s, c s -> Type) : argprod c w → Type :=
    match w with
    | nil => λ _, True
    | s :: w' => λ '(x,l), P s x * argprod_for_all P l
    end.

  Fixpoint argprod_for_all_2 {c1 c2 : sorts σ → Type} {w : list (sorts σ)}
      (R : ∀ s, c1 s -> c2 s -> Type) : argprod c1 w → argprod c2 w → Type :=
    match w with
    | nil => λ _ _, True
    | s :: w' => λ '(x1,l1) '(x2,l2), R s x1 x2 * argprod_for_all_2 R l1 l2
    end.

  (** Uncurry of [op_type]. *)
  Fixpoint argprod_apply {c : sorts σ → Type} {w : OpType (sorts σ)}
      : op_type c w → argprod c (ne_list.front w) → c (result _ w) :=
    match w with
    | neone s => λ a _, a
    | s ::: w' => λ f '(x, l), argprod_apply (f x) l
    end.

  (** Funext for uncurried [op_type]s. *)
  Fixpoint argprod_apply_forall `{H : Funext}
      {c : sorts σ → Type} {w : OpType (sorts σ)}
      : ∀ (f g : op_type c w), (∀ a : argprod c (ne_list.front w),
            argprod_apply f a = argprod_apply g a) ->
        f = g :=
    match w with
    | neone s => λ f g h, h tt
    | s ::: w' =>
        λ f g h, path_forall f g (λ x,
                   argprod_apply_forall (f x) (g x) (λ a, h (x,a)))
    end.

  Definition congruence_property (w : OpType (sorts σ)) :=
    ∀ (f : op_type v w) (a b : argprod v (ne_list.front w)),
    argprod_for_all_2 e a b ->
    e (result (sorts σ) w) (argprod_apply f a) (argprod_apply f b).

  Global Instance congruence_property_prop (w : OpType (sorts σ))
      : IsHProp (congruence_property w).
  Proof. apply _. Defined.

  Class Congruence : Type :=
    { congruence_equivalence :> ∀ (s : sorts σ), Equivalence (e s)
    ; congruence_respect_ops : ∀ (u : σ), congruence_property (σ u) }.

  Context `{Congruence}.

  Definition carrier (s : sorts σ) : Type := quotient (e s).

  Global Instance quotient_op_type_hset `{Funext}
    : ∀ l : ne_list (sorts σ), IsHSet (op_type carrier l).
  Proof. induction l; apply _. Qed.

  Lemma argprod_for_all_2_reflexive
      : ∀ w (a : argprod v w), argprod_for_all_2 e a a.
  Proof with try reflexivity; auto.
    induction w; intros...
    destruct a0. split...
  Qed.

  Fixpoint argprod_quotient_ind_prop {w : list (sorts σ)}
      : ∀ (P : argprod carrier w -> Type) {sP : ∀ a, IsHProp (P a)}
          (dclass : ∀ x, P (argprod_map (λ s, class_of (e s)) x))
          (a : argprod carrier w), P a :=
    match w with
    | nil => λ P sP dclass 'tt, dclass tt
    | s :: w' => λ P sP dclass a,
      quotient_ind_prop (e s) (λ a0, ∀ a1, P (a0, a1))
        (λ a0, argprod_quotient_ind_prop
                (λ c, P (class_of (e s) a0, c)) (λ c, dclass (a0, c)))
        (fst a) (snd a)
    end.

  Lemma quotient_argprod_apply_hprop :
    ∀ w (f f' : op_type carrier w)
      (a : argprod carrier (ne_list.front w)),
    IsHProp (argprod_apply f a = argprod_apply f' a).
  Proof.
    induction w; intros.
    exact (quotient_set (e t) f f').
    apply IHw.
  Defined.

  Definition quotient_ops_property {w : OpType (sorts σ)}
    (f : op_type v w) (g : op_type carrier w) :=
    ∀ (a : argprod v (ne_list.front w)),
      argprod_apply g (argprod_map (λ s, class_of (e s)) a) =
      class_of (e (result (sorts σ) w)) (argprod_apply f a).

  Lemma congruence_property_from_cons {s : sorts σ} {w : OpType (sorts σ)}
      : congruence_property (s ::: w) → v s → congruence_property w.
  Proof.
    intros P x f' a b h.
    exact (P (λ _, f') (x,a) (x,b) (Equivalence_Reflexive x, h)).
  Defined.

  Fixpoint rec_impl `{Funext} {w : OpType (sorts σ)} :
    congruence_property w ->
    ∀ (f : op_type v w), ∃ (g : op_type carrier w), quotient_ops_property f g.
  Proof. refine (
      match w with
      | neone s => λ P f, (class_of (e s) f; λ a, 1%path)
      | s ::: w' => λ P f,
        (* Introduce lambda abstraction to induce correct obligations. *)
        (λ R, (quotient_rec (e s) (λ x, (rec_impl _ w'
                (congruence_property_from_cons P x) (f x)).1) R; _)) _
      end
    ).
    intros [x a].
    apply (rec_impl H2 w' (congruence_property_from_cons P x) (f x)).
    intros x y E.
    apply argprod_apply_forall.
    apply argprod_quotient_ind_prop.
    apply quotient_argprod_apply_hprop.
    intros a.
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
    intro u.
    apply rec_impl.
    apply congruence_respect_ops.
    apply (algebra_op u).
  Defined.

  Global Instance quotient_algebra `{Funext} : Algebra σ carrier.
  Proof. constructor. intros. apply _. Defined.
End contents.

Definition quotient_homomorphism {σ : Signature}
    {A : sorts σ → Type} {As : AlgebraOps σ A} {AA : Algebra σ A}
    (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
    : ∀ s, A s → carrier σ e s :=
  λ s, (quotient_ump (e s) (BuildhSet (carrier σ e s)) idmap).1.

Global Instance quotient_is_homomorphism `{Funext} {σ : Signature}
  {A : sorts σ → Type} {As : AlgebraOps σ A} {AA : Algebra σ A}
  (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
  {C : Congruence σ e}
  : HomoMorphism σ A (carrier σ e) (quotient_homomorphism e).
Proof.
  intro u.
  unfold quotient_homomorphism.
  unfold quotient_ops, algebra_op.
  set (ao := As u).
  set (co := congruence_respect_ops _ _ u).
  clearbody ao co.
  induction (σ u); simpl; intros; auto.
Qed.

Definition quotient_mapout_homomorphism `{Funext} {σ : Signature}
    {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
    {AA : Algebra σ A} {BB : Algebra σ B}
    (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
    (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}
    (P : ∀ s x y, e s x y → f s x = f s y)
    : ∀ s, carrier σ e s → B s :=
  λ s, (quotient_ump (e s) (BuildhSet (B s)))^-1 (f s; P s).

Global Instance quotient_mapout_is_homomorphism `{Funext} {σ : Signature}
    {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
    {AA : Algebra σ A} {BB : Algebra σ B}
    (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
    {C : Congruence σ e}
    (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}
    (P : ∀ s x y, e s x y → f s x = f s y)
    : HomoMorphism σ (carrier σ e) B (quotient_mapout_homomorphism e f P).
Proof.
  intro u.
  unfold quotient_ops, algebra_op.
  generalize (preserves σ A B f u).
  set (ao := As u).
  set (bo := Bs u).
  set (co := congruence_respect_ops _ _ u).
  clearbody ao bo co.
  induction (σ u); intro Q.
  assumption.
  refine (quotient_ind_prop (e t) _ _).
  intro x.
  set (co' := congruence_property_from_cons σ e co x).
  exact (IHo (ao x) (bo (f t x)) co' (Q x)).
Qed.

Lemma quotient_property_rl `{Funext} {σ : Signature}
  {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
  {AA : Algebra σ A} {BB : Algebra σ B}
  (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
  {C : Congruence σ e}
  : (∃ (f : ∀ s, A s → B s) (F : HomoMorphism σ A B f),
    ∀ s x y, e s x y → f s x = f s y)
    → ∃ (g : ∀ s, carrier σ e s → B s), HomoMorphism σ (carrier σ e) B g.
Proof.
  intros [f [F P]].
  exists (quotient_mapout_homomorphism e f P).
  apply _.
Defined.

Definition quotient_factor_homomorphism `{Funext} {σ : Signature}
    {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
    {AA : Algebra σ A} {BB : Algebra σ B}
    (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
    {C : Congruence σ e}
    (g : ∀ s, carrier σ e s → B s) {G : HomoMorphism σ (carrier σ e) B g}
    : ∀ s, A s → B s :=
  λ s, (quotient_ump (e s) (BuildhSet (B s)) (g s)).1.

Lemma quotient_factor_homomorphism_is_factor `{Funext} {σ : Signature}
  {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
  {AA : Algebra σ A} {BB : Algebra σ B}
  (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
  {C : Congruence σ e}
  (g : ∀ s, carrier σ e s → B s) {G : HomoMorphism σ (carrier σ e) B g}
  : quotient_factor_homomorphism e g = λ s, g s ∘ quotient_homomorphism e s.
Proof. reflexivity. Defined.

Global Instance quotient_factor_is_homomorphism `{Funext} {σ : Signature}
  {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
  {AA : Algebra σ A} {BB : Algebra σ B}
  (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
  {C : Congruence σ e}
  (g : ∀ s, carrier σ e s → B s) {G : HomoMorphism σ (carrier σ e) B g}
  : HomoMorphism σ A B (quotient_factor_homomorphism e g).
Proof.
  refine (transport (λ h, HomoMorphism σ A B h)
          ((quotient_factor_homomorphism_is_factor e g)^)
          (compose_homomorphisms _ _ _ _ _ _)).
Defined.

Lemma quotient_property_lr `{Funext} {σ : Signature}
  {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
  {AA : Algebra σ A} {BB : Algebra σ B}
  (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
  {C : Congruence σ e}
  : (∃ (g : ∀ s, carrier σ e s → B s), HomoMorphism σ (carrier σ e) B g) →
    ∃ (f : ∀ s, A s → B s) (F : HomoMorphism σ A B f),
      ∀ s x y, e s x y → f s x = f s y.
Proof.
  refine (λ '(g;G),
    (quotient_factor_homomorphism e g ;
     quotient_factor_is_homomorphism e g ;
     λ s x y E, transport (λ z, g s (class_of (e s) x) = g s z)
                 (related_classes_eq (e s) E) idpath)).
Defined.

Lemma quotient_property_sect_lr `{Funext} {σ : Signature}
  {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
  {AA : Algebra σ A} {BB : Algebra σ B}
  (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
  {C : Congruence σ e}
  (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}
  : Sect (quotient_property_lr e) (quotient_property_rl e).
Proof.
  intros [g G].
  apply path_sigma_hprop.
  apply path_forall.
  intro s.
  apply (eissect (quotient_ump (e s) (BuildhSet (B s)))).
Defined.

Lemma quotient_property_sect_rl `{Funext} {σ : Signature}
  {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
  {AA : Algebra σ A} {BB : Algebra σ B}
  (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
  {C : Congruence σ e}
  (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}
  : Sect (quotient_property_rl e) (quotient_property_lr e).
Proof.
  intros [h [H0 H1]].
  apply path_sigma_hprop.
  apply path_forall.
  intro s.
  apply path_forall.
  intro x.
  reflexivity.
Defined.

Lemma quotient_property `{Funext} {σ : Signature}
  {A B : sorts σ → Type} {As : AlgebraOps σ A} {Bs : AlgebraOps σ B}
  {AA : Algebra σ A} {BB : Algebra σ B}
  (e : ∀ s, relation (A s)) {R : ∀ s, is_mere_relation _ (e s)}
  {C : Congruence σ e}
  (f : ∀ s, A s → B s) {F : HomoMorphism σ A B f}
  (P : ∀ s a b, e s a b → f s a = f s b)
  : (∃ (f : ∀ s, A s → B s) (F : HomoMorphism σ A B f),
    ∀ s (x y : A s), e s x y → f s x = f s y)
   <~>
    ∃ (g : ∀ s, carrier σ e s → B s), HomoMorphism σ (carrier σ e) B g.
Proof.
  apply (equiv_adjointify (quotient_property_rl e) (quotient_property_lr e)).
  apply (quotient_property_sect_lr e f).
  apply (quotient_property_sect_rl e f).
Defined.

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
