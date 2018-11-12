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
  HoTT.Spaces.Nat.

Import ne_list.notations.
Local Coercion ne_list.to_list : ne_list >-> list.

Require HoTTClasses.theory.ua_products.

Section contents.
  Local Generalizable Variable vo.
  Context σ `{@Algebra σ v vo}.

  Context (e: ∀ s, relation (v s)) `{∀ s, is_mere_relation _ (e s)}.

  Fixpoint aplist (c : sorts σ → Type) (u : list (sorts σ)) : Type :=
    match u with
    | nil => Unit
    | s :: u' => c s * aplist c u'
    end.

  Fixpoint aplist_map {u : list (sorts σ)} {c1 : sorts σ → Type}
      (c2 : sorts σ → Type) (f : ∀ s, c1 s → c2 s)
      : aplist c1 u → aplist c2 u :=
    match u with
    | nil => const tt
    | s :: u' => λ '(x,l), (f s x, aplist_map c2 f l)
    end.

(*
  Inductive arg_type_list (c : sorts σ → Type) : OpType (sorts σ) → Type :=
    | atl_nil : ∀ s, arg_type_list c (ne_list.one s)
    | atl_cons : ∀ s t, c s →
                 arg_type_list c t ->
                 arg_type_list c (ne_list.cons s t).

  Fixpoint arg_type_list_map {u : OpType (sorts σ)} {c1 c2 : sorts σ → Type}
      (f : ∀ s, c1 s → c2 s) (l : arg_type_list c1 u) : arg_type_list c2 u :=
    match l with
    | atl_nil s => atl_nil c2 s
    | atl_cons s u' x l' =>
        atl_cons c2 s u' (f s x) (arg_type_list_map f l')
    end.
*)

  Definition ne_list_front {A} : ne_list A → list A :=
    let fix aux (u : ne_list A) :=
      match u with
      | neone s => nil
      | s ::: u' => s :: aux u'
      end
    in aux.

  Fixpoint aplist_apply {c : sorts σ → Type} {u : OpType (sorts σ)}
      : op_type c u → aplist c (ne_list_front u) → c (result _ u) :=
    match u with
    | neone s => λ a _, a
    | s ::: u' => λ f '(x, l), aplist_apply (f x) l
    end.

  Lemma op_type_forall `{Funext} : ∀ (c : sorts σ → Type) (u : OpType (sorts σ))
      (f g : op_type c u),
      (∀ (a : aplist c (ne_list_front u)),
      aplist_apply f a = aplist_apply g a) -> f = g.
  Proof.
    intros c u.
    induction u; intros; simpl in *.
    exact (X tt).
    apply path_forall.
    intro x.
    apply IHu.
    intro.
    exact (X (x,a)).
  Qed.

(*
  Definition arg_list_apply {c : sorts σ → Type}
      : ∀ (w : OpType (sorts σ)), arg_type_list c w →
        op_type c w → c (result _ w) :=
    arg_type_list_rect c
      (λ w l, op_type c w → c (result _ w))
      (λ s, idmap)
      (λ s w' a l' r f, r (f a)).
*)

  Fixpoint aplist_forall2 {c1 c2 : sorts σ → Type} {u : list (sorts σ)}
      (R : ∀ s, c1 s -> c2 s -> Type) : aplist c1 u → aplist c2 u → Type :=
    match u with
    | nil => λ _ _, True
    | s :: u' => λ '(x1,l1) '(x2,l2), R s x1 x2 * aplist_forall2 R l1 l2
    end.

  Definition congruence_preserves :=
    ∀ (u : σ) (a b : aplist v (ne_list_front (σ u))) (f : op_type v (σ u)),
    aplist_forall2 e a b ->
    e (result (sorts σ) (σ u)) (aplist_apply f a) (aplist_apply f b).

  Class Congruence : Type :=
    { congruence_equivalence :> ∀ s, Equivalence (e s)
    ; congruence_respects : congruence_preserves }.

  Context `{Congruence}.

  Definition quotient_carriers (s : sorts σ) : Type := quotient (e s).

  Global Instance quotient_op_type_hset `{Funext}
    : ∀ l : ne_list.L (sorts σ), IsHSet (op_type quotient_carriers l).
  Proof. induction l; apply _. Qed.

  (* TODO: clean *)
  Lemma aplist_forall_refl : ∀ u (a : aplist v u), aplist_forall2 e a a.
  Proof.
    induction u.
    intros.
    reflexivity.
    intros; simpl in *.
    destruct a0.
    split.
    reflexivity.
    apply IHu.
  Qed.

  Lemma aplist_quotient_ind u (P : aplist quotient_carriers u -> Type)
      (sP : ∀ a, IsHProp (P a))
      (dclass : ∀ x, P (aplist_map quotient_carriers (λ s, class_of (e s)) x))
      : ∀ (a : aplist quotient_carriers u), P a.
  Proof.
    induction u.
    intros.
    simpl in *.
    unfold const in dclass.
    destruct a.
    apply (dclass tt).
    simpl in *.
    intros [a0 a1].
    revert a1.
    assert (∀ a0 a1, IsHProp (P (a0,a1))).
    intros.
    apply sP.
    refine (quotient_ind_prop (e a)
        (λ a0, ∀ a1, P (a0, a1))
        (λ a0,
          IHu (λ c, P (class_of (e a) a0, c))
              (X (class_of (e a) a0)) (λ c, dclass (a0, c))
        ) a0).
  Qed.

  Lemma quotient_aplist_apply_hprop :
    ∀ u (f f' : op_type quotient_carriers u)
      (a : aplist quotient_carriers (ne_list_front u)),
    IsHProp (aplist_apply f a = aplist_apply f' a).
  Proof.
    induction u.
    intros.
    simpl in *.
    pose (quotient_set (e t)).
    unfold IsHSet in i.
    unfold IsTrunc_internal in i.
    intros p1 p2.
    unfold IsTrunc_internal.
    apply (i f f' p1 p2).
    intros.
    simpl in *.
    pose (quotient_set (e t)).
    intros p1 p2.
    unfold IsTrunc_internal.
    destruct a as [a0 a1].
    specialize (IHu (f a0) (f' a0) a1).
    unfold IsHProp in IHu.
    unfold IsTrunc_internal in IHu.
    apply IHu.
  Qed.

  Definition rec_impl `{Funext} (u : σ) (f : op_type v (σ u)) :
    ∃ (g : op_type quotient_carriers (σ u)),
    ∀ (a : aplist v (ne_list_front (σ u))),
    aplist_apply g (aplist_map quotient_carriers (λ s, class_of (e s)) a) =
    class_of (e (result (sorts σ) (σ u))) (aplist_apply f a).
  Proof.
    destruct H1.
    unfold congruence_preserves in congruence_respects0.
    specialize (congruence_respects0 u).
    induction (σ u) as [| x w IH].
    intros.
    exists (class_of (e t) f).
    simpl in *.
    intros.
    reflexivity.
    simpl in *.

    assert (v x → ∀ (a b : aplist v (ne_list_front w)) (f0 : op_type v w),
        aplist_forall2 e a b →
        e (result (sorts σ) w) (aplist_apply f0 a) (aplist_apply f0 b)).
      intros.
      destruct (congruence_equivalence0 x).
      unfold Reflexive in Equivalence_Reflexive.
      pose (Equivalence_Reflexive X).
      pose (congruence_respects0 (X,a) (X,b) (λ _, f0) (e0, X0)).
      simpl in e1.
      apply e1.

    transparent assert (g : (quotient_carriers x → op_type quotient_carriers w)).
    refine (quotient_rec (e x) (λ a, (IH (f a) (X a)).1) _).
    intros.

    assert (X x0 = X y).
    assert (IsHProp (
      ∀ (a b : aplist v (ne_list_front w)) (f0 : op_type v w),
      aplist_forall2 e a b →
      e (result (sorts σ) w) (aplist_apply f0 a) (aplist_apply f0 b))).
    apply trunc_forall.
    unfold IsHProp in X1.
    unfold IsTrunc_internal in X1.
    specialize (X1 (X x0) (X y)).
    destruct X1.
    apply center.
    rewrite X1.

    apply op_type_forall.
    apply (aplist_quotient_ind (ne_list_front w)).
    apply quotient_aplist_apply_hprop.
    intros.
    destruct (IH (f x0) (X y)) as [Y1 Y2].
    destruct (IH (f y) (X y)) as [Y1' Y2'].
    unfold proj1_sig.
    rewrite Y2.
    rewrite Y2'.
    pose (aplist_forall_refl (ne_list_front w) x1).
    pose (congruence_respects0 (x0,x1) (y,x1) f (X0,a)).
    simpl in *.
    apply (related_classes_eq).
    apply e0.

    exists g.
    intros.
    destruct a as [a a'].
    unfold quotient_rec in g.
    unfold g.
    rewrite (quotient_ind_compute).
    simpl in *.

    destruct (IH (f a) (X a)) as [Y1 Y2].
    unfold proj1_sig.
    apply Y2.
  Qed.

  Instance quotient_ops `{Funext} : AlgebraOps σ quotient_carriers.
  Proof. intro u. apply rec_impl. apply (algebra_op u). Defined.

  Instance quotient_algebra `{Funext} : Algebra σ quotient_carriers.
  Proof. constructor. intros. apply _. Defined.
End contents.

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
