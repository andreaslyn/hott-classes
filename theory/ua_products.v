Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_basic
  HoTTClasses.theory.ua_homomorphisms
  HoTT.Types.Forall.

Section algebras.
  Context
    (sig: Signature) (I: Type) (carriers: I → sorts sig → Type)
    `{F : Funext}
    `{∀ i, AlgebraOps sig (carriers i)}
    `{AA : ∀ i, Algebra sig (carriers i)}.

  Definition carrier: sorts sig → Type := λ sort, ∀ i: I, carriers i sort.

  Fixpoint rec_impl u: (∀ i, op_type (carriers i) u) → op_type carrier u :=
    match u return (∀ i, op_type (carriers i) u) → op_type carrier u with
    | ne_list.one _ => id
    | ne_list.cons _ g => λ X X0, rec_impl g (λ i, X i (X0 i))
    end.

  Global Instance product_ops: AlgebraOps sig carrier := λ u, rec_impl (sig u) (λ i, algebra_op u).

  Global Instance product_algebra : Algebra sig carrier := {}.

  Lemma preservation i u: Preservation sig carrier (carriers i) (λ _ v, v i) (algebra_op u) (algebra_op u).
   unfold product_ops, algebra_op.
   set (select_op := λ i0 : I, H i0 u).
   assert (H i u = select_op i) as H2. reflexivity.
   rewrite H2.
   clearbody select_op.
   generalize select_op.
   set (X := operation_type sig u).
   induction X.
   simpl. reflexivity.
   intros. intro. apply IHX.
  Qed.

  Lemma algebra_projection_morphisms i
    : HomoMorphism sig carrier (carriers i) (λ a v, v i).
  Proof. intro u. apply preservation. Qed.
End algebras.

Section varieties.
  Context
    (et: EquationalTheory)
    (I: Type) (carriers: I → sorts et → Type)
    `{F : Funext}
    `(∀ i, AlgebraOps et (carriers i))
    `(∀ i, InVariety et (carriers i)).

  Notation carrier := (carrier et I carriers).

  Fixpoint nqe {t}: op_type carrier t → (∀ i, op_type (carriers i) t) → Type :=
   match t with
   | ne_list.one _ => λ f g, ∀ i, f i = g i
   | ne_list.cons _ _ => λ f g, ∀ tuple, nqe (f tuple) (λ i, g i (tuple i))
   end. (* todo: rename *)

  Lemma nqe_always {t} (term: Term _ nat t) vars:
    nqe (eval et vars term) (λ i, eval et (λ sort n, vars sort n i) term).
  Proof.
   induction term; simpl in *.
     reflexivity.
    set (k := (λ i : I,
        eval et (λ (sort: sorts et) (n : nat), vars sort n i) term1
          (eval et vars term2 i))).
    cut (nqe (eval et vars term1 (eval et vars term2)) k).
    set (p := λ i : I, eval et (λ (sort : sorts et) (n : nat), vars sort n i) term1
        (eval et (λ (sort : sorts et) (n : nat), vars sort n i) term2)).
    assert (p = k) as P.
    apply path_forall.
    subst p k.
    intro i.
    rewrite IHterm2.
    reflexivity.
    rewrite P; trivial.
    apply IHterm1.
    change (nqe (rec_impl et _ _ (et u) (λ i : I, @algebra_op _ (carriers i) _ u)) (λ i : I, @algebra_op _ (carriers i) _ u)).
    generalize (λ i: I, @algebra_op et (carriers i) _ u).
    induction (et u); simpl. reflexivity.
    intros. apply IHo.
  Qed.

  Lemma component_equality_to_product t
    (A A': op_type carrier t)
    (B B': ∀ i, op_type (carriers i) t):
    (∀ i, B i = B' i) → nqe A B → nqe A' B' → A = A'.
  Proof with auto.
   induction t; simpl in *; intros BE ABE ABE'; apply path_forall.
   intro. rewrite ABE, ABE'...
   intros x.
   apply (IHt (A x) (A' x) (λ i, B i (x i)) (λ i, B' i (x i)))...
   intros. rewrite BE. reflexivity.
  Qed.

  Lemma laws_hold s : et_laws et s → ∀ vars, @eval_stmt et _ (product_ops et I carriers) vars s.
  Proof.
   intros.
   pose proof (λ i, variety_laws s X (λ sort n, vars sort n i)). clear X.
   assert (∀ i : I, eval_stmt (et_sig et)
       (λ (sort : sorts (et_sig et)) (n : nat), vars sort n i)
       (entailment_as_conjunctive_statement (et_sig et) s)).
     intros.
     apply boring_eval_entailment.
     apply (X0 i). clear X0.
   apply boring_eval_entailment.
   destruct s.
   simpl in *.
   destruct entailment_conclusion.
   simpl in *.
   destruct proj2_sig.
   simpl in *.
   intro.
   apply component_equality_to_product with
       (λ i, eval et (λ sort n, vars sort n i) fst) (λ i, eval et (λ sort n, vars sort n i) snd).
   intro.
   apply X. clear X. simpl.
   induction entailment_premises... simpl in *.
   constructor.
   simpl.
   rewrite <- (nqe_always (Datatypes.fst (projT2 a)) vars i).
   rewrite <- (nqe_always (Datatypes.snd (projT2 a)) vars i).
   split.
   simpl in X0.
   destruct X0.
   rewrite fst0.
   reflexivity.
   apply IHentailment_premises.
   apply X0.
   apply nqe_always.
   apply nqe_always.
  Qed. (* todo: clean up! also, we shouldn't have to go through boring.. *)

  Global Instance product_variety : InVariety et carrier.
  Proof with apply _.
   constructor. apply product_algebra... intro i.
   apply laws_hold.
  Qed.
End varieties.
