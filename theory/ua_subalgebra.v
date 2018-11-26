Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_basic
  HoTTClasses.theory.ua_homomorphisms
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Types.Sigma.

Section subalgebras.
  Context (sign : Signature) `{Algebra sign A} (P: ∀ s, A s → Type).

  (* We begin by describing what it means for P to be a proper closed subset: *)

  Fixpoint op_closed {u: OpType (sorts sign)}: op_type A u → Type :=
    match u with
    | ne_list.one x => P x
    | ne_list.cons _ _ => λ d, ∀ z, P _ z → op_closed (d z)
    end.

  Class ClosedSubset `{∀ s x, IsHProp (P s x)} : Type :=
    subset_closed: ∀ u, op_closed (algebra_op u).

  (* Now suppose P is closed in this way. *)

  Context `{ClosedSubset}.

  Global Instance op_closed_hprop `{Funext} (u : OpType (sorts sign))
      (bo : op_type A u) : IsHProp (op_closed bo).
  Proof. induction u; apply _. Defined.

  (* Our new algebra's elements are just those for which P holds: *)

  Definition carrier s := {x | P s x}.

  (* We can implement closed operations in the new algebra: *)

  Fixpoint close_op {d}: ∀ (u: op_type A d), op_closed u → op_type carrier d :=
    match d with
    | ne_list.one _ => λ u c, exist _ u (c)
    | ne_list.cons _ _ => λ u c X, close_op (u (pr1 X)) (c (pr1 X) (pr2 X))
    end.

  Global Instance impl: AlgebraOps sign carrier := λ u, close_op (algebra_op u) (subset_closed u).

  Lemma close_op_proper `{Funext} d (o0 o1: op_type A d)
    (P': op_closed o0) (Q: op_closed o1): o0 = o1 → close_op o0 P' = close_op o1 Q.
  Proof.
   induction d. simpl in *.
   intros. apply path_sigma_hprop. assumption.
   intro.
   apply path_forall.
   intro.
   apply IHd.
   apply (apD10 X x.1).
  Qed.

  Global Instance subalgebra: Algebra sign carrier.
  Proof. intro s. apply _. Qed.

  (* And we have the obvious projection morphism: *)

  Definition proj s := @pr1 (A s) (P s).

  Global Instance: HomoMorphism sign carrier A proj.
  Proof with try apply _.
   intro u.
   unfold impl, algebra_op.
   generalize (subset_closed u).
   unfold algebra_op.
   generalize (H u).
   induction (sign u); simpl; intros; auto...
  Qed.

(* TODO. Use IsEmbedding?
  (* Which is mono because proj is injective. *)
  Instance: Injective (proj i).
  Proof.
    split.
     firstorder.
    apply (@homo_proper sign carrier A
      (fun s : sorts sign => @sig_equiv (A s) (e s) (P s)) _ _ _ _).
    apply _.
  Qed.

  Global Instance: Mono (algebras.arrow _ proj) := {}.
  Proof.
   apply forget_algebra.mono.
   apply categories.product.mono.
   intro. apply setoids.mono.
   simpl. apply _.
  Qed. (* this really should be completely automatic. *)
*)
End subalgebras.

Hint Unfold carrier: typeclass_instances.
