Require
  HoTTClasses.categories.varieties.
Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.universal_algebra
  HoTTClasses.theory.ua_homomorphisms
  HoTTClasses.misc.workaround_tactics
  HoTT.Spaces.Nat.

Inductive op := mult.

Definition sig: Signature := single_sorted_signature
  (λ u, match u with mult => 2%nat end).

Section laws.
  Global Instance: SgOp (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Type :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.
Definition Object := varieties.Object theory.

Instance encode_operations A `{!SgOp A}: AlgebraOps sig (λ _, A) :=
  λ u, match u with mult => (&) end.

Section decode_operations.
  Context `{AlgebraOps theory A}.
  Global Instance: SgOp (A tt) := algebra_op mult.
End decode_operations.

Section semigroup_morphism.
  Context (A B : Type) {Aop : SgOp A} {Bop : SgOp B}.

  Class SemiGroupMorphism (f : A → B) :=
    { semigroup_morphism_domain: SemiGroup A
    ; semigroup_morphism_codomain: SemiGroup B
    ; semigroup_morphism:> HomoMorphism sig (const A) (const B) (const f) }.

  Coercion semigroup_morphism : SemiGroupMorphism >-> HomoMorphism.
End semigroup_morphism.

Section encode_variety_and_ops.
  Context A `{SemiGroup A}.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. constructor; intros []; simpl; apply _. Qed.

  Global Instance encode_variety_and_ops: InVariety theory (const A).
  Proof.
   constructor. apply _.
   intros ? [] ?; simpl; unfold algebra_op; simpl.
   apply associativity.
  Qed.

  Definition object: Object := varieties.object theory (const A).
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{!SemiGroup (A tt)}: Algebra theory A .
Proof. constructor; intros []; simpl in *; try apply _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: SemiGroup (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 constructor; try apply _.
  intro. apply_simplified (laws _ e_mult_assoc).
Qed.

Instance semigroup_morphism_preserving
  {A B : Type} (f : A → B)
  `{SemiGroupMorphism A B f}: SemiGroupPreserving f.
Proof.
 intros x y.
 apply_simplified (preserves sig (const A) (const B) (const f) mult).
Qed.

Instance id_sg_morphism `{SemiGroup A}: SemiGroupMorphism A A id.
Proof. repeat (split; try apply _); easy. Qed.

Section specialized.
  Context `{SgOp A} `{SgOp B} `{SgOp C} (f : A → B) (g : B → C).

  Instance compose_sg_morphism:
    SemiGroupMorphism A B f →
    SemiGroupMorphism B C g →
    SemiGroupMorphism A C (g ∘ f).
  Proof.
    intros.
    destruct X, X0.
    pose proof (@compose_homomorphisms theory _ _ _ _ _ _ _ _ semigroup_morphism0 semigroup_morphism1) as PP.
    constructor; assumption.
  Qed.

  Instance invert_sg_morphism {A B : Type} (f : A → B) `{IsEquiv A B f}
    `{SemiGroupMorphism A B f} : SemiGroupMorphism B A (f^-1).
  Proof.
    intros.
    pose proof (@invert_homomorphism theory _ _ _ _ _ _ H3) as Q.
    pose proof semigroup_morphism_domain.
    pose proof semigroup_morphism_codomain.
    constructor.
    apply (X0 A0 B0 _ _ f0 H3).
    apply (X A0 B0 _ _ f0 H3).
    assumption.
  Qed.
End specialized.

Hint Extern 4 (SemiGroupMorphism (_ ∘ _)) => class_apply @compose_sg_morphism : typeclass_instances.
Hint Extern 4 (SemiGroupMorphism (_^-1)) => class_apply @invert_sg_morphism : typeclass_instances.
