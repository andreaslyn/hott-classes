(* To be imported qualified. *)
Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.universal_algebra
  HoTTClasses.categories.varieties
  HoTTClasses.misc.workaround_tactics
  HoTTClasses.theory.ua_homomorphisms
  HoTT.Spaces.Nat
  HoTT.Basics.Equivalences.

Inductive op := mult | one.

Definition sig: Signature := single_sorted_signature
  (λ u, match u with one => O | mult => 2%nat end).

Section laws.
  Global Instance: SgOp (Term0 sig nat tt) :=
    fun x => App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).
  Global Instance: MonUnit (Term0 sig nat tt) := Op sig nat one.

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Type :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z)
    | e_mult_1_l: Laws (mon_unit & x === x)
    | e_mult_1_r: Laws (x & mon_unit === x).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.
Definition Object := varieties.Object theory.

Local Hint Extern 3 => progress simpl : typeclass_instances.

(* Now follow a series of encoding/decoding functions to convert between the
 specialized Monoid/MonoidMorphism type classes and the universal
 Algebra/InVariety/HomoMorphism type classes instantiated with the above
 signature and theory. *)

Instance encode_operations A `{!SgOp A} `{!MonUnit A}: AlgebraOps sig (λ _, A) :=
  λ u, match u with mult => (&) | one => mon_unit: A end.

Section decode_operations.
  Context `{AlgebraOps theory A}.
  Global Instance: MonUnit (A tt) := algebra_op one.
  Global Instance: SgOp (A tt) := algebra_op mult.
End decode_operations.

Section monoid_morphism.
  Context (A B : Type) {Aop : SgOp A} {Bop : SgOp B}
      {Aunit : MonUnit A} {Bunit : MonUnit B}.

  Class MonoidMorphism (f : A → B) :=
    { monoid_morphism_domain: Monoid A
    ; monoid_morphism_codomain: Monoid B
    ; monoid_morphism:> HomoMorphism sig (const A) (const B) (const f) }.

  Coercion monoid_morphism : MonoidMorphism >-> HomoMorphism.
End monoid_morphism.

Section encode_variety_and_ops.
  Context A `{Monoid A}.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. constructor. intro. apply _. Qed.

  Global Instance encode_variety_and_ops: InVariety theory (const A) | 10.
  Proof.
   constructor. apply _.
   intros ? [] ?; simpl; unfold algebra_op; simpl.
     apply associativity.
    apply left_identity.
   apply right_identity.
  Qed.

  Definition object: Object := varieties.object theory (const A).
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{!Monoid (A tt)}: Algebra theory A .
Proof. constructor; intros []; apply _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: Monoid (A tt) | 10.
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 constructor.
   constructor.
     apply _.
    intro. apply_simplified (laws _ e_mult_assoc).
   intro. apply_simplified (laws _ e_mult_1_l)...
  intro. apply_simplified (laws _ e_mult_1_r)...
Qed.

Instance monoid_morphism_preserving
  {A B : Type} (f : A → B)
  `{MonoidMorphism A B f}: MonoidPreserving f.
Proof.
 constructor.
 intros x y.
 apply_simplified (preserves sig (const A) (const B) (const f) mult).
 apply_simplified (preserves sig (const A) (const B) (const f) one).
Qed.

Instance id_monoid_morphism `{Monoid A}: MonoidMorphism A A id.
Proof. repeat (split; try apply _); easy. Qed.

(* Finally, we use these encoding/decoding functions to specialize some universal results: *)
Section specialized.
  Context `{MonUnit A} `{SgOp A}
     `{MonUnit B} `{SgOp B}
     `{MonUnit C} `{SgOp C}
    (f : A → B) (g : B → C).

  Instance compose_monoid_morphism:
    MonoidMorphism A B f → MonoidMorphism B C g → MonoidMorphism A C (g ∘ f).
  Proof.
    intros.
    pose proof (@compose_homomorphisms theory _ _ _ _ _ _ _ _ X X0) as PP.
    pose proof (@monoid_morphism_domain _ _ _ _ _ _ f).
    pose proof (@monoid_morphism_codomain _ _ _ _ _ _ f).
    pose proof (@monoid_morphism_codomain _ _ _ _ _ _ g).
    destruct X, X0. constructor; assumption.
  Qed.

  Lemma invert_monoid_morphism `{IsEquiv A B f}
    : MonoidMorphism A B f → MonoidMorphism B A (f^-1).
  Proof with try assumption.
    intros.
    pose proof (@invert_homomorphism theory _ _ _ _ _ _ X) as Q.
    pose proof monoid_morphism_domain.
    pose proof monoid_morphism_codomain.
    destruct X.
    destruct Q.
    constructor...
    constructor...
  Qed.
End specialized.

Hint Extern 4 (MonoidMorphism (_ ∘ _)) => class_apply @compose_monoid_morphism : typeclass_instances.
Hint Extern 4 (MonoidMorphism (_^-1)) => class_apply @invert_monoid_morphism : typeclass_instances.
