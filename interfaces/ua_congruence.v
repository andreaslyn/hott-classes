Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.implementations.ua_carrier_product
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Basics.Overture.

Import algebra_notations.

(* TODO. Fix doc. *)

(** This section develops the [quotient_algebra] instance of the [Algebra] type
    class. *)

Section congruence.
  Context
    {σ : Signature} (A : Algebra σ) (Φ : ∀ s, relation (A s)).

  (** The relation family [Φ] satisfies the [congruence_property f] with respect
      to the algebra operation [f : A s1 → A s2 → ... → A (s(n+1))] if

        [Φ s1 x1 y1 ∧ Φ s2 x2 y2 ∧ ... ∧ Φ sn xn yn] implies
        [Φ (s(n+1)) (f x1 x2 ... xn) (f y1 y2 ... yn)]. *)

  Definition congruence_property {w : symboltype σ} (f : Operation A w) :=
    ∀ (a b : CProd A (dom_symboltype w)),
    for_all_2_cprod Φ a b ->
    Φ (cod_symboltype w) (apply_cprod f a) (apply_cprod f b).

  (** The relation family [Φ] is a [IsCongruence] if [Φ s] it is a family of
      mere equivalence relations and [Φ] has the [congruence_property f]
      for all the algebra operations [f]. *)

  Class IsCongruence `{!∀ s, is_mere_relation (A s) (Φ s)}
      `{!∀ s, Equivalence (Φ s)} : Type :=
    congruence_property_family : ∀ (u : symbol σ), congruence_property (u^^A).
End congruence.

Global Arguments congruence_property {σ} {A} Φ {w} f.
