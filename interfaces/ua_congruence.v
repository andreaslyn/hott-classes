Require Import
  Coq.Unicode.Utf8
  HoTTClasses.interfaces.ua_algebra
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Basics.Overture.

Import algebra_notations.

(* TODO. Fix doc. *)

(** This section develops the [quotient_algebra] instance of the [Algebra] type
    class. *)

Section congruence.
  Context {σ : Signature} (A : Algebra σ) (Φ : ∀ s, relation (A s)).

  (** The relation family [Φ] satisfies the [CongruenceProperty f] with respect
      to the algebra operation [f : A s1 → A s2 → ... → A (s(n+1))] if

        [Φ s1 x1 y1 ∧ Φ s2 x2 y2 ∧ ... ∧ Φ sn xn yn] implies
        [Φ (s(n+1)) (f x1 x2 ... xn) (f y1 y2 ... yn)]. *)

  Definition CongruenceProperty {w : SymbolType σ} (f : Operation A w) : Type
    := ∀ (a b : FamilyProd A (dom_symboltype w)),
       for_all_2_family_prod A A Φ a b ->
       Φ (cod_symboltype w) (ap_operation f a) (ap_operation f b).

  (** The relation family [Φ] is a [IsCongruence] if [Φ s] it is a family of
      mere equivalence relations and [Φ] has the [CongruenceProperty f]
      for all the algebra operations [f]. *)

  Class IsCongruence {M : ∀ s, is_mere_relation (A s) (Φ s)}
      {E : ∀ s, Equivalence (Φ s)} : Type
      := congruence_properties : ∀ (u : Symbol σ), CongruenceProperty (u^^A).
End congruence.

Arguments congruence_properties {σ} A Φ {M} {E} {IsCongruence}.
