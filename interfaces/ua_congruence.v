Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Record
  HoTTClasses.interfaces.ua_algebra
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Basics.Overture.

Import algebra_notations.

(* TODO. Fix doc. *)
Section congruence_property.
  Context {σ : Signature} (A : Algebra σ) (Φ : ∀ s, relation (A s)).

(** The relation family [Φ] satisfies the [CongruenceProperty f] with respect
    to the algebra operation [f : A s1 → A s2 → ... → A (s(n+1))] if

      [Φ s1 x1 y1 ∧ Φ s2 x2 y2 ∧ ... ∧ Φ sn xn yn] implies
      [Φ (s(n+1)) (f x1 x2 ... xn) (f y1 y2 ... yn)]. *)

  Definition CongruenceProperty {w : SymbolType σ} (f : Operation A w)
    : Type
    := ∀ (a b : FamilyProd A (dom_symboltype w)),
       for_all_2_family_prod A A Φ a b ->
       Φ (cod_symboltype w) (ap_operation f a) (ap_operation f b).

  Class HasCongruenceProperty : Type
    := has_congruence_property : ∀ (u : Symbol σ), CongruenceProperty (u^^A).
End congruence_property.

Arguments has_congruence_property {σ} A Φ {HasCongruenceProperty}.

Section congruence.
  Context {σ : Signature} (A : Algebra σ).

  (** The relation family [Φ] is a [IsCongruence] if [Φ s] it is a family of
      mere equivalence relations and [Φ] has the [CongruenceProperty f]
      for all the algebra operations [f]. *)

  Record Congruence : Type := BuildCongruence
    { relation_congruence : ∀ (s : Sort σ), relation (A s)
    ; is_mere_relation_congruence
        : ∀ (s : Sort σ), is_mere_relation (A s) (relation_congruence s)
    ; equivalence_congruence
        : ∀ (s : Sort σ), Equivalence (relation_congruence s)
    ; congruence_property : HasCongruenceProperty A relation_congruence }.

  Global Existing Instance is_mere_relation_congruence.

  Global Existing Instance equivalence_congruence.

  Global Existing Instance congruence_property.

  Global Coercion relation_congruence : Congruence >-> Funclass.

  Definition SigCongruence : Type :=
    { relation_congruence : ∀ (s : Sort σ), relation (A s)
    | { _ : ∀ (s : Sort σ), is_mere_relation (A s) (relation_congruence s)
      | { _ : ∀ (s : Sort σ), Equivalence (relation_congruence s)
        | HasCongruenceProperty A relation_congruence }}}.

  Lemma issig_congruence : Congruence <~> SigCongruence.
  Proof.
    apply symmetric_equiv.
    unfold SigCongruence.
    issig BuildCongruence relation_congruence is_mere_relation_congruence
            equivalence_congruence congruence_property.
  Defined.
End congruence.

Arguments BuildCongruence {σ} {A} relation_congruence
  {is_mere_relation_congruence} {equivalence_congruence} {congruence_property}.
