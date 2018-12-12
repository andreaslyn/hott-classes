Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Equivalences
  HoTT.HProp
  HoTT.Types.Universe
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Record
  HoTTClasses.interfaces.relation
  HoTTClasses.interfaces.ua_algebra
  HoTT.Classes.interfaces.abstract_algebra.

Import algebra_notations.

Section property_congruence.
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

  Global Instance trunc_has_congruence_property `{Funext}
    {n} `{∀ s x y, IsTrunc n (Φ s x y)}
    : IsTrunc n HasCongruenceProperty.
  Proof.
    apply trunc_forall.
  Defined.
End property_congruence.

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
    ; property_congruence : HasCongruenceProperty A relation_congruence }.

  Global Existing Instance is_mere_relation_congruence.

  Global Existing Instance equivalence_congruence.

  Global Existing Instance property_congruence.

  Global Coercion relation_congruence : Congruence >-> Funclass.
End congruence.

Arguments BuildCongruence {σ} {A} relation_congruence
  {is_mere_relation_congruence} {equivalence_congruence} {property_congruence}.

Arguments relation_congruence {σ} {A}.
Arguments is_mere_relation_congruence {σ} {A}.
Arguments equivalence_congruence {σ} {A}.
Arguments property_congruence {σ} {A}.

Section path_congruence.
  Context {σ : Signature} (A : Algebra σ).

  Definition SigCongruence : Type :=
    { relation_congruence : ∀ (s : Sort σ), relation (A s)
    | { _ : ∀ (s : Sort σ), is_mere_relation (A s) (relation_congruence s)
      | { _ : ∀ (s : Sort σ), Equivalence (relation_congruence s)
        | HasCongruenceProperty A relation_congruence }}}.

  Lemma issig_congruence : Congruence A <~> SigCongruence.
  Proof.
    apply symmetric_equiv.
    unfold SigCongruence.
    issig (@BuildCongruence σ A)
            (@relation_congruence σ A) (@is_mere_relation_congruence σ A)
            (@equivalence_congruence σ A) (@property_congruence σ A).
  Defined.

  Ltac change_issig_congruence Φ :=
    change (property_congruence Φ) with (issig_congruence Φ).2.2.2 in *;
    change (equivalence_congruence Φ) with (issig_congruence Φ).2.2.1 in *;
    change (is_mere_relation_congruence Φ) with (issig_congruence Φ).2.1 in *;
    change (relation_congruence Φ) with (issig_congruence Φ).1 in *.

  Lemma path_congruence `{Univalence} (Φ Ψ : Congruence A)
    (e : ∀ s (x y : A s), Φ s x y <-> Ψ s x y) : Φ = Ψ.
  Proof.
    apply (ap issig_congruence)^-1.
    apply path_sigma_hprop.
    simpl.
    funext s x y.
    apply (path_universe (equiv_equiv_iff_hprop _ _ (e s x y))).
  Defined.
End path_congruence.
