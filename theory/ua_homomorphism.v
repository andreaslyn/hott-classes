(** This file implements algebra [Homomorphism] and [IsIsomorphism].
    It developes basic algebra homomorphisms and isomorphims. The main
    theorem in this file is the [path_isomorphism] theorem, which
    states that there is a path between isomorphic algebras. *)

Require Import
  HoTT.Basics.Equivalences
  HoTT.Basics.PathGroupoids
  HoTT.Types.Forall
  HoTT.Types.Arrow
  HoTT.Types.Universe
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.Fibrations
  HoTT.HSet
  HoTT.Tactics
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra.

Import algebra_notations ne_list.notations.

Section is_homomorphism.
  Context {σ} {A B : Algebra σ} (f : ∀ (s : Sort σ), A s → B s).

(** The family of functions [f] above is [OpPreserving α β] with
    respect to operations [α : A s1 → A s2 → ... → A sn → A t] and
    [β : B s1 → B s2 → ... → B sn → B t] if

    <<
      f t (α x1 x2 ... xn) = β (f s1 x1) (f s2 x2) ... (f sn xn)
    >>
*)

  Fixpoint OpPreserving {w : SymbolType σ}
    : Operation A w → Operation B w → Type
    := match w with
       | [:s:] => λ α β, f s α = β
       | s ::: y => λ α β, ∀ (x : A s), OpPreserving (α x) (β (f s x))
       end.

  Global Instance trunc_oppreserving `{Funext} {n : trunc_index}
    `{!IsTruncAlgebra n.+1 B} {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    : IsTrunc n (OpPreserving α β).
  Proof.
    intros. induction w; exact _.
  Defined.

(** The family of functions [f : ∀ (s : Sort σ), A s → B s] above is
    a homomorphism if for each function symbol [u : Symbol σ], it is
    [OpPreserving (u^^A) (u^^B)] with respect to the algebra
    operations [u^^A] and [u^^B] corresponding to [u]. *)

  Definition IsHomomorphism : Type
    := ∀ (u : Symbol σ), OpPreserving (u^^A) (u^^B).

  Global Instance trunc_is_homomorphism `{Funext} {n : trunc_index}
    `{!IsTruncAlgebra n.+1 B}
    : IsTrunc n IsHomomorphism.
  Proof.
    intros. apply trunc_forall.
  Defined.
End is_homomorphism.

(** Given algebras [A B : Algebra σ] a homomorphism [Homomorphism A B]
    is a family of functions [f : ∀ (s : Sort σ), A s → B s] where
    [IsHomomorphism f] holds. *)

Record Homomorphism {σ} {A B : Algebra σ} : Type := BuildHomomorphism
  { def_hom : ∀ (s : Sort σ), A s → B s
  ; is_homomorphism_hom : IsHomomorphism def_hom }.

Arguments Homomorphism {σ}.

Arguments BuildHomomorphism {σ A B} def_hom is_homomorphism_hom.

(** We declare an implicit coercion from [Homomorphism A B] to the
    family of functions [∀ s, A s → B s]. *)

Global Coercion def_hom : Homomorphism >-> Funclass.

(** To find a path between two homomorphisms [f g : Homomorphism A B]
    it suffices to find a path between the defining families of
    functions and a path between the [is_homomorphism_hom] witnesses. *)

Lemma path_homomorphism {σ} {A B : Algebra σ}
  (f g : Homomorphism A B) (p : def_hom f = def_hom g)
  (q : p#(is_homomorphism_hom f) = is_homomorphism_hom g)
  : f = g.
Proof.
  destruct f,g. simpl in *. by path_induction.
Defined.

(** Let [A B : Algebra σ] and suppose [IsHSetAlgebra A] and
    [IsHSetAlgebra B]. To find a path between two homomorphisms
    [f g : Homomorphism A B] it suffices to find a path between the
    defining families of functions. *)

Lemma path_hset_homomorphism `{Funext} {σ} {A B : Algebra σ} `{!IsHSetAlgebra B}
  (f g : Homomorphism A B) (p : def_hom f = def_hom g)
  : f = g.
Proof.
  apply (path_homomorphism _ _ p). apply path_ishprop.
Defined.

(** [f : Homomorphism A B] is an isomorphism if for each [s : Sort σ],
    [f s] is an equivalence. *)

Class IsIsomorphism {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B)
  := isequiv_carriers_isomorphism : ∀ (s : Sort σ), IsEquiv (f s).

Global Existing Instance isequiv_carriers_isomorphism.

Definition equiv_carriers_isomorphism {σ : Signature} {A B : Algebra σ}
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : ∀ (s : Sort σ), A s <~> B s.
Proof.
  intro s. rapply (BuildEquiv _ _ (f s)).
Defined.

Global Instance hprop_is_isomorphism `{Funext} {σ : Signature}
  {A B : Algebra σ} (f : Homomorphism A B)
  : IsHProp (IsIsomorphism f).
Proof.
  apply trunc_forall.
Defined.

(** Let [f : Homomorphism A B] be a homomorphism. The following
    section proves that [f] is "OpPreserving" with respect to
    uncurried algebra operations in the sense that

    <<
      f t (α (x1,x2,...,xn,tt)) = β (f s1 x1,f s2 x1,...,f sn xn,tt)
    >>

    for all [(x1,x2,...,xn,tt) : FamilyProd A [s1;s2;...;sn]], where
    [α] and [β] are uncurried algebra operations in [A] and [B]
    respectively.
*)

Section homomorphism_ap_operation.
  Context {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B).

  Lemma path_homomorphism_ap_operation' {w : SymbolType σ}
    (a : FamilyProd A (dom_symboltype w)) (α : Operation A w)
    (β : Operation B w) (P : OpPreserving f α β)
    : f (cod_symboltype w) (ap_operation α a)
      = ap_operation β (map_family_prod f a).
  Proof.
    induction w.
    - assumption.
    - destruct a as [x a]. apply IHw. apply P.
  Defined.

  Lemma path_homomorphism_ap_operation
    : ∀ (u : Symbol σ) (a : FamilyProd A (dom_symboltype (σ u))),
      f (cod_symboltype (σ u)) (ap_operation (u^^A) a)
      = ap_operation (u^^B) (map_family_prod f a).
  Proof.
    intros u a.
    apply path_homomorphism_ap_operation'.
    apply f.
  Defined.
End homomorphism_ap_operation.

(** The next section shows that the family of identity functions,
    [f s x = x] is an isomorphism. *)

Section hom_id.
  Context {σ} (A : Algebra σ).

  Definition is_homomorphism_id
    : @IsHomomorphism σ A A (λ _, idmap).
  Proof.
   intro u. generalize (u^^A). intro w. induction (σ u).
   - reflexivity.
   - now intro x.
  Defined.

  Definition hom_id : Homomorphism A A
    := BuildHomomorphism (λ _, idmap) is_homomorphism_id.

  Global Instance is_isomorphism_id : IsIsomorphism hom_id.
  Proof.
    intro s. exact _.
  Qed.
End hom_id.

(** Suppose [f : Homomorphism A B] and [IsIsomorphism f]. The next
    section provides an inverse homomorphism [g : Homomorphism B A],
    which is also an isomorphism [IsIsomorphism g]. *)

Section hom_inv.
  Context {σ} {A B : Algebra σ}.

  Definition is_homomorphism_inv (f : Homomorphism A B)
    `{!IsIsomorphism f}
    : IsHomomorphism (λ s, (f s)^-1).
  Proof.
   intro u.
   generalize (u^^A) (u^^B) (is_homomorphism_hom f u).
   intros a b P.
   induction (σ u).
   - destruct P. apply (eissect (f t)).
   - intro. apply IHs.
     exact (transport (λ y, OpPreserving f _ (b y))
              (eisretr (f t) x) (P (_^-1 x))).
  Defined.

  Definition hom_inv (f : Homomorphism A B) `{!IsIsomorphism f}
    : Homomorphism B A
    := BuildHomomorphism (λ s, (f s)^-1) (is_homomorphism_inv f).

  Global Instance is_isomorphism_inv (f : Homomorphism A B)
    `{!IsIsomorphism f}
    : IsIsomorphism (hom_inv f).
  Proof.
    intro s. exact _.
  Qed.
End hom_inv.

(** Let [f : Homomorphism A B] and [g : Homomorphism B C]. The
    following section shows that composition given by [λ (s : Sort σ),
    g s o f s] is again a homomorphism. If both [f] and [g] are
    isomorphisms, then the composition is an isomorphism. *)

Section hom_compose.
  Context {σ} {A B C : Algebra σ}.

  Lemma oppreserving_compose {w : SymbolType σ}
    {α : Operation A w} {β : Operation B w} {γ : Operation C w}
    (g : Homomorphism B C) (f : Homomorphism A B)
    (G : OpPreserving g β γ) (F : OpPreserving f α β)
    : OpPreserving (λ s, g s o f s) α γ.
  Proof.
   induction w; simpl in *.
   - by path_induction.
   - intro x. now apply (IHw _ (β (f _ x))).
  Defined.

  Definition is_homomorphism_compose
    (g : Homomorphism B C) (f : Homomorphism A B)
    : IsHomomorphism (λ s, g s o f s).
  Proof.
   intro u.
   exact (oppreserving_compose g f
            (is_homomorphism_hom g u) (is_homomorphism_hom f u)).
  Defined.

  Definition hom_compose (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
    := BuildHomomorphism (λ s, g s o f s) (is_homomorphism_compose g f).

  Global Instance is_isomorphism_compose
    (g : Homomorphism B C) `{!IsIsomorphism g}
    (f : Homomorphism A B) `{!IsIsomorphism f}
    : IsIsomorphism (hom_compose g f).
  Proof.
   intro s. exact _.
  Qed.
End hom_compose.

(** If [f : ∀ i, F i <~> G i] is a family of equivalences,
    then by function extensionality composed with univalence there is
    a path [F = G]. *)

Definition path_equiv_family `{Univalence} {I : Type}
  {F G : I → Type} (f : ∀ i, F i <~> G i)
  : F = G
  := path_forall F G (λ i, path_universe (f i)).

(** The following section shows that there is a path between
    isomorphic algebras. *)

Section path_isomorphism.
  Context `{Univalence} {σ : Signature} {A B : Algebra σ}.

(** Given a family of equivalences [f : ∀ (s : Sort σ), A s <~> B s]
    which is [OpPreserving f α β] with respect to algebra operations

    <<
      α : A s1 → A s2 → ... → A sn → A t
      β : B s1 → B s2 → ... → B sn → B t
    >>

    By transporting [α] along the path [path_equiv_family f] we
    find a path from the transported operation [α] to [β]. *)

  Lemma path_operations_equiv {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    (f : ∀ (s : Sort σ), A s <~> B s) (P : OpPreserving f α β)
    : transport (λ C : Carriers σ, Operation C w)
        (path_equiv_family f) α
      = β.
  Proof.
    unfold path_equiv_family.
    induction w; simpl in *.
    - transport_path_forall_hammer.
      exact (ap10 (transport_idmap_path_universe (f t)) α @ P).
    - funext y.
      transport_path_forall_hammer.
      rewrite transport_forall_constant.
      rewrite transport_arrow_toconst.
      rewrite (transport_path_universe_V (f t)).
      apply IHw.
      specialize (P ((f t)^-1 y)).
      by rewrite (eisretr (f t) y) in P.
  Qed.

(** Suppose [u : Symbol σ] is a function symbol. Recall that
    [u^^A] is notation for [operations A u : Operation A (σ u)]. This
    is the algebra operation corresponding to function symbol [u]. *)

(** An isomorphism [f : Homomorphism A B] induces a family of
    equivalences [e : ∀ (s : Sort σ), A s <~> B s]. Let [u : Symbol σ]
    be a function symbol. Since [f] is a homomorphism, the induced
    family of equivalences [e] satisfies [OpPreserving e (u^^A) (u^^B)].
    By [path_operations_equiv] above, we can then transport [u^^A] along
    the path [path_equiv_family e] and obtain a path to [u^^B]. *)

  Lemma path_operations_isomorphism (f : Homomorphism A B)
    `{!IsIsomorphism f} (u : Symbol σ)
    : transport (λ C : Carriers σ, Operation C (σ u))
        (path_equiv_family (equiv_carriers_isomorphism f)) (u^^A)
      = u^^B.
  Proof.
    apply path_operations_equiv. apply (is_homomorphism_hom f).
  Defined.

(** If there is an isomorphism [Homomorphism A B] then [A = B]. *)

  Theorem path_isomorphism (f : Homomorphism A B) `{!IsIsomorphism f}
    : A = B.
  Proof.
    apply (path_algebra _ _
            (path_equiv_family (equiv_carriers_isomorphism f))).
    funext u.
    exact (transport_forall_constant _ _ u
           @ path_operations_isomorphism f u).
  Defined.
End path_isomorphism.
