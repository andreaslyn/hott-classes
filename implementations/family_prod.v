Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTTClasses.implementations.list.

(* TODO Fix documentation. *)

(** The following section implements a datatype [FamilyProd] intended to represent
    a product/tuple of algebra operation arguments. Suppose [σ : Signature] is
    a signature and [A : Algebra σ] an algebra. An algebra operation
    [u^^A] has type [u^^U : Operation A (σ u)], for [u : symbol σ] a function
    symbol. The type [Operation A (σ u)] is a curried function type
    [A s1 -> A s2 -> ... -> A sn], where [[:s1,s2,...,sn] = σ u]. The
    [ap_operation] function below can be used to uncurry [f], so that

      [ap_operation f (x1,x2,...,xn) = f x1 x2 ... xn]. *)

Section family_prod.
  Context {I : Type}.

  (** TODO A product type [FamilyProd A [s1,s2,...,sn] = A s1 * A s2 * ... * A sn * Unit]. *)

  Definition FamilyProd (F : I → Type) : list I → Type
    := fold_right (λ (i:I) (A:Type), F i * A) Unit.

  (** Map function for [FamilyProd]

        [map_family_prod f (x1,x2,...,xn) = (f x1, f x2, ..., f xn)]. *)

  Fixpoint map_family_prod {F G : I → Type} {ℓ : list I}
      (f : ∀ i, F i → G i)
      : FamilyProd F ℓ → FamilyProd G ℓ :=
    match ℓ with
    | nil => const tt
    | i :: ℓ' => λ '(x,s), (f i x, map_family_prod f s)
    end.

  (** Test whether [P s1 x1 ∧ P s2 x2 ∧ ... ∧ P sn xn] holds, where
      [(x1,...,xn) : A s1 * A s2 * ... * A sn]. *)

  Fixpoint for_all_family_prod (F : I → Type) {ℓ : list I}
      (P : ∀ i, F i -> Type) : FamilyProd F ℓ → Type :=
    match ℓ with
    | nil => λ _, True
    | i :: ℓ' => λ '(x,s), P i x ∧ for_all_family_prod F P s
    end.

  (** Test whether [R s1 x1 y1 ∧ R s2 x2 y2 ∧ ... ∧ P sn xn yn] holds, where
      [(x1,...,xn) : A s1 * A s2 * ... * S xn] and
      [(y1,...,yn) : B s1 * B s2 * ... * B xn] *)

  Fixpoint for_all_2_family_prod (F G : I → Type) {ℓ : list I}
      (R : ∀ i, F i -> G i -> Type)
      : FamilyProd F ℓ → FamilyProd G ℓ → Type :=
    match ℓ with
    | nil => λ _ _, True
    | i :: ℓ' => λ '(x,s) '(y,t), R i x y ∧ for_all_2_family_prod F G R s t
    end.

  Lemma reflexive_for_all_2_family_prod (F : I → Type)
    (R : ∀ i, relation (F i)) `{!∀ i, Reflexive (R i)}
    {ℓ : list I} (s : FamilyProd F ℓ)
    : for_all_2_family_prod F F R s s.
  Proof with try reflexivity.
    induction ℓ...
    split...
    apply IHℓ.
  Defined.
End family_prod.
