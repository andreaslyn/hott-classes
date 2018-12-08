Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTTClasses.implementations.list
  HoTTClasses.interfaces.ua_algebra.

Import algebra_notations.

(* TODO Fix documentation. *)

(** The following section implements a datatype [CProd] intended to represent
    a product/tuple of algebra operation arguments. Suppose [σ : Signature] is
    a signature and [A : Algebra σ] an algebra. An algebra operation
    [u^^A] has type [u^^U : Operation A (σ u)], for [u : symbol σ] a function
    symbol. The type [Operation A (σ u)] is a curried function type
    [A s1 -> A s2 -> ... -> A sn], where [[:s1,s2,...,sn] = σ u]. The
    [apply_cprod] function below can be used to uncurry [f], so that

      [apply_cprod f (x1,x2,...,xn) = f x1 x2 ... xn]. *)

Section cprod.
  Context {σ : Signature}.

  (** TODO A product type [CProd A [s1,s2,...,sn] = A s1 * A s2 * ... * A sn]. *)

  Fixpoint CProd (A : Carriers σ) (w : list (Sort σ)) : Type :=
    match w with
    | nil => Unit
    | s :: w' => A s * CProd A w'
    end.

  (** Map function for [CProd]

        [map_cprod f (x1,x2,...,xn) = (f x1, f x2, ..., f xn)]. *)

  Fixpoint map_cprod {A : Carriers σ} {B : Carriers σ}
      {w : list (Sort σ)} (f : ∀ s, A s → B s)
      : CProd A w → CProd B w :=
    match w with
    | nil => const tt
    | s :: w' => λ '(x,l), (f s x, map_cprod f l)
    end.

  (** Test whether [P s1 x1 ∧ P s2 x2 ∧ ... ∧ P sn xn] holds, where
      [(x1,...,xn) : A s1 * A s2 * ... * S xn]. *)

  Fixpoint for_all_cprod {A : Carriers σ} {w : list (Sort σ)}
      (P : ∀ s, A s -> Type) : CProd A w → Type :=
    match w with
    | nil => λ _, True
    | s :: w' => λ '(x,l), P s x * for_all_cprod P l
    end.

  (** Test whether [R s1 x1 y1 ∧ R s2 x2 y2 ∧ ... ∧ P sn xn yn] holds, where
      [(x1,...,xn) : A s1 * A s2 * ... * S xn] and
      [(y1,...,yn) : B s1 * B s2 * ... * B xn] *)

  Fixpoint for_all_2_cprod {A B : Carriers σ} {w : list (Sort σ)}
      (R : ∀ s, A s -> B s -> Type) : CProd A w → CProd B w → Type :=
    match w with
    | nil => λ _ _, True
    | s :: w' => λ '(x1,l1) '(x2,l2), R s x1 x2 * for_all_2_cprod R l1 l2
    end.

  Lemma reflexive_for_all_2_cprod (A : Carriers σ) (R : ∀ s, relation (A s))
    `{!∀ s, Reflexive (R s)} (w : list (Sort σ)) (a : CProd A w)
    : for_all_2_cprod R a a.
  Proof.
    induction w.
    - reflexivity.
    - by split.
  Defined.

  (** Uncurry of [Operation], such that

        [apply_cprod f (x1,x2,...,xn) = f x1 x2 ... xn]. *)

  Fixpoint apply_cprod {A : Carriers σ} {w : SymbolType σ}
      : Operation A w → CProd A (dom_symboltype w) → A (cod_symboltype w) :=
    match w with
    | [:s] => λ a _, a
    | s ::: w' => λ f '(x, l), apply_cprod (f x) l
    end.

  (** Funext for uncurried [Operation]s. If

        [apply_cprod f (x1,x2,...,xn) = apply_cprod g (x1,x2,...,xn)],

      for all [(x1,x2,...,xn) : A s1 * A s2 * ... A sn], then [f = g].
  *)

  Fixpoint path_forall_apply_cprod `{Funext} {A : Carriers σ} {w : SymbolType σ}
      : ∀ (f g : Operation A w),
        (∀ a : CProd A (dom_symboltype w),
         apply_cprod f a = apply_cprod g a) -> f = g
  := match w with
     | [:s] => λ f g h, h tt
     | s ::: w' =>
         λ f g h, path_forall f g
                    (λ x, path_forall_apply_cprod (f x) (g x) (λ a, h (x,a)))
     end.
End cprod.
