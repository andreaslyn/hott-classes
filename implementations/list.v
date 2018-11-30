Require Import HoTT.Basics.Overture.
Require Export HoTT.Classes.implementations.list.

Import ListNotations.

(** Extension of [list] *)
Section operations.
  Context {A: Type}.

  (* Copy pasted from the Coq library. *)
  Definition tl (l:list A) :=
    match l with
      | [] => nil
      | a :: m => m
    end.

  (* Modified copy from the Coq library. *)
  (** The [In] predicate *)
  Fixpoint InList (a:A) (l:list A) : Type0 :=
    match l with
      | [] => False
      | b :: m => b = a |_| InList a m
    end.

  Fixpoint fold_right {B: Type} (f: B -> A -> A) (a0: A) (l: list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right f a0 t)
    end.
End operations.
