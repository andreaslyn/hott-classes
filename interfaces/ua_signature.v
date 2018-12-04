Require Export HoTTClasses.implementations.ne_list.

Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTT.Classes.implementations.list.

Import ne_list.notations.

Local Notation symboltype_internal := @ne_list.

Record Signature : Type := Build
  { sort : Type
  ; symbol : Type
  ; symboltype_symbol : symbol → symboltype_internal sort }.

Global Coercion symboltype_symbol : Signature >-> Funclass.

Definition BuildSingleSorted {Op : Type} (arities : Op → nat)
  : Signature
  := Build Unit Op (ne_list.replicate_Sn tt o arities).

Definition symboltype (σ : Signature) : Type := symboltype_internal (sort σ).

Definition cod_symboltype {σ} : symboltype σ → sort σ := ne_list.last.

Definition dom_symboltype {σ} : symboltype σ → list (sort σ) := ne_list.front.

Definition arity_symboltype {σ} : symboltype σ → nat := length o dom_symboltype.

Module signature_notations.
  Export ne_list.notations.
End signature_notations.
