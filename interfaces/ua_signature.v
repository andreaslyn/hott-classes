Require Export HoTTClasses.implementations.ne_list.

Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTT.Classes.implementations.list.

Import ne_list.notations.

Local Notation SymbolType_internal := @ne_list.

Record Signature : Type := Build
  { Sort : Type
  ; Symbol : Type
  ; symbol_types : Symbol → SymbolType_internal Sort }.

Global Coercion symbol_types : Signature >-> Funclass.

Definition BuildSingleSorted {Op : Type} (arities : Op → nat)
  : Signature
  := Build Unit Op (ne_list.replicate_Sn tt o arities).

Definition SymbolType (σ : Signature) : Type := SymbolType_internal (Sort σ).

Definition cod_symboltype {σ} : SymbolType σ → Sort σ := ne_list.last.

Definition dom_symboltype {σ} : SymbolType σ → list (Sort σ) := ne_list.front.

Definition arity_symboltype {σ} : SymbolType σ → nat := length o dom_symboltype.

Module signature_notations.
  Export ne_list.notations.
End signature_notations.
