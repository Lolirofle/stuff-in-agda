import      Lvl
open import Type

module Data.IndexedList {ℓ ℓᵢ} (T : Type{ℓ}) {I : Type{ℓᵢ}} where

private variable i : I

record Index : Type{ℓᵢ Lvl.⊔ ℓ} where
  constructor intro
  field
    ∅   : I
    _⊰_ : T → I → I

module _ ((intro ∅ᵢ _⊰ᵢ_) : Index) where
  data IndexedList : I → Type{ℓᵢ Lvl.⊔ ℓ} where
    ∅   : IndexedList(∅ᵢ)
    _⊰_ : (x : T) → IndexedList(i) → IndexedList(x ⊰ᵢ i)

  infixr 1000 _⊰_

module LongOper where
  pattern empty = ∅
  pattern prepend elem list = elem ⊰ list
pattern singleton x = x ⊰ ∅
