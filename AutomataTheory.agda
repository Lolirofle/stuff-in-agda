module AutomataTheory where

-- ∑ denotes an alphabet
-- String|Word is a list of symbols in an alphabet
-- ∑* denotes the set of all words for a given alphabet

Alphabet = Set

data ∑* (∑ : Alphabet) : Set where
  ε : (∑* ∑)
  _-_ : ∑ → (∑* ∑) → (∑* ∑)

_⧺_ : ∀{∑} → (∑* ∑) → (∑* ∑) → (∑* ∑)
_⧺_ ε       y = y
_⧺_ (a - x) y = a - (x ⧺ y)

module TestOnOffSwitch where
  data ∑ : Alphabet where
    Push : ∑

module TestVendingMachine where
  data ∑ : Alphabet where
    OutputTea    : ∑
    OutputCoffee : ∑
    Input5kr     : ∑
    Input10kr    : ∑
