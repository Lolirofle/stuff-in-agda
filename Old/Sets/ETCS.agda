import      Lvl

-- TODO: Is it possible formalize this like this? Is it even correct?

-- Based on http://www.maths.ed.ac.uk/~tl/edinburgh_yrm/ (2017-11-22)
module Sets.ETCS where

  open import Logic.Propositional

  module Theory (S : Set(Lvl.𝟎)) (F : S → S → Set(Lvl.𝟎)) (_∘_ : ∀{a b c} → F(b)(c) → F(a)(b) → F(a)(c)) (_≡_ : ∀{a b} → F(a)(b) → F(a)(b) → Stmt{Lvl.𝟎}) where
    open import Functional hiding (_∘_)
    open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
    open import Logic.Propositional.Theorems{Lvl.𝟎}
    open import Relator.Equals{Lvl.𝟎} using () renaming (_≡_ to _≡ᵣ_)
    open import Type{Lvl.𝟎}

    Terminal : S → Stmt
    Terminal(x) = (∀{a : S} → (f g : F(a)(x)) → (f ≡ g))

    record Axioms : Set(Lvl.𝐒(Lvl.𝟎)) where
      field
        associativity : ∀{a b c d : S}{f : F(a)(b)}{g : F(b)(c)}{h : F(c)(d)} → ((h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f))
        identity : ∀{a : S} → ∃{F(a)(a)}(id ↦ (∀{b : S}{f : F(a)(b)} → ((f ∘ id) ≡ f)) ∧ (∀{b : S}{f : F(b)(a)} → ((id ∘ f) ≡ f)))
        terminal : ∃(term ↦ Terminal(term))

      𝟏 : S
      𝟏 = [∃]-witness(terminal)

      _∈_ : ∀{a b : S} → F(a)(b) → S → Stmt
      _∈_ {a}{b} x X = (a ≡ᵣ 𝟏)∧(b ≡ᵣ X)

      _∉_ : ∀{a b : S} → F(a)(b) → S → Stmt
      _∉_ x X = ¬(x ∈ X)

      field
        empty : ∃{S}(∅ ↦ ∀{a b : S}{f : F(a)(b)} → (f ∉ ∅))

      -- TODO

  module Construction where
    open import Data
    open import Functional using (_∘_ ; id)
    open import Logic.Predicate{Lvl.𝐒(Lvl.𝟎)}{Lvl.𝟎}
    open import Logic.Propositional.Theorems{Lvl.𝐒(Lvl.𝟎)}
    open import Relator.Equals{Lvl.𝟎}

    Terminal : Set → Stmt
    Terminal(x) = (∀{a : Set}{f g : a → x} → (f ≡ g))

    _∈_ : ∀{a b : Set} → (a → b) → Set → Stmt
    _∈_ {a}{b} _ X = (a ≡ Unit)∧(b ≡ X)

    ∅ : Set
    ∅ = Empty

    -- TODO: Maybe use FunctionEquals instead?
    -- TODO: Is this construction working? Try to prove some of the theorems of standard set theory
