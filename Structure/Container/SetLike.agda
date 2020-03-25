module Structure.Container.SetLike where

open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Sets.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level

record SetLike (C : Type{ℓ₁}) : Type{ℓ₁ ⊔ Lvl.𝐒(ℓ₂ ⊔ ℓ₃)} where
  field
    Element : Type{ℓ₂}
    ⦃ element-equiv ⦄ : Equiv(Element)
    _∈_ : Element → C → Stmt{ℓ₃}
    _⊆_ : C → C → Stmt{ℓ₃}
    _≡_ : C → C → Stmt{ℓ₃}

  _∋_ : C → Element → Stmt
  _∋_ = swap(_∈_)

  _⊇_ : C → C → Stmt
  _⊇_ = swap(_⊆_)

  _∉_ : Element → C → Stmt
  _∉_ = (¬_) ∘₂ (_∈_)

  _⊈_ : C → C → Stmt
  _⊈_ = (¬_) ∘₂ (_⊆_)

  _⊉_ : C → C → Stmt
  _⊉_ = (¬_) ∘₂ (_⊇_)

  _≢_ : C → C → Stmt
  _≢_ = (¬_) ∘₂ (_≡_)

  field
    ∅ : C
    _∪_ : C → C → C
    _∩_ : C → C → C
    _∖_ : C → C → C
    singleton : Element → C
    add       : Element → C → C
    remove    : Element → C → C

  field
    [⊆]-inclusion : ∀{a b} → (a ⊆ b) ↔ (∀{x} → (x ∈ a) → (x ∈ b))
    [≡]-inclusion : ∀{a b} → (a ≡ b) ↔ (∀{x} → (x ∈ a) ↔ (x ∈ b))
    [∅]-inclusion : ∀{x} → (x ∉ ∅)
    [∪]-inclusion : ∀{x}{a b} → (x ∈ (a ∪ b)) ↔ ((x ∈ a) ∨ (x ∈ b))
    [∩]-inclusion : ∀{x}{a b} → (x ∈ (a ∩ b)) ↔ ((x ∈ a) ∧ (x ∈ b))
    [∖]-inclusion : ∀{x}{a b} → (x ∈ (a ∖ b)) ↔ ((x ∈ a) ∧ (x ∉ b))
    singleton-inclusion : ∀{x y}    → (x ∈ singleton(y)) ↔ (x ≡ₛ y)
    add-inclusion       : ∀{x y}{a} → (x ∈ add y a)      ↔ ((x ∈ a) ∨ (x ≡ₛ y))
    remove-inclusion    : ∀{x y}{a} → (x ∈ remove y a)   ↔ ((x ∈ a) ∧ (x ≢ₛ y))

{-
open SetLike ⦃ … ⦄
  using (
    _∈_ ; _⊆_ ; _≡_ ;
    _∋_ ; _⊇_ ;
    _∉_ ; _⊈_ ; _⊉_ ; _≢_ ;
    ∅ ; _∪_ ; _∩_ ; _∖_ ;
    singleton ; add ; remove
  )
-}

module Proofs {C : Type{ℓ₁}} ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}(C) ⦄ where
  open import Logic.Predicate.Theorems
  open import Logic.Propositional.Theorems
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Ordering
  open import Structure.Relator.Properties

  open SetLike(setLike)

  private variable a b c : C
  private variable x y z : Element

  [⊇]-inclusion : ∀{a b} → (a ⊇ b) ↔ (∀{x} → (x ∈ a) ← (x ∈ b))
  [⊇]-inclusion = [⊆]-inclusion

  instance
    [≡]-to-[⊆] : (_≡_) ⊆₂ (_⊆_)
    _⊆₂_.proof [≡]-to-[⊆] =
      [↔]-to-[←] [⊆]-inclusion
      ∘ [∀][→]-distributivity [↔]-to-[→]
      ∘ [↔]-to-[→] [≡]-inclusion

  instance
    [≡]-to-[⊇] : (_≡_) ⊆₂ (_⊇_)
    _⊆₂_.proof [≡]-to-[⊇] =
      [↔]-to-[←] [⊆]-inclusion
      ∘ [∀][→]-distributivity [↔]-to-[←]
      ∘ [↔]-to-[→] [≡]-inclusion

  instance
    [⊆]-reflexivity : Reflexivity(_⊆_)
    Reflexivity.proof [⊆]-reflexivity = [↔]-to-[←] [⊆]-inclusion [→]-reflexivity

  instance
    [⊆]-antisymmetry : Antisymmetry(_⊆_)(_≡_)
    Antisymmetry.proof [⊆]-antisymmetry ab ba =
      [↔]-to-[←] [≡]-inclusion ([↔]-intro ([↔]-to-[→] [⊇]-inclusion ba) ([↔]-to-[→] [⊆]-inclusion ab))

  instance
    [⊆]-transitivity : Transitivity(_⊆_)
    Transitivity.proof [⊆]-transitivity xy yz =
      [↔]-to-[←] [⊆]-inclusion ([→]-transitivity ([↔]-to-[→] [⊆]-inclusion xy) ([↔]-to-[→] [⊆]-inclusion yz))

  instance
    [⊆]-partialOrder : Weak.PartialOrder(_⊆_)(_≡_)
    [⊆]-partialOrder = Weak.intro

  instance
    [≡]-reflexivity : Reflexivity(_≡_)
    Reflexivity.proof [≡]-reflexivity = [↔]-to-[←] [≡]-inclusion [↔]-reflexivity

  instance
    [≡]-symmetry : Symmetry(_≡_)
    Symmetry.proof [≡]-symmetry =
      [↔]-to-[←] [≡]-inclusion
      ∘ [∀][→]-distributivity [↔]-symmetry
      ∘ [↔]-to-[→] [≡]-inclusion

  instance
    [≡]-transitivity : Transitivity(_≡_)
    Transitivity.proof [≡]-transitivity xy yz = [↔]-to-[←] [≡]-inclusion ([↔]-transitivity ([↔]-to-[→] [≡]-inclusion xy) ([↔]-to-[→] [≡]-inclusion yz))

  instance
    [≡]-equivalence : Equivalence(_≡_)
    [≡]-equivalence = intro
