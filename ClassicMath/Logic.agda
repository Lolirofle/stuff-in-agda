{-# OPTIONS --without-K --no-universe-polymorphism #-} -- --cubical

module ClassicMath.Logic where

import      Lvl
open import Logic.Classical{Lvl.𝟎}
open import Logic.Propositional{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎} -- TODO: Is incompatible with without-K?
open import Type{Lvl.𝟎}

instance postulate classical : ∀{P} → Classical(P) -- TODO: There may be a problem assuming this? It could probably be interpreted as: everything is computable

-- postulate [≡]-stmt : ∀{Proof : Stmt}{x y : Proof} → (x ≡ y)
postulate [≡]-function : ∀{X : Type}{Y : Type}{f g : X → Y} → (∀{x} → (f(x) ≡ g(x))) → (f ≡ g)

-- Filtered "subset" type
record Filter (T : Type) (P : T → Stmt) : Type where
  constructor intro
  field
    element   : T
    ⦃ .proof ⦄ : P(element)

module _ where
  open import Structure.Relator.Equivalence{Lvl.𝟎}
  open import Structure.Relator.Properties{Lvl.𝟎}

  -- Quotient type
  -- data _/_ (T : Type) (_≅_ : T → T → Stmt) ⦃ _ : Equivalence(_≅_) ⦄ : Type where
  --   [_] : (a : T) → (b : T) → ⦃ _ : a ≅ b ⦄ → Quotient(_≅_)

  -- data [_of_] {T : Type} (a : T) (_≅_ : T → T → Stmt) ⦃ _ : Equivalence(_≅_) ⦄ : Type where
  --   intro : (b : T) → ⦃ _ : (a ≅ b) ⦄ → [ a of (_≅_) ]

  -- [_of_] : ∀{T : Type} → T → (_≅_ : T → T → Stmt) → ⦃ _ : Equivalence(_≅_) ⦄ → T → Type
  -- [ x of _≅_ ] y = (x ≅ y)

  -- [≡]-quotient : ∀{T : Type}{_≅_} → ⦃ _ : Equivalence(_≅_) ⦄ → ∀{x y : T} → (x ≅ y) → ([ x of (_≅_) ] ≡ [ y of (_≅_) ])
  -- [≡]-quotient proof = [≡]-function proof
