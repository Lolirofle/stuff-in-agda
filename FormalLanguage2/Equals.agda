{-# OPTIONS --guardedness #-}

module FormalLanguage2.Equals where

import      Lvl
open import FormalLanguage2 using (Alphabet ; Language)
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs.Equiv
import      Structure.Relator.Names as Names
open import Structure.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ : Lvl.Level
private variable Σ : Alphabet{ℓ}

record _≅_ (A : Language(Σ)) (B : Language(Σ)) : Type{Lvl.of(Σ)} where
  constructor intro
  coinductive
  field
    accepts-ε : Language.accepts-ε(A) ≡ₑ Language.accepts-ε(B)
    suffix    : ∀{c : Σ} → (Language.suffix A c ≅ Language.suffix B c)

instance
  [≅]-reflexivity : Reflexivity(_≅_ {Σ = Σ})
  [≅]-reflexivity = intro p where
    p : Names.Reflexivity(_≅_ {Σ = Σ})
    _≅_.accepts-ε p = [≡]-intro
    _≅_.suffix    p = p

instance
  [≅]-symmetry : Symmetry(_≅_ {Σ = Σ})
  [≅]-symmetry = intro p where
    p : Names.Symmetry(_≅_ {Σ = Σ})
    _≅_.accepts-ε (p ab) = symmetry(_≡ₑ_) (_≅_.accepts-ε ab)
    _≅_.suffix    (p ab) = p (_≅_.suffix ab)

instance
  [≅]-transitivity : Transitivity(_≅_ {Σ = Σ})
  [≅]-transitivity = intro p where
    p : Names.Transitivity(_≅_ {Σ = Σ})
    _≅_.accepts-ε (p ab bc) = transitivity(_≡ₑ_) (_≅_.accepts-ε ab) (_≅_.accepts-ε bc)
    _≅_.suffix    (p ab bc) = p (_≅_.suffix ab) (_≅_.suffix bc)

instance
  [≅]-equivalence : Equivalence(_≅_ {Σ = Σ})
  [≅]-equivalence = record{}

instance
  [≅]-equiv : Equiv(Language(Σ))
  [≅]-equiv = intro(_≅_) ⦃ [≅]-equivalence ⦄
