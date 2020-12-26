{-# OPTIONS --sized-types #-}

module FormalLanguage.Equals{ℓ} where

import      Lvl
open import FormalLanguage
open import Lang.Size
open import Logic.Propositional
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
import      Structure.Relator.Names as Names
open import Structure.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable s : Size

module _ {Σ : Alphabet{ℓ}} where
  record _≅[_]≅_ (A : Language(Σ){∞ˢⁱᶻᵉ}) (s : Size) (B : Language(Σ){∞ˢⁱᶻᵉ}) : Type{ℓ} where
    constructor intro
    coinductive
    field
      accepts-ε   : Language.accepts-ε(A) ≡ₑ Language.accepts-ε(B)
      suffix-lang : ∀{c : Σ}{sₛ : <ˢⁱᶻᵉ s} → (Language.suffix-lang A c ≅[ sₛ ]≅ Language.suffix-lang B c)

  _≅_ : ∀{s : Size} → Language(Σ){∞ˢⁱᶻᵉ} → Language(Σ){∞ˢⁱᶻᵉ} → Type
  _≅_ {s} = _≅[ s ]≅_

  [≅]-reflexivity-raw : Names.Reflexivity(_≅[ s ]≅_)
  _≅[_]≅_.accepts-ε   ([≅]-reflexivity-raw) = [≡]-intro
  _≅[_]≅_.suffix-lang ([≅]-reflexivity-raw) = [≅]-reflexivity-raw

  [≅]-symmetry-raw : Names.Symmetry(_≅[ s ]≅_)
  _≅[_]≅_.accepts-ε   ([≅]-symmetry-raw ab) = symmetry(_≡ₑ_) (_≅[_]≅_.accepts-ε ab)
  _≅[_]≅_.suffix-lang ([≅]-symmetry-raw ab) = [≅]-symmetry-raw (_≅[_]≅_.suffix-lang ab)

  [≅]-transitivity-raw : Names.Transitivity(_≅[ s ]≅_)
  _≅[_]≅_.accepts-ε   ([≅]-transitivity-raw ab bc) = transitivity(_≡ₑ_) (_≅[_]≅_.accepts-ε ab) (_≅[_]≅_.accepts-ε bc)
  _≅[_]≅_.suffix-lang ([≅]-transitivity-raw ab bc) = [≅]-transitivity-raw (_≅[_]≅_.suffix-lang ab) (_≅[_]≅_.suffix-lang bc)

  instance
    [≅]-reflexivity : Reflexivity(_≅[ s ]≅_)
    Reflexivity.proof([≅]-reflexivity) = [≅]-reflexivity-raw

  instance
    [≅]-symmetry : Symmetry(_≅[ s ]≅_)
    Symmetry.proof([≅]-symmetry) = [≅]-symmetry-raw

  instance
    [≅]-transitivity : Transitivity(_≅[ s ]≅_)
    Transitivity.proof([≅]-transitivity) = [≅]-transitivity-raw

  instance
    [≅]-equivalence : Equivalence(_≅[ s ]≅_)
    [≅]-equivalence = record{}

  instance
    [≅]-equiv : let _ = s in Equiv(Language(Σ))
    [≅]-equiv {s = s} = intro(_≅[ s ]≅_) ⦃ [≅]-equivalence ⦄
