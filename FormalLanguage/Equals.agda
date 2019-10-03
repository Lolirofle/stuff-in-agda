module FormalLanguage.Equals where

import      Lvl
open import FormalLanguage
open import Lang.Size
open import Logic.Propositional
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
import      Structure.Relator.Names as Names
open import Sets.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties

module _ {Σ}{s₁ : Size} where
  record _≅_ (A : Language(Σ){∞}) (B : Language(Σ){∞}) : Set where
    constructor intro
    coinductive
    field
      accepts-ε   : Language.accepts-ε(A) ≡ₑ Language.accepts-ε(B)
      suffix-lang : ∀{c : Σ}{s₂ : Size< s₁} → (Language.suffix-lang A c ≅ Language.suffix-lang B c)

  [≅]-reflexivity-raw : Names.Reflexivity(_≅_)
  _≅_.accepts-ε   ([≅]-reflexivity-raw) = [≡]-intro
  _≅_.suffix-lang ([≅]-reflexivity-raw) = [≅]-reflexivity-raw

  [≅]-symmetry-raw : Names.Symmetry(_≅_)
  _≅_.accepts-ε   ([≅]-symmetry-raw ab) = symmetry(_≡ₑ_) (_≅_.accepts-ε ab)
  _≅_.suffix-lang ([≅]-symmetry-raw ab) = [≅]-symmetry-raw (_≅_.suffix-lang ab)

  [≅]-transitivity-raw : Names.Transitivity(_≅_)
  _≅_.accepts-ε   ([≅]-transitivity-raw ab bc) = transitivity(_≡ₑ_) (_≅_.accepts-ε ab) (_≅_.accepts-ε bc)
  _≅_.suffix-lang ([≅]-transitivity-raw ab bc) = [≅]-transitivity-raw (_≅_.suffix-lang ab) (_≅_.suffix-lang bc)

  instance
    [≅]-reflexivity : Reflexivity(_≅_)
    Reflexivity.proof([≅]-reflexivity) = [≅]-reflexivity-raw

  instance
    [≅]-symmetry : Symmetry(_≅_)
    Symmetry.proof([≅]-symmetry) = [≅]-symmetry-raw

  instance
    [≅]-transitivity : Transitivity(_≅_)
    Transitivity.proof([≅]-transitivity) = [≅]-transitivity-raw

  instance
    [≅]-equivalence : Equivalence(_≅_)
    [≅]-equivalence = record{}

  instance
    [≅]-equiv : Equiv(Language(Σ))
    [≅]-equiv = intro(_≅_) ⦃ [≅]-equivalence ⦄
