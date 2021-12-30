{-# OPTIONS --cubical #-}

module Type.Cubical.HTrunc₁ where

import      Lvl
open import Type
open import Type.Cubical.Path.Equality
open import Type.Properties.Homotopy
open import Type.Properties.MereProposition
open import Structure.Relator
open import Syntax.Function

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}

data HTrunc₁(A : Type{ℓ}) : Type{ℓ} where
  trunc : A → HTrunc₁(A)
  trunc-proof : Names.HomotopyLevel(1) (HTrunc₁(A))

instance
  HTrunc₁-prop : MereProposition(HTrunc₁(A))
  HTrunc₁-prop = intro trunc-proof

module _ ⦃ prop : MereProposition(B) ⦄ where
  HTrunc₁-function : (A → B) → (HTrunc₁(A) → B)
  HTrunc₁-function f (trunc a)              = f(a)
  HTrunc₁-function f (trunc-proof {x}{y} i) = uniqueness(B) {HTrunc₁-function f x} {HTrunc₁-function f y} i

module _ {P : HTrunc₁(A) → Type{ℓ}} ⦃ prop-p : ∀{a} → MereProposition(P(a)) ⦄ where
  HTrunc₁-property : (∀{x} → P(trunc x)) → (∀{a} → P(a))
  HTrunc₁-property axpx {a} = HTrunc₁-function (x ↦ substitute₁ᵣ(P) (uniqueness(HTrunc₁(A)) {trunc x}{a}) axpx) a

data HTrunc₂(A : Type{ℓ}) : Type{ℓ} where
  trunc : A → HTrunc₂(A)
  trunc-proof : Names.HomotopyLevel(2) (HTrunc₂(A))

{- TODO: Does not work because when using a definition like `HomotopyLevel` as a data variant, it must be a Path in normal form
open import Numeral.Natural

data HTrunc (n : ℕ) (A : Type{ℓ}) : Type{ℓ} where
  trunc : A → HTrunc(n)(A)
  trunc-proof : HomotopyLevel(n) (HTrunc(n)(A))
-}
