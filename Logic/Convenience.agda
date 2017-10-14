module Logic.Convenience {ℓ} where

import      Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ}
open import Type

record [⇒]-proof (Proof : Stmt → Stmt → Type{ℓ}) : Type{Lvl.𝐒(ℓ)} where
  infixl 10 _⇒_
  infixr 10 _⇐_

  field
    _⇒_ : ∀{X Y : Stmt} → X → Proof(X)(Y) → Y

  _⇐_ : ∀{X Y : Stmt} → Proof(X)(Y) → X → Y
  _⇐_ = swap(_⇒_)
open [⇒]-proof ⦃...⦄ public

instance
  [⇒]-proof-[→] : [⇒]-proof (X ↦ Y ↦ (X → Y))
  _⇒_ ⦃ [⇒]-proof-[→] ⦄ = apply

instance
  [⇒]-proof-[↔] : [⇒]-proof (X ↦ Y ↦ (X ↔ Y))
  _⇒_ ⦃ [⇒]-proof-[↔] ⦄ = swap(Tuple.right)

instance
  [⇒]-proof-unrelated : [⇒]-proof (X ↦ Y ↦ Y)
  _⇒_ ⦃ [⇒]-proof-unrelated ⦄ = swap(const)
