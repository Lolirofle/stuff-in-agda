module Data.List.Computability where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Proofs
open import Data.List
open import Logic.Computability.Binary
open import Functional
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type

instance
  [≡]-computable : ∀{ℓ}{T : Type{ℓ}} → ⦃ _ : ComputablyDecidable{X = T}(_≡_) ⦄ → ComputablyDecidable{X = List(T)}(_≡_)
  [≡]-computable {T = T} ⦃ decidableT ⦄ = ComputablyDecidable-intro decide ⦃ proof ⦄ where
    decideT : T → T → Bool
    decideT = ComputablyDecidable.decide (_) ⦃ decidableT ⦄

    proofT : ∀{x y} → (x ≡ y) ↔ (decideT(x)(y) ≡ 𝑇)
    proofT = ComputablyDecidable.proof  (_) ⦃ decidableT ⦄

    decide : List(T) → List(T) → Bool
    decide ∅         ∅         = 𝑇
    decide (_ ⊰ _)   ∅         = 𝐹
    decide ∅         (_ ⊰ _)   = 𝐹
    decide (x₁ ⊰ l₁) (x₂ ⊰ l₂) = decideT(x₁)(x₂) && decide(l₁)(l₂)

    decideT-reflexivity : ∀{x} → (decideT(x)(x) ≡ 𝑇)
    decideT-reflexivity = [↔]-elimᵣ([≡]-intro) (proofT)

    decide-reflexivity : ∀{l} → (_≡_ (decide(l)(l)) 𝑇)
    decide-reflexivity {∅}     = [≡]-intro
    decide-reflexivity {x ⊰ l} = 𝑇.[∧]-intro (decideT-reflexivity) (decide-reflexivity {l})

    proof : ∀{x}{y} → (x ≡ y) ↔ (decide x y ≡ 𝑇)
    proof{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
      l : ∀{x}{y} → (x ≡ y) ← (decide x y ≡ 𝑇)
      l {∅}       {∅}       ([≡]-intro) = [≡]-intro
      l {_ ⊰ _}   {∅}       ()
      l {∅}       {_ ⊰ _}   ()
      l {x₁ ⊰ l₁} {x₂ ⊰ l₂} (proof) with [↔]-elimₗ (𝑇.[∧]-elimₗ {decideT(x₁)(x₂)} {decide(l₁)(l₂)} proof) (proofT{_}{_})
      ... | [≡]-intro = [≡]-with (x₁ ⊰_) (l (𝑇.[∧]-elimᵣ {decideT(x₁)(x₂)} {decide(l₁)(l₂)} proof))

      r : ∀{x}{y} → (x ≡ y) → (decide x y ≡ 𝑇)
      r {∅}       {∅}       ([≡]-intro) = [≡]-intro
      r {_ ⊰ _}   {∅}       ()
      r {∅}       {_ ⊰ _}   ()
      r {x ⊰ l₁} {.x ⊰ l₂} ([≡]-intro) = 𝑇.[∧]-intro (decideT-reflexivity{x}) (r{l₁}{l₂}([≡]-intro))
