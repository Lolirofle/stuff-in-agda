module Data.List.Computability{ℓ₁}{ℓ₂} where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Proofs
open import Data.List
open import Logic.Computability.Binary{ℓ₁}{ℓ₂}
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals
open import Relator.Equals.Proofs

instance
  [≡]-computable : ∀{T} → ⦃ _ : ComputablyDecidable{T}(_≡_) ⦄ → ComputablyDecidable{List(T)}(_≡_)
  [≡]-computable {T} ⦃ decidableT ⦄ = ComputablyDecidable-intro decide ⦃ proof ⦄ where
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
    decideT-reflexivity = [↔]-elimᵣ(proofT) ([≡]-intro)

    decide-reflexivity : ∀{l} → (_≡_ {ℓ₁ Lvl.⊔ ℓ₂} (decide(l)(l)) 𝑇)
    decide-reflexivity {∅}     = [≡]-intro
    decide-reflexivity {x ⊰ l} = [∧]-intro-[𝑇] (decideT-reflexivity) (decide-reflexivity {l})

    proof : ∀{x}{y} → (x ≡ y) ↔ (decide x y ≡ 𝑇)
    proof{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
      l : ∀{x}{y} → (x ≡ y) ← (decide x y ≡ 𝑇)
      l {∅}       {∅}       ([≡]-intro) = [≡]-intro
      l {_ ⊰ _}   {∅}       ()
      l {∅}       {_ ⊰ _}   ()
      l {x₁ ⊰ l₁} {x₂ ⊰ l₂} (proof) with [↔]-elimₗ(proofT{_}{_}) ([∧]-elimₗ-[𝑇] {_} {decideT(x₁)(x₂)} {decide(l₁)(l₂)} proof)
      ... | [≡]-intro = [≡]-with {ℓ₁} (x₁ ⊰_) (l{l₁}{l₂} ([∧]-elimᵣ-[𝑇] {_} {decideT(x₁)(x₂)} {decide(l₁)(l₂)} proof))

      r : ∀{x}{y} → (x ≡ y) → (decide x y ≡ 𝑇)
      r {∅}       {∅}       ([≡]-intro) = [≡]-intro
      r {_ ⊰ _}   {∅}       ()
      r {∅}       {_ ⊰ _}   ()
      r {x ⊰ l₁} {.x ⊰ l₂} ([≡]-intro) = [∧]-intro-[𝑇] (decideT-reflexivity{x}) (r{l₁}{l₂}([≡]-intro))
