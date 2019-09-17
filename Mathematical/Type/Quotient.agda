module Type.Quotient where

open import Logic
open import Relator.Equals
open import Type
open import Lvl

private variable ℓ₁ : Lvl.Level
private variable ℓ₂ : Lvl.Level

data _/_  (T : Type{ℓ₁}) (_≅_ : T → T → Stmt{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  [_] : T → (T / (_≅_))
  [/]-equiv-to-eq : ∀{x y : T} → (x ≅ y) → ([ x ] ≡ [ y ])
  [/]-uip : ∀{X Y : (T / (_≅_))} → (proof₁ proof₂ : (X ≡ Y)) → (proof₁ ≡ proof₂)

  -- TODO: [/]-eq-to-equiv : (x y : A) → (x ≅ y) ← ([ x ] ≡ [ y ])
