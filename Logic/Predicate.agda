module Logic.Predicate where

open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Type
open import Type.Empty

------------------------------------------
-- Existential quantification (Existance, Exists)

module _ {ℓ₁}{ℓ₂} where
  record ∃ {Obj : Type{ℓ₁}} (Pred : Obj → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    instance constructor [∃]-intro
    field
      witness   : Obj
      ⦃ proof ⦄ : Pred(witness)

  [∃]-witness : ∀{Obj}{Pred} → ∃{Obj}(Pred) → Obj
  [∃]-witness([∃]-intro(x) ⦃ _ ⦄ ) = x

  [∃]-proof : ∀{Obj}{Pred} → (e : ∃{Obj}(Pred)) → Pred([∃]-witness(e))
  [∃]-proof([∃]-intro(_) ⦃ proof ⦄ ) = proof

  [∃]-elim : ∀{ℓ₃}{Obj}{Pred}{Z : Stmt{ℓ₃}} → (∀{x : Obj} → Pred(x) → Z) → (∃{Obj} Pred) → Z
  [∃]-elim (f) ([∃]-intro(_) ⦃ proof ⦄) = f(proof)

  syntax ∃{T}(λ x → y) = ∃❪ x ꞉ T ❫․ y

  {- TODO: This would allow the syntax: ∃ₗ x ↦ P(x)
    ∃ₗ_ = ∃
    infixl 1 ∃ₗ_
  -}

------------------------------------------
-- Universal quantification (Forall, All)

module _ {ℓ₁}{ℓ₂} where
  ∀ₗ : ∀{Obj : Type{ℓ₁}} → (Pred : Obj → Stmt{ℓ₂}) → Stmt
  ∀ₗ (Pred) = (∀{x} → Pred(x))

  [∀]-intro : ∀{Obj : Type}{Pred : Obj → Stmt} → ((a : Obj) → Pred(a)) → ∀ₗ(x ↦ Pred(x))
  [∀]-intro p{a} = p(a)

  [∀]-elim : ∀{Obj : Type}{Pred : Obj → Stmt} → ∀ₗ(x ↦ Pred(x)) → (a : Obj) → Pred(a)
  [∀]-elim p(a) = p{a}

  -- Eliminates universal quantification for a non-empty domain using a witnessed existence which proves that the domain is non-empty.
  [∀ₑ]-elim : ∀{Obj : Type} → ⦃ _ : ◊ Obj ⦄ → ∀{P : Obj → Stmt} → ∀ₗ(x ↦ P(x)) → P([◊]-existence)
  [∀ₑ]-elim {Obj} ⦃ proof ⦄ {P} apx = [∀]-elim {Obj}{P} apx(◊.existence(proof))

  syntax ∀ₗ{T}(λ x → y) = ∀❪ x ꞉ T ❫․ y

module _ {ℓ₁}{ℓ} where
  ∀ᶠ : ∀{X : Type{ℓ₁}} → (Pred : X → Stmt{ℓ}) → Stmt
  ∀ᶠ (Pred) = (∀{x} → Pred(x))

module _ {ℓ₁}{ℓ₂}{ℓ} where
  ∀²ᶠ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}} → (Pred : X → Y → Stmt{ℓ}) → Stmt
  ∀²ᶠ (Pred) = (∀{x}{y} → Pred(x)(y))

module _ {ℓ₁}{ℓ₂}{ℓ₃}{ℓ} where
  ∀³ᶠ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (Pred : X → Y → Z → Stmt{ℓ}) → Stmt
  ∀³ᶠ (Pred) = (∀{x}{y}{z} → Pred(x)(y)(z))

module _ {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄}{ℓ} where
  ∀⁴ᶠ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}}{W : Type{ℓ₄}} → (Pred : X → Y → Z → W → Stmt{ℓ}) → Stmt
  ∀⁴ᶠ (Pred) = (∀{x}{y}{z}{w} → Pred(x)(y)(z)(w))
