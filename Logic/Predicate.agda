module Logic.Predicate where

open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Type
open import Type.Properties.Inhabited

------------------------------------------
-- Existential quantification (Existance, Exists)

module _ {ℓ₁}{ℓ₂} where
  record ∃ {Obj : Type{ℓ₁}} (Pred : Obj → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    eta-equality
    constructor [∃]-intro
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

private variable ℓ : Lvl.Level
private variable Obj X Y Z W : Type{ℓ}
private variable Pred P Q R : X → Type{ℓ}

[∃]-map-proof : (∀{x} → P(x) → Q(x)) → ((∃ P) → (∃ Q))
[∃]-map-proof (f) ([∃]-intro(x) ⦃ proof ⦄) = [∃]-intro(x) ⦃ f(proof) ⦄

[∃]-map : (f : X → Y) → (∀{x} → P(x) → Q(f(x))) → ((∃ P) → (∃ Q))
[∃]-map f p ([∃]-intro(x) ⦃ proof ⦄) = [∃]-intro(f(x)) ⦃ p(proof) ⦄

[∃]-map₂ : (f : X → Y → Z) → (∀{x y} → P(x) → Q(y) → R(f x y)) → ((∃ P) → (∃ Q) → (∃ R))
[∃]-map₂ f p ([∃]-intro(x) ⦃ proof₁ ⦄) ([∃]-intro(y) ⦃ proof₂ ⦄) = [∃]-intro(f x y) ⦃ p proof₁ proof₂ ⦄

[∃]-map-proof-dependent : (ep : ∃ P) → (P(∃.witness ep) → Q(∃.witness ep)) → (∃ Q)
[∃]-map-proof-dependent ([∃]-intro(x) ⦃ proof ⦄) f = [∃]-intro(x) ⦃ f(proof) ⦄

------------------------------------------
-- Universal quantification (Forall, All)

∀ₑₓₚₗ : (Pred : Obj → Stmt{ℓ}) → Stmt
∀ₑₓₚₗ (Pred) = (∀(x) → Pred(x))

∀ᵢₘₚₗ : (Pred : Obj → Stmt{ℓ}) → Stmt
∀ᵢₘₚₗ (Pred) = (∀{x} → Pred(x))

∀ᵢₙₛₜ : (Pred : Obj → Stmt{ℓ}) → Stmt
∀ᵢₙₛₜ (Pred) = (∀ ⦃ x ⦄ → Pred(x))

∀ₗ = ∀ᵢₘₚₗ

[∀]-intro : ((a : Obj) → Pred(a)) → ∀ₗ(x ↦ Pred(x))
[∀]-intro p{a} = p(a)

[∀]-elim : ∀ₗ(x ↦ Pred(x)) → (a : Obj) → Pred(a)
[∀]-elim p(a) = p{a}

-- Eliminates universal quantification for a non-empty domain using a witnessed existence which proves that the domain is non-empty.
[∀ₑ]-elim : ⦃ _ : ◊ Obj ⦄ → ∀{P : Obj → Stmt{ℓ}} → ∀ₗ(x ↦ P(x)) → P(inhabitant)
[∀ₑ]-elim {Obj = Obj} ⦃ proof ⦄ {P} apx = [∀]-elim {Obj = Obj}{P} apx(◊.inhabitant(proof))

syntax ∀ₗ{T}(λ x → y) = ∀❪ x ꞉ T ❫․ y

∀⁰ : (Pred : Stmt{ℓ}) → Stmt
∀⁰ = id

∀¹ : (Pred : X → Stmt{ℓ}) → Stmt
∀¹ (Pred) = ∀⁰(∀ₗ ∘₀ Pred)
-- ∀¹ (Pred) = (∀{x} → Pred(x))

∀² : (Pred : X → Y → Stmt{ℓ}) → Stmt
∀² (Pred) = ∀¹(∀ₗ ∘₁ Pred)
-- ∀² (Pred) = (∀{x}{y} → Pred(x)(y))

∀³ : (Pred : X → Y → Z → Stmt{ℓ}) → Stmt
∀³ (Pred) = ∀²(∀ₗ ∘₂ Pred)
-- ∀³ (Pred) = (∀{x}{y}{z} → Pred(x)(y)(z))

∀⁴ : (Pred : X → Y → Z → W → Stmt{ℓ}) → Stmt
∀⁴ (Pred) = ∀³(∀ₗ ∘₃ Pred)
-- ∀⁴ (Pred) = (∀{x}{y}{z}{w} → Pred(x)(y)(z)(w))
