module Structure.Type.Quotient where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Function hiding (intro)
open import Structure.Function.Domain hiding (intro)
open import Structure.Relator.Equivalence hiding (intro)
open import Structure.Setoid.WithLvl hiding (intro)
import      Type
open import Type.Properties.Empty hiding (intro)

record Quotient {ℓ₁ ℓ₂} {T : TYPE(ℓ₁)} (_≅_ : T → T → Stmt{ℓ₂}) ⦃ equivalence : Equivalence(_≅_) ⦄ : Stmtω where
  field
    {ℓ} : Lvl.Level
    Type : TYPE(ℓ)
    {ℓₑ} : Lvl.Level
    ⦃ equiv ⦄ : Equiv{ℓₑ}(Type) -- TODO: Consider using Id instead of this because otherwise every type has a quotient by just using itself
    class : T → Type
    ⦃ intro-function ⦄ : Function ⦃ Structure.Setoid.WithLvl.intro(_≅_) ⦃ equivalence ⦄ ⦄ (class)
    ⦃ intro-bijective ⦄ : Bijective ⦃ Structure.Setoid.WithLvl.intro(_≅_) ⦃ equivalence ⦄ ⦄ (class)
    -- elim : Type → T -- TODO: Choice?
    -- inverseᵣ : ∀{q : Type} → (class(elim(q)) ≡ q)
    -- extensionality : ∀{a b : T} → (class(a) ≡ class(b)) ↔ (a ≅ b)

_/_ : ∀{ℓ₁ ℓ₂} → (T : TYPE(ℓ₁)) → (_≅_ : T → T → Stmt{ℓ₂}) → ⦃ e : Equivalence(_≅_) ⦄ → ⦃ q : Quotient(_≅_) ⦃ e ⦄ ⦄ → TYPE(Quotient.ℓ q)
(T / (_≅_)) ⦃ _ ⦄ ⦃ q ⦄ = Quotient.Type(q)

[_of_] : ∀{ℓ₁ ℓ₂}{T : TYPE(ℓ₁)} → T → (_≅_ : T → T → Stmt{ℓ₂}) → ⦃ e : Equivalence(_≅_) ⦄ → ⦃ q : Quotient(_≅_) ⦃ e ⦄ ⦄ → (T / (_≅_))
[ x of (_≅_) ] ⦃ _ ⦄ ⦃ q ⦄ = Quotient.class(q)(x)

{-
record Filterer (Filter : ∀{T : Type} → (T → Stmt) → Type) : Stmt where
  field
    intro : ∀{P} → (x : T) → ⦃ _ : P(x) ⦄ → Filter(P)
    obj   : ∀{P} → Filter(P) → T
    proof : ∀{P} → (X : Filter(P)) → P(obj(X))
    inverseₗ : ∀{P}{X : Filter(P)} → (intro(obj(X)) ⦃ proof(X) ⦄ ≡ X)
    inverseᵣ : ∀{P}{x}{px} → (obj(intro(x) ⦃ px ⦄) ≡ x)
    extensionality : ∀{T} → ⦃ _ : Equiv(T) ⦄ → ∀{Q : (T / (_≡_))}{a b : Q} → (intro(a) ≡ intro(b)) ↔ (a ≡ b)
-}
