module Structure.Type.Quotient where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Setoid hiding (intro)
open import Structure.Relator.Equivalence hiding (intro)
open import Type renaming (Type to Ty)
open import Type.Empty hiding (intro)

record Quotient {ℓ₁ ℓ₂} {T : Ty{ℓ₁}} (_≅_ : T → T → Stmt{ℓ₂}) ⦃ equivalence : Equivalence(_≅_) ⦄ : Stmtω where
  field
    {ℓ} : Lvl.Level
    Type : Ty{ℓ}
    ⦃ equiv ⦄ : Equiv(Type)
    intro : T → Type
    elim : Type → T
    inverseᵣ : ∀{q : Type} → (intro(elim(q)) ≡ q)
    extensionality : ∀{a b : T} → (intro(a) ≡ intro(b)) ↔ (a ≅ b)

_/_ : ∀{ℓ₁ ℓ₂} → (T : Ty{ℓ₁}) → (_≅_ : T → T → Stmt{ℓ₂}) → ⦃ e : Equivalence(_≅_) ⦄ → ⦃ q : Quotient(_≅_) ⦃ e ⦄ ⦄ → Ty{Quotient.ℓ q}
(T / (_≅_)) ⦃ _ ⦄ ⦃ q ⦄ = Quotient.Type(q)

[_of_] : ∀{ℓ₁ ℓ₂}{T : Ty{ℓ₁}} → T → (_≅_ : T → T → Stmt{ℓ₂}) → ⦃ e : Equivalence(_≅_) ⦄ → ⦃ q : Quotient(_≅_) ⦃ e ⦄ ⦄ → (T / (_≅_))
[ x of (_≅_) ] ⦃ _ ⦄ ⦃ q ⦄ = Quotient.intro(q)(x)

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
