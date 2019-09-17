module Structure.Type.Quotient where

record Quotient (_/_ : Type → (Type → Type → Stmt) → Type) : Stmt where
  field
    intro : ∀{T}{_≡_} → T → (T / (_≡_))
    elim  : ∀{T}{_≡_} → (T / (_≡_)) → T
    inverseᵣ : ∀{T}{_≡_}{Q : (T / (_≡_))} → (intro(elim(Q)) ≡ₑ Q)
    extensionality : ∀{T} → ⦃ _ : Equiv(T) ⦄ → ∀{Q : (T / (_≡_))}{a b : Q} → (intro(a) ≡ intro(b)) ↔ (a ≡ b)

module Syntax where
  [_of_] x (_≡_) = Quotient.class{_≡_ = _≡_} (x)


record Filterer (Filter : ∀{T : Type} → (T → Stmt) → Type) : Stmt where
  field
    intro : ∀{P} → (x : T) → ⦃ _ : P(x) ⦄ → Filter(P)
    obj   : ∀{P} → Filter(P) → T
    proof : ∀{P} → (X : Filter(P)) → P(obj(X))
    inverseₗ : ∀{P}{X : Filter(P)} → (intro(obj(X)) ⦃ proof(X) ⦄ ≡ X)
    inverseᵣ : ∀{P}{x}{px} → (obj(intro(x) ⦃ px ⦄) ≡ x)
    extensionality : ∀{T} → ⦃ _ : Equiv(T) ⦄ → ∀{Q : (T / (_≡_))}{a b : Q} → (intro(a) ≡ intro(b)) ↔ (a ≡ b)
