module Miscellaneous.associative-side where

private variable T : Set
private variable _▫_ : T → T → T
private variable id : T

data _≡_ {ℓ}{T : Set(ℓ)} : T → T → Set(ℓ) where
  [≡]-intro : ∀{x : T} → (x ≡ x)

Associativity : (T → T → T) → Set
Associativity(_▫_) = ∀{a b c} → ((a ▫ (b ▫ c)) ≡ ((a ▫ b) ▫ c))

Identityₗ : (T → T → T) → T → Set
Identityₗ(_▫_)(id) = ∀{a} → ((id ▫ a) ≡ a)

Identityᵣ : (T → T → T) → T → Set
Identityᵣ(_▫_)(id) = ∀{a} → ((a ▫ id) ≡ a)

right-op₂-associativity : Associativity{T}(\x y → y)
right-op₂-associativity = [≡]-intro

right-op₂-identityₗ : Identityₗ{T}(\x y → y)(id)
right-op₂-identityₗ {a = a} = [≡]-intro

right-op₂-when-identityᵣₗ : (∀{a} → (id ≡ a)) → Identityᵣ{T}(\x y → y)(id) 
right-op₂-when-identityᵣₗ p = p

right-op₂-when-identityᵣᵣ : Identityᵣ{T}(\x y → y)(id) → (∀{a} → (id ≡ a))
right-op₂-when-identityᵣᵣ p = p
