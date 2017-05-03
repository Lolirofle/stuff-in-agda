module Structure.Operator.Properties {l₁} {l₂} where

import      Level as Lvl
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Relator.Equals{l₁}{l₂}
open import Type{l₁}

-- Definition of commutativity
Commutativity : {T₁ T₂ : Type} → (T₁ → T₁ → T₂) → Stmt
Commutativity {T₁} (_▫_) = {x y : T₁} → (x ▫ y) ≡ (y ▫ x)

DistributivityPatternₗ : {T₁ T₂ T₃ : Type} → (T₁ → T₂ → T₃) → (T₂ → T₂ → T₂) → (T₃ → T₃ → T₃) → Stmt
DistributivityPatternₗ {T₁} {T₂} {T₃} (_▫₁_) (_▫₂_) (_▫₃_) = ∀{x : T₁} {y z : T₂} → (x ▫₁ (y ▫₂ z)) ≡ (x ▫₁ y) ▫₃ (x ▫₁ z)

DistributivityPatternᵣ : {T₁ T₂ T₃ : Type} → (T₁ → T₂ → T₃) → (T₁ → T₁ → T₁) → (T₃ → T₃ → T₃) → Stmt
DistributivityPatternᵣ {T₁} {T₂} {T₃} (_▫₁_) (_▫₂_) (_▫₃_) = ∀{x y : T₁} {z : T₂} → ((x ▫₂ y) ▫₁ z) ≡ (x ▫₁ z) ▫₃ (y ▫₁ z)

-- Definition of left identity
Identityₗ : {T₁ T₂ : Type} → (T₁ → T₂ → T₂) → T₁ → Stmt
Identityₗ {_} {T₂} (_▫_) id = {x : T₂} → (id ▫ x) ≡ x

-- Definition of right identity
Identityᵣ : {T₁ T₂ : Type} → (T₁ → T₂ → T₁) → T₂ → Stmt
Identityᵣ {T₁} {_} (_▫_) id = {x : T₁} → (x ▫ id) ≡ x

-- Definition of a left inverse function -- TODO: Maybe rename to InverseFunctionₗ?
Inverseₗ : {T₊ T₋ Tᵣ : Type} → (T₋ → T₊ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
Inverseₗ {T₊} (_▫_) id inv = {x : T₊} → ((inv x) ▫ x) ≡ id

-- Definition of a right inverse function
Inverseᵣ : {T₊ T₋ Tᵣ : Type} → (T₊ → T₋ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
Inverseᵣ {T₊} (_▫_) id inv = {x : T₊} → (x ▫ (inv x)) ≡ id

-- Definition of a left absorber element
Absorberₗ : {T₁ T₂ : Type} → (T₁ → T₂ → T₁) → T₁ → Stmt
Absorberₗ {_} {T₂} (_▫_) null = ∀{x : T₂} → (null ▫ x) ≡ null

-- Definition of a right absorber element
Absorberᵣ : {T₁ T₂ : Type} → (T₁ → T₂ → T₂) → T₂ → Stmt
Absorberᵣ {T₁} {_} (_▫_) null = ∀{x : T₁} → (x ▫ null) ≡ null

AssociativityPattern : {T₁ T₂ T₃ Tᵣ₂ Tᵣ₃ Tᵣ : Type} → (T₁ → T₂ → Tᵣ₃) → (Tᵣ₃ → T₃ → Tᵣ)  → (T₁ → Tᵣ₂ → Tᵣ) → (T₂ → T₃ → Tᵣ₂)→ Stmt
AssociativityPattern {T₁} {T₂} {T₃} {Tᵣ₂} {Tᵣ₃} {Tᵣ} (_▫₁_) (_▫₂_) (_▫₃_) (_▫₄_) =
  {x : T₁}{y : T₂}{z : T₃} → ((x ▫₁ y) ▫₂ z) ≡ (x ▫₃ (y ▫₄ z))

---------------------------------------------------------
-- Derived

-- Definition of associativity for a binary operation
Associativity : {T : Type} → (T → T → T) → Stmt
Associativity {T} (_▫_) = AssociativityPattern (_▫_) (_▫_) (_▫_) (_▫_)
-- {x y z : T} → ((x ▫ y) ▫ z) ≡ (x ▫ (y ▫ z))

-- Definition of compatibility for a binary operation
Compatibility : {T₁ T₂ : Type} → (T₁ → T₁ → T₁) → (T₁ → T₂ → T₂) → Stmt
Compatibility {T₁} {T₂} (_▫₁_) (_▫₂_) = AssociativityPattern (_▫₁_) (_▫₂_) (_▫₂_) (_▫₂_)
-- {x₁ x₂ : T₁}{y : T₂} → ((x₁ ▫₁ x₂) ▫₂ y) ≡ (x₁ ▫₂ (x₂ ▫₂ y))

-- Definition of left distributivity for a binary operation
Distributivityₗ : {T₁ T₂ : Type} → (T₁ → T₂ → T₂) → (T₂ → T₂ → T₂) → Stmt
Distributivityₗ {T₁} {T₂} (_▫₁_) (_▫₂_) = DistributivityPatternₗ {T₁} {T₂} {T₂} (_▫₁_) (_▫₂_) (_▫₂_)
-- ∀{x : T₁} {y z : T₂} → (x ▫₁ (y ▫₂ z)) ≡ (x ▫₁ y) ▫₂ (x ▫₁ z)

-- Definition of right distributivity for a binary operation
Distributivityᵣ : {T₁ T₂ : Type} → (T₂ → T₁ → T₂) → (T₂ → T₂ → T₂) → Stmt
Distributivityᵣ {T₁} {T₂} (_▫₁_) (_▫₂_) = DistributivityPatternᵣ {T₂} {T₁} {T₂} (_▫₁_) (_▫₂_) (_▫₂_)
-- ∀{x y : T₂} {z : T₁} → ((x ▫₂ y) ▫₁ z) ≡ (x ▫₁ z) ▫₂ (y ▫₁ z)

---------------------------------------------------------
-- Functions

-- Returns a commuted LHS of an equality
commuteₗ : ∀{T _▫_ x y z} → {{_ : Commutativity {T} {T} (_▫_)}} → (x ▫ y ≡ z) → (y ▫ x ≡ z)
commuteₗ {{comm}} stmt =
  [≡]-transitivity([∧]-intro
    comm
    stmt
  )

-- Returns a commuted RHS of an equality
commuteᵣ : ∀{T _▫_ x y z} → {{_ : Commutativity {T} {T} (_▫_)}} → (z ≡ x ▫ y) → (z ≡ y ▫ x)
commuteᵣ {{comm}} stmt =
  [≡]-transitivity([∧]-intro
    stmt
    comm
  )
