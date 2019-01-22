
module Structure where
  -- Structures in meta-functions.
  module Function' where -- TODO: Temporary naming fix with tick
    module Properties ⦃ signature : Signature ⦄ where
      Type : Domain → Domain → Function → Formula
      Type(X)(Y)(f) = ∀ₛ(X)(x ↦ f(x) ∈ Y)

      Closed : Domain → Function → Formula
      Closed(S)(f) = Type(S)(S)(f)

      Injective'' : Domain → Function → Formula
      Injective''(A)(f) = ∀ₛ(A)(x ↦ ∀ₛ(A)(y ↦ (f(x) ≡ f(y)) ⟶ (x ≡ y)))

      Surjective'' : Domain → Domain → Function → Formula
      Surjective''(A)(B)(f) = ∀ₛ(B)(y ↦ ∃ₛ(A)(x ↦ f(x) ≡ y))

      Bijective'' : Domain → Domain → Function → Formula
      Bijective''(A)(B)(f) =
        Injective''(A)(f)
        ∧ Surjective''(A)(B)(f)

      Preserving₁'' : Domain → Function → Function → Function → Formula
      Preserving₁''(A)(f)(g₁)(g₂) = ∀ₛ(A)(x ↦ f(g₁(x)) ≡ g₂(f(x)))

      Preserving₂'' : Domain → Domain → Function → BinaryOperator → BinaryOperator → Formula
      Preserving₂''(A)(B)(f)(_▫₁_)(_▫₂_) = ∀ₛ(A)(x ↦ ∀ₛ(B)(y ↦ f(x ▫₁ y) ≡ (f(x) ▫₂ f(y))))

  module Relator where
    module Properties where
      Reflexivity : Domain → BinaryRelator → Formula
      Reflexivity(S)(_▫_) = ∀ₛ(S)(x ↦ x ▫ x)

      Irreflexivity : Domain → BinaryRelator → Formula
      Irreflexivity(S)(_▫_) = ∀ₛ(S)(x ↦ ¬(x ▫ x))

      Symmetry : Domain → BinaryRelator → Formula
      Symmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ⟶ (y ▫ x)))

      Asymmetry : Domain → BinaryRelator → Formula
      Asymmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ⟶ ¬(y ▫ x)))

      Antisymmetry : Domain → BinaryRelator → Formula
      Antisymmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y)∧(y ▫ x) ⟶ (x ≡ y)))

      Transitivity : Domain → BinaryRelator → Formula
      Transitivity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ (x ▫ y)∧(y ▫ z) ⟶ (x ▫ z))))

      Equivalence : Domain → BinaryRelator → Formula
      Equivalence(S)(_▫_) =
        Reflexivity(S)(_▫_)
        ∧ Symmetry(S)(_▫_)
        ∧ Transitivity(S)(_▫_)

      SymmetricallyTotal : Domain → BinaryRelator → Formula
      SymmetricallyTotal(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ∨ (y ▫ x)))

  module Ordering where
    open Relator.Properties

    Minima : Domain → BinaryRelator → Domain → Formula
    Minima(S)(_≤_)(min) = ∀ₛ(S)(x ↦ min ≤ x)

    Maxima : Domain → BinaryRelator → Domain → Formula
    Maxima(S)(_≤_)(max) = ∀ₛ(S)(x ↦ x ≤ max)

    module _  ⦃ signature : Signature ⦄ where
      open Signature ⦃ ... ⦄

      lowerBounds : Domain → BinaryRelator → Domain → Domain
      lowerBounds(S)(_≤_)(Sₛ) = filter(S)(Minima(S)(_≤_))

      upperBounds : Domain → BinaryRelator → Domain → Domain
      upperBounds(S)(_≤_)(Sₛ) = filter(S)(Maxima(S)(_≤_))

      interval : Domain → BinaryRelator → Domain → Domain → Domain
      interval(S)(_≤_) (a)(b) = filter(S)(s ↦ (a ≤ s) ∧ (s ≤ b))

      Bounded : Domain → BinaryRelator → Domain → Domain → Formula
      Bounded(S)(_≤_) (a)(b) = ∀ₛ(S)(s ↦ (a ≤ s) ∧ (s ≤ b))

      Infima : Domain → BinaryRelator → Domain → Domain → Formula
      Infima(S)(_≤_)(Sₛ)(inf) = Maxima(lowerBounds(S)(_≤_)(Sₛ))(_≤_)(inf)

      Suprema : Domain → BinaryRelator → Domain → Domain → Formula
      Suprema(S)(_≤_)(Sₛ)(sup) = Minima(upperBounds(S)(_≤_)(Sₛ))(_≤_)(sup)

    module Weak where
      PartialOrder : Domain → BinaryRelator → Formula
      PartialOrder(S)(_≤_) =
        Reflexivity(S)(_≤_)
        ∧ Antisymmetry(S)(_≤_)
        ∧ Transitivity(S)(_≤_)

      TotalOrder : Domain → BinaryRelator → Formula
      TotalOrder(S)(_≤_) =
        PartialOrder(S)(_≤_)
        ∧ SymmetricallyTotal(S)(_≤_)

    module Strict where
      Order : Domain → BinaryRelator → Formula
      Order(S)(_<_) =
        Irreflexivity(S)(_<_)
        ∧ Asymmetry(S)(_<_)
        ∧ Transitivity(S)(_<_)

      Dense : Domain → BinaryRelator → Formula
      Dense(S)(_<_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x < y) ⟶ ∃ₛ(S)(z ↦ (x < z)∧(z < y))))

  module Operator where
    module Properties where
      AssociativityPattern : Domain → Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
      AssociativityPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₃_)(_▫₄_) = (((x ▫₁ y) ▫₂ z) ≡ (x ▫₃ (y ▫₄ z)))

      DistributivityₗPattern : Domain → Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
      DistributivityₗPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₃_)(_▫₄_)(_▫₅_) = (x ▫₁ (y ▫₂ z)) ≡ ((x ▫₃ y) ▫₄ (x ▫₅ z))

      DistributivityᵣPattern : Domain → Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
      DistributivityᵣPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₃_)(_▫₄_)(_▫₅_) = ((x ▫₂ y) ▫₁ z) ≡ ((x ▫₃ z) ▫₄  (y ▫₅ z))

      Type : BinaryOperator → Domain → Domain → Domain → Formula
      Type(_▫_)(X)(Y)(Z) = ∀ₛ(X)(x ↦ ∀ₛ(Y)(y ↦ (x ▫ y) ∈ Z))

      Closed : Domain → BinaryOperator → Formula
      Closed(S)(_▫_) = Type(_▫_)(S)(S)(S)

      Commutativity : Domain → BinaryOperator → Formula
      Commutativity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ≡ (y ▫ x)))

      Associativity : Domain → BinaryOperator → Formula
      Associativity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ AssociativityPattern(x)(y)(z)(_▫_)(_▫_)(_▫_)(_▫_))))

      Identityₗ : Domain → BinaryOperator → Domain → Formula
      Identityₗ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ (id ▫ x) ≡ x)

      Identityᵣ : Domain → BinaryOperator → Domain → Formula
      Identityᵣ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ (x ▫ id) ≡ x)

      Identity : Domain → BinaryOperator → Domain → Formula
      Identity(S)(_▫_)(id) = Identityₗ(S)(_▫_)(id) ∧ Identityᵣ(S)(_▫_)(id)

      Invertibleₗ : Domain → BinaryOperator → Domain → Formula
      Invertibleₗ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ (x⁻¹ ▫ x) ≡ id))

      Invertibleᵣ : Domain → BinaryOperator → Domain → Formula
      Invertibleᵣ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ (x ▫ x⁻¹) ≡ id))

      Invertible : Domain → BinaryOperator → Domain → Formula
      Invertible(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ ((x⁻¹ ▫ x) ≡ id) ∧ ((x ▫ x⁻¹) ≡ id)))

      Distributivityₗ : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivityₗ(S)(_▫₁_)(_▫₂_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ DistributivityₗPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₁_)(_▫₂_)(_▫₁_))))

      Distributivityᵣ : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivityᵣ(S)(_▫₁_)(_▫₂_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ DistributivityᵣPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₁_)(_▫₂_)(_▫₁_))))

      Distributivity : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivity(S)(_▫₁_)(_▫₂_) = Distributivityₗ(S)(_▫₁_)(_▫₂_) ∧ Distributivityᵣ(S)(_▫₁_)(_▫₂_)

      Compatibility : Domain → Domain → BinaryOperator → BinaryOperator → Formula
      Compatibility(A)(B)(_▫₁_)(_▫₂_) = ∀ₛ(A)(a₁ ↦ ∀ₛ(A)(a₂ ↦ ∀ₛ(B)(b ↦ AssociativityPattern(a₁)(a₂)(b)(_▫₁_)(_▫₁_)(_▫₂_)(_▫₁_))))

      Semigroup : Domain → BinaryOperator → Formula
      Semigroup(S)(_▫_) =
        Closed(S)(_▫_)
        ∧ Associativity(S)(_▫_)

      Monoid : Domain → BinaryOperator → Formula
      Monoid(S)(_▫_) =
        Semigroup(S)(_▫_)
        ∧ ∃ₛ(S)(Identity(S)(_▫_))

      Group : Domain → BinaryOperator → Formula
      Group(S)(_▫_) =
        Monoid(S)(_▫_)
        ∧ ∀ₛ(S)(id ↦ Identity(S)(_▫_)(id) ⟶ Invertible(S)(_▫_)(id))

      CommutativeGroup : Domain → BinaryOperator → Formula
      CommutativeGroup(S)(_▫_) =
        Group(S)(_▫_)
        ∧ Commutativity(S)(_▫_)

      Rng : Domain → BinaryOperator → BinaryOperator → Formula
      Rng(S)(_▫₁_)(_▫₂_) =
        CommutativeGroup(S)(_▫₁_)
        ∧ Semigroup(S)(_▫₂_)
        ∧ Distributivity(S)(_▫₂_)(_▫₁_)

      Ring : Domain → BinaryOperator → BinaryOperator → Formula
      Ring(S)(_▫₁_)(_▫₂_) =
        CommutativeGroup(S)(_▫₁_)
        ∧ Monoid(S)(_▫₂_)
        ∧ Distributivity(S)(_▫₂_)(_▫₁_)

      module _  ⦃ signature : Signature ⦄ where
        open Signature ⦃ ... ⦄

        Field : Domain → BinaryOperator → BinaryOperator → Formula
        Field(S)(_▫₁_)(_▫₂_) =
          CommutativeGroup(S)(_▫₁_)
          ∧ ∀ₛ(S)(id₁ ↦ Identity(S)(_▫₁_)(id₁) ⟶ CommutativeGroup(S ∖ singleton(id₁))(_▫₂_))
          ∧ Distributivity(S)(_▫₂_)(_▫₁_)

        VectorSpace : Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
        VectorSpace(V)(S)(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) =
          CommutativeGroup(V)(_+ᵥ_)
          ∧ Field(S)(_+ₛ_)(_⋅ₛ_)
          ∧ ∀ₛ(S)(id ↦ Identity(S)(_⋅ₛ_)(id) ⟶ Identityₗ(V)(_⋅ₛᵥ_)(id))
          ∧ Compatibility(S)(V)(_⋅ₛᵥ_)(_⋅ₛ_)
          ∧ ∀ₛ(S)(s ↦ ∀ₛ(V)(v₁ ↦ ∀ₛ(V)(v₂ ↦ DistributivityₗPattern(s)(v₁)(v₂)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_))))
          ∧ ∀ₛ(S)(s₁ ↦ ∀ₛ(S)(s₂ ↦ ∀ₛ(V)(v ↦ DistributivityᵣPattern(s₁)(s₂)(v)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_))))

  module Numeral where
    module Natural ⦃ signature : Signature ⦄ where
      open Signature ⦃ ... ⦄

      FormulaInduction : Domain → Domain → Function → (Domain → Formula) → Formula
      FormulaInduction(ℕ)(𝟎)(𝐒) (φ) = (φ(𝟎) ∧ ∀ₛ(ℕ)(n ↦ φ(n) ⟶ φ(𝐒(n)))) ⟶ ∀ₛ(ℕ)(φ)

      SetInduction : Domain → Domain → Function → Formula
      SetInduction(ℕ)(𝟎)(𝐒) = ∀ₗ(X ↦ ((𝟎 ∈ X) ∧ ∀ₛ(ℕ)(n ↦ (n ∈ X) ⟶ (𝐒(n) ∈ X))) ⟶ (ℕ ⊆ X))
      -- TODO: Can be expressed as ∀ₗ(X ↦ Inductive(X) ⟶ (ℕ ⊆ X))

      -- A set ℕ which can be constructed ℕ-inductively.
      Peano : Domain → Domain → Function → Formula
      Peano(ℕ)(𝟎)(𝐒) =
        (𝟎 ∈ ℕ)
        ∧ Function'.Properties.Closed(ℕ)(𝐒)
        ∧ Function'.Properties.Injective''(ℕ)(𝐒)
        ∧ ∀ₛ(ℕ)(n ↦ 𝐒(n) ≢ 𝟎)
        ∧ SetInduction(ℕ)(𝟎)(𝐒)
