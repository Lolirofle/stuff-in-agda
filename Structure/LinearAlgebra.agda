module Structure.LinearAlgebra {ℓ} where

import      Lvl
open import Functional hiding (id)
open import Functional.Proofs
open import Logic.Propositional{ℓ Lvl.⊔ ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Proofs{ℓ}
open import Relator.Equals{ℓ}
open import Relator.Equals.Proofs{ℓ}
open import Relator.Equals.Uniqueness{ℓ}{ℓ}{ℓ}
open import Structure.Function.Domain{ℓ}
import      Structure.Function.Linear{ℓ}{ℓ} as Linear
open import Structure.Operator.Field{ℓ}{ℓ}
open import Structure.Operator.Group{ℓ}{ℓ}
open import Structure.Operator.Properties{ℓ}{ℓ}
open import Structure.Operator.Vector{ℓ}{ℓ}
open import Type{ℓ}

module _ {V S} ⦃ lang ⦄ (VSP : VectorSpace(V)(S) ⦃ lang ⦄) where
  module _ where
    open Language(lang)
    open VectorSpace(VSP)

    -- A list of scalars
    Scalars : ℕ → Stmt
    Scalars(n) = ((i : ℕ) → ⦃ _ : i < n ⦄ → S) -- TODO: Maybe use 𝕟 instead? Or just use CoordinateVector

    -- A list of vectors
    Vectors : ℕ → Stmt
    Vectors(n) = ((i : ℕ) → ⦃ _ : i < n ⦄ → V)

    module _ where
      LinearCombination : ∀{n} → Scalars(n) → Vectors(n) → V
      LinearCombination {0}       _ _ = 𝟎ᵥ
      LinearCombination {1}       sf vf = (sf(0) ⦃ [<][0]-minimum ⦄) ⋅ₛᵥ (vf(0) ⦃ [<][0]-minimum ⦄)
      LinearCombination {𝐒(𝐒(n))} sf vf = (LinearCombination {𝐒(n)} sf₋ vf₋) +ᵥ ((sf(𝐒(n)) ⦃ [<]-of-[𝐒] {𝐒(n)} ⦄) ⋅ₛᵥ (vf(𝐒(n)) ⦃ [<]-of-[𝐒] {𝐒(n)} ⦄)) where
        postulate sf₋ : (i : ℕ) → ⦃ _ : i < 𝐒(n) ⦄ → S
        postulate vf₋ : (i : ℕ) → ⦃ _ : i < 𝐒(n) ⦄ → V

      -- Spanning(vf) ⇔ (VSP = Span(vf))
      -- A set of vectors is spanning the vector space when every vector in the vector space can be represented as a linear combination of the set of vectors.
      Spanning : ∀{n} → Vectors(n) → Stmt
      Spanning(vf) = (∀{v} → ∃(sf ↦ v ≡ LinearCombination(sf)(vf)))

      -- Basis(vf) ⇔ (vf is a basis)
      -- A set of vectors is a basis when every vector in the vector space can be represented as a unique linear combination of the set of vectors.
      -- A set of vectors is a basis when they span the vector space and is linearly independent.
      Basis : ∀{n} → Vectors(n) → Stmt
      Basis(vf) = ∀{v} → ∃!(sf ↦ LinearCombination(sf)(vf) ≡ v)

-- TODO: Something with (<) and its instances are making this freeze
--      -- A set of vectors is linearly independent when there is no vector that can be represented as a linear combination by the others.
--      LinearlyIndependent : ∀{n} → Vectors(n) → Stmt
--      LinearlyIndependent{n}(vf) = ∀{sf} → (LinearCombination(sf)(vf) ≡ 𝟎ᵥ) → (∀{i} → ⦃ _ : i < n ⦄ → sf(i) ≡ 𝟎ₛ)
--
--      postulate basis-span-independent : ∀{n}{vf : Vectors(n)} → LinearlyIndependent(vf) ↔ (Basis(vf) ∧ LinearlyIndependent(vf))
--
--      -- Existence of a subset of spanning vectors which is a basis
--      -- TODO: postulate basis-from-spanning : ∀{n}{vf} → ⦃ _ : Spanning{n}(vf) ⦄ → ∃(m ↦ (m ≤ n) ∧ ∃(f ↦ Basis{n}(vf ∘ f) ∧ Injective(f)))
--
--      -- Existence of a basis
--      postulate basis-existence : ∃(n ↦ ∃(vf ↦ Basis{n}(vf)))
--
--      -- A set of linearly independent vectors is smaller than a set of basis vectors
--      postulate independent-lesser-than-basis-number : ∀{m n} → {vfₘ : Vectors(m)} → LinearlyIndependent(vfₘ) → {vfₙ : Vectors(n)} → Basis(vfₙ) → (m ≤ n)
--
--      -- Every set of basis vectors are equal in size
--      postulate basis-equal-number : ∀{m n} → {vfₘ : Vectors(m)} → Basis(vfₘ) → {vfₙ : Vectors(n)} → Basis(vfₙ) → (m ≡ n)
--
--      -- The dimension of the vector space
--      dim :  ℕ
--      dim = [∃]-witness(basis-existence)
--
--      -- Existence of a superset of linearly independent vectors which is a basis
--      -- TODO: basis-from-linearly-independent : ∀{n}{vf} → ⦃ _ : Spanning{n}(vf) ⦄ → ∃(m ↦ (m ≥ n) ∧ ∃(f ↦ Basis{n}(vf ∘ f) ∧ Injective(f)))
--
--      postulate basis-from-dim-spanning : ∀{vf} → Spanning{dim}(vf) → Basis{dim}(vf)
--
--      postulate basis-from-dim-independent : ∀{vf} → LinearlyIndependent{dim}(vf) → Basis{dim}(vf)
--
--      -- TODO: Move to some algebraic structure?
--      -- Nilpotent(f) = ∃(n ↦ ∀{v} → (f ^ n ≡ 𝟎ᵥ))
--
--    module _ where
--      private LinearMap = Linear.LinearMap(_+ᵥ_)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_)
--
--      postulate linear-map-id : LinearMap(Functional.id)
--
--      -- v is a eigenvector for the eigenvalue 𝜆 of the linear transformation f
--      Eigenvector : (V → V) → S → V → Stmt
--      Eigenvector(f)(𝜆)(v) = ((v ≢ 𝟎ᵥ) → (f(v) ≡ 𝜆 ⋅ₛᵥ v))
--
--      -- 𝜆 is a eigenvalue of the linear transformation f
--      -- Multiplication by an eigenvalue can replace a linear transformation for certain vectors.
--      Eigenvalue : (V → V) → S → Stmt
--      Eigenvalue(f)(𝜆) = (∀{v : V} → Eigenvector(f)(𝜆)(v))
--
--      -- Two linear mappings are similiar when there is a basis in which they are equal.
--      -- Similiar : (f : V → V) → ⦃ _ : LinearMap(f) ⦄ → (g : V → V) → ⦃ _ : LinearMap(g) ⦄ → Stmt
--      -- Similiar(f)(g) = (∀{v} → ∃(b ↦ Bijective(b) ∧ (f(v) ≡ (b ∘ g ∘ (inv-fn(b)))(v))))
--
--    record DotProductSpace (_∙_ : V → V → S) (_≤_ : S → S → Stmt) : Stmt where
--      field
--        commutativity     : Commutativity(_∙_)
--        linearmapₗ        : ∀{v₂} → Linear.LinearMap(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) (_∙ v₂)
--        positive          : ∀{v} → (𝟎ₛ ≤ (v ∙ v))
--        injective-zero    : ∀{v} → ((v ∙ v) ≡ 𝟎ₛ) → (v ≡ 𝟎ᵥ)
--
--      postulate [⋅ₛᵥ]-commuting : ∀{s}{v₁ v₂} → ((s ⋅ₛᵥ v₁) ∙ v₂) ≡ (v₁ ∙ (s ⋅ₛᵥ v₂))
--      postulate almost-injectivity-zeroₗ : ∀{v₁} → (∀{v₂} → ((v₁ ∙ v₂) ≡ 𝟎ₛ)) → (v₁ ≡ 𝟎ᵥ)
--      postulate injectivityₗ : ∀{v₁ v₂} → (∀{v₃} → ((v₁ ∙ v₃) ≡ (v₂ ∙ v₃))) → (v₁ ≡ v₂)
--
--      module Norm (√ : S → S) where
--        -- The length of a vector
--        norm : V → S
--        norm(v) = √(v ∙ v)
--
--        -- The positive part of a scalar
--        abs : S → S
--        abs(s) = √(s ⋅ₛ s)
--
--        postulate homogeneity : ∀{s}{v} → norm(s ⋅ₛᵥ v) ≡ abs(s) ⋅ₛ norm(v)
--        postulate triangle-inequality : ∀{v₁ v₂} → (norm(v₁ +ᵥ v₂) ≤ (norm(v₁) +ₛ norm(v₂)))
--        postulate positivity : ∀{v} → (𝟎ₛ ≤ norm(v))
--        postulate injectivity-zero : ∀{v} → (norm(v) ≡ 𝟎ₛ) → (v ≡ 𝟎ᵥ)
--        postulate mult-inequality : ∀{v₁ v₂} → (abs(v₁ ∙ v₂) ≤ (norm(v₁) ⋅ₛ norm(v₂)))
--
--        -- Two vectors are orthogonal when they are perpendicular.
--        Orthogonal : V → V → Stmt
--        Orthogonal(v₁)(v₂) = (v₁ ∙ v₂ ≡ 𝟎ₛ)
--
--        {-
--        OrthogonalAll : ∀{n} → Vectors(n) → Stmt
--        OrthogonalAll{0}       (vf) = ⊤
--        OrthogonalAll{1}       (vf) = Orthogonal(vf(0))(vf(1))
--        OrthogonalAll{𝐒(𝐒(n))} (vf) = (OrthogonalAll{n} (vf)) ∧ Orthogonal(vf(n))(vf(𝐒(n)))
--        -}
--
--        postulate hypotenuse-length : ∀{v₁ v₂} → ⦃ _ : Orthogonal(v₁)(v₂) ⦄ → ((v₁ +ᵥ v₂) ∙ (v₁ +ᵥ v₂) ≡ (v₁ ∙ v₁) +ₛ (v₂ ∙ v₂))
--
--        -- Transforms a vector to an unit vector in the same direction.
--        normalize : (v : V) → ⦃ _ : v ≢ 𝟎ᵥ ⦄ → V
--        normalize(v) ⦃ proof ⦄ = (⅟ₛ_ (norm(v)) ⦃ contrapositiveᵣ (injectivity-zero) (proof) ⦄) ⋅ₛᵥ v
--
--        postulate norm-of-normalize : ∀{v} → ⦃ nonzero : (v ≢ 𝟎ᵥ) ⦄ → (norm(normalize(v) ⦃ nonzero ⦄) ≡ 𝟏ₛ)
--
--  -- TODO: Is it okay for VSP₂ to have a different scalar field compared to VSP? Some stuff will not be compatible (like addition for the same scalar type)?
--  module _ {V₂} ⦃ lang₂ ⦄ (VSP₂ : VectorSpace(V₂)(S) ⦃ lang₂ ⦄) where
--    open Language ⦃ ... ⦄
--    open VectorSpace ⦃ ... ⦄
--
--    private _+ᵥ₁_ = _+ᵥ_ ⦃ lang ⦄
--    private _⋅ₛᵥ₁_ = _⋅ₛᵥ_ ⦃ lang ⦄
--    private _+ᵥ₂_ = _+ᵥ_ ⦃ lang₂ ⦄
--    private _⋅ₛᵥ₂_ = _⋅ₛᵥ_ ⦃ lang₂ ⦄
--
--    private LinearMap₁₂ = Linear.LinearMap(_+ᵥ₁_)(_⋅ₛᵥ₁_)(_+ᵥ₂_)(_⋅ₛᵥ₂_)
--    private LinearMap₂₁ = Linear.LinearMap(_+ᵥ₂_)(_⋅ₛᵥ₂_)(_+ᵥ₁_)(_⋅ₛᵥ₁_)
--
--    module _ where
--      -- Kernel(f)(v) ⇔ (v ∈ Kernel(f))
--      Kernel : (f : V → V₂) → ⦃ _ : LinearMap₁₂(f) ⦄ → V → Stmt
--      Kernel(f)(v) = (f(v) ≡ 𝟎ᵥ ⦃ lang₂ ⦄ ⦃ VSP₂ ⦄)
--
--      -- TODO: Move away the module for two vector spaces from one so that dim is not bound to V
--      -- rank : (V → V₂) → ℕ
--      -- rank(_) = dim ⦃ VSP₂ ⦄
--
--    module _ where
--      postulate linear-map-const-zero : LinearMap₁₂(const(𝟎ᵥ ⦃ lang₂ ⦄ ⦃ VSP₂ ⦄))
--
--      -- The inverse of an invertible linear mapping is a linear mapping
--      postulate linear-inverse : ∀{f} → ⦃ _ : Bijective(f) ⦄ → LinearMap₁₂(f) → LinearMap₂₁(inv-fn(f))
--
--      -- Injectivity for only the zero vector implies injectivity
--      postulate injective-zero : ∀{f} → ⦃ _ : LinearMap₁₂(f) ⦄ → (∀{v} → (f(v) ≡ 𝟎ᵥ ⦃ lang₂ ⦄ ⦃ VSP₂ ⦄) → (v ≡ 𝟎ᵥ ⦃ lang ⦄ ⦃ VSP ⦄)) → Injective(f)
--
--    -- module _ {_∙₁_ : V → V → S}{_≤₁_} {_∙₂_ : V₂ → V₂ → S}{_≤₂_} (DPSP₁ : DotProductSpace(_∙₁_)(_≤₁_)) (DPSP₂ : DotProductSpace(_∙₂_)(_≤₂_)) where
--    --   Adjoint : (f : V → V₂) → ⦃ _ : LinearMap₁₂(f) ⦄ → (g : V₂ → V) → ⦃ _ : LinearMap₂₁(g) ⦄ → Stmt
--    --   Adjoint(f)(g) = (∀{v₁ : V}{v₂ : V₂} → (f(v₁) ∙₂ v₂ ≡ v₁ ∙₁ g(v₂)))
