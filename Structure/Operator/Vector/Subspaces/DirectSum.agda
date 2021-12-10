import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid
open import Type

module Structure.Operator.Vector.Subspaces.DirectSum
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ ℓₙ₀}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀} ⦄
  where

open VectorSpace(vectorSpace)

open import Data.Tuple as Tuple using (_,_)
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_ ; [∋]-binaryRelator)
open import Structure.Container.SetLike using (SetElement)
private open module SetLikeFunctionProperties{ℓ} = Structure.Container.SetLike.FunctionProperties{C = PredSet{ℓ}(V)}{E = V}(_∈_)
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Structure.Operator.Vector
open import Structure.Operator.Vector.Subspace ⦃ vectorSpace = vectorSpace ⦄
open import Syntax.Transitivity

private variable ℓ ℓ₁ ℓ₂ ℓₗ : Lvl.Level

module _ where
  module _ where
    -- TODO: This operator can also be constructed for vector spaces, not just subspaces
    _+ˢᵘᵇ_ : SubspaceObject{ℓ₁} → SubspaceObject{ℓ₂} → SubspaceObject
    ([∃]-intro V₁ ⦃ p₁ ⦄) +ˢᵘᵇ ([∃]-intro V₂ ⦃ p₂ ⦄) = [∃]-intro (PredSet.map₂(_+ᵥ_) V₁ V₂) ⦃ p ⦄ where
      p : Subspace(PredSet.map₂(_+ᵥ_) V₁ V₂)
      ∃.witness (Structure.Container.SetLike.FunctionProperties._closed-under₂_.proof (Subspace.add-closure p) ([∃]-intro(a₁ , a₂)) ([∃]-intro(b₁ , b₂))) = ((a₁ +ᵥ b₁) , (a₂ +ᵥ b₂))
      ∃.proof (Structure.Container.SetLike.FunctionProperties._closed-under₂_.proof (Subspace.add-closure p) {a}{b} ([∃]-intro ([∧]-intro a₁ a₂) ⦃ [∧]-intro ([∧]-intro a₁V₁ a₂V₂) a₁a₂a ⦄) ([∃]-intro (b₁ , b₂) ⦃ [∧]-intro ([∧]-intro b₁V₁ b₂V₂) b₁b₂b ⦄)) = [∧]-intro ([∧]-intro l₁ l₂) r where
        l₁ : (a₁ +ᵥ b₁) ∈ V₁
        l₁ = (V₁ closureUnder₂(_+ᵥ_)) a₁V₁ b₁V₁
        l₂ : (a₂ +ᵥ b₂) ∈ V₂
        l₂ = (V₂ closureUnder₂(_+ᵥ_)) a₂V₂ b₂V₂
        r : (a₁ +ᵥ b₁) +ᵥ (a₂ +ᵥ b₂) ≡ a +ᵥ b
        r =
          (a₁ +ᵥ b₁) +ᵥ (a₂ +ᵥ b₂) 🝖[ _≡_ ]-[ One.associate-commute4-c {_▫_ = _+ᵥ_} ⦃ op = [+ᵥ]-binaryOperator ⦄ ⦃ assoc = [+ᵥ]-associativity ⦄ ⦃ comm = [+ᵥ]-commutativity ⦄ ] -- TODO: Why are the instances not inferred?
          (a₁ +ᵥ a₂) +ᵥ (b₁ +ᵥ b₂) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) ⦃ [+ᵥ]-binaryOperator ⦄ a₁a₂a b₁b₂b ]
          a +ᵥ b                   🝖-end
      ∃.witness (Structure.Container.SetLike.FunctionProperties._closed-under₁_.proof (Subspace.mul-closure p {s}) ([∃]-intro(v₁ , v₂))) = ((s ⋅ₛᵥ v₁) , (s ⋅ₛᵥ v₂))
      ∃.proof (Structure.Container.SetLike.FunctionProperties._closed-under₁_.proof (Subspace.mul-closure p {s}) {v} ([∃]-intro(v₁ , v₂) ⦃ [∧]-intro ([∧]-intro v₁V₁ v₂V₂) v₁v₂v ⦄)) = [∧]-intro ([∧]-intro l₁ l₂) r where
        l₁ : (s ⋅ₛᵥ v₁) ∈ V₁
        l₁ = (V₁ closureUnder₁(s ⋅ₛᵥ_)) v₁V₁
        l₂ : (s ⋅ₛᵥ v₂) ∈ V₂
        l₂ = (V₂ closureUnder₁(s ⋅ₛᵥ_)) v₂V₂
        r : (s ⋅ₛᵥ v₁) +ᵥ (s ⋅ₛᵥ v₂) ≡ (s ⋅ₛᵥ v)
        r =
          (s ⋅ₛᵥ v₁) +ᵥ (s ⋅ₛᵥ v₂) 🝖[ _≡_ ]-[ distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_) ]-sym
          s ⋅ₛᵥ (v₁ +ᵥ v₂)         🝖[ _≡_ ]-[ congruence₂-₂(_⋅ₛᵥ_)(s) v₁v₂v ]
          s ⋅ₛᵥ v                  🝖-end

  -- TODO: Formulate
  -- [⊕ˢᵘᵇ]-span-vectorSpace : (V₁ ⊕ V₂ ⊕ … ≡ₛ 𝐔) ↔ (∀{v₁}{v₂}{…} → (v₁ ∈ V₁) → (v₂ ∈ V₂) → … → (v₁ + v₂ + … ≡ 𝟎ᵥ) → ((v₁ ≡ 𝟎ᵥ) ∧ (v₂ ≡ 𝟎ᵥ) ∧ …))
  -- [⊕ˢᵘᵇ]-span-existence-finite-space : Finite → ∃(\{(V₁ , V₂ , …) → V₁ ⊕ V₂ ⊕ … ≡ₛ 𝐔}) -- TODO: Just take the "standard" "axis aligned" subspaces
