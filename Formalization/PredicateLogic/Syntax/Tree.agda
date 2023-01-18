open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Syntax.Tree (𝔏 : Signature) where
open Signature(𝔏)

open import Data.DependentWidthTree as Tree hiding (height)
import      DependentFunctional
import      Logic.Propositional as Logic
import      Lvl
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Formalization.PredicateLogic.Syntax.Substitution(𝔏)
open import Functional using (_∘_ ; _∘₂_ ; _∘₃_ ; _∘₄_ ; swap ; _←_ ; _on₂_)
open import Numeral.Finite
open import Numeral.Natural.Function.Proofs
open import Numeral.Natural.Inductions
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural
open import Relator.Equals
open import Structure.Relator
open import Structure.Relator.Ordering
open import Structure.Relator.Ordering.Proofs
open import Structure.Relator.Properties
open import Type.Dependent.Sigma
open import Type

private variable ℓ : Lvl.Level
private variable vars vars₁ vars₂ : ℕ
private variable φ ψ : Formula(vars)

tree : Formula(vars) → FiniteTreeStructure
tree (_ $ _) = Node 0 \()
tree ⊤       = Node 0 \()
tree ⊥       = Node 0 \()
tree (φ ∧ ψ) = Node 2 \{𝟎 → tree φ; (𝐒 𝟎) → tree ψ}
tree (φ ∨ ψ) = Node 2 \{𝟎 → tree φ; (𝐒 𝟎) → tree ψ}
tree (φ ⟶ ψ) = Node 2 \{𝟎 → tree φ; (𝐒 𝟎) → tree ψ}
tree (Ɐ φ)   = Node 1 \{𝟎 → tree φ}
tree (∃ φ)   = Node 1 \{𝟎 → tree φ}

height : Formula(vars) → ℕ
height = Tree.height ∘ tree

-- Ordering on formulas based on the height of their tree representation.
_<↑_ : (Σ ℕ Formula) → (Σ ℕ Formula) → Type
_<↑_ = (_<_) on₂ (height DependentFunctional.∘ Σ.right)

substitute-height : ∀{t} → (height(substitute{vars₁ = vars₁}{vars₂ = vars₂} t φ) ≡ height φ)
substitute-height {φ = f $ x} = [≡]-intro
substitute-height {φ = ⊤}     = [≡]-intro
substitute-height {φ = ⊥}     = [≡]-intro
substitute-height {φ = φ ∧ ψ} {t} rewrite substitute-height {φ = φ}{t} rewrite substitute-height {φ = ψ}{t} = [≡]-intro
substitute-height {φ = φ ∨ ψ} {t} rewrite substitute-height {φ = φ}{t} rewrite substitute-height {φ = ψ}{t} = [≡]-intro
substitute-height {φ = φ ⟶ ψ} {t} rewrite substitute-height {φ = φ}{t} rewrite substitute-height {φ = ψ}{t} = [≡]-intro
substitute-height {φ = Ɐ φ}   {t} rewrite substitute-height {φ = φ}{termMapper𝐒 t} = [≡]-intro
substitute-height {φ = ∃ φ}   {t} rewrite substitute-height {φ = φ}{termMapper𝐒 t} = [≡]-intro

instance
  [<↑]-wellfounded : Strict.Properties.WellFounded(_<↑_)
  [<↑]-wellfounded = wellfounded-image-by-trans {f = height DependentFunctional.∘ Σ.right}

induction-on-height : (P : ∀{vars} → Formula(vars) → Type{ℓ}) → (∀{vars}{φ : Formula(vars)} → (∀{vars}{ψ : Formula(vars)} → (height ψ < height φ) → P(ψ)) → P(φ)) → ∀{vars}{φ : Formula(vars)} → P(φ)
induction-on-height P step {vars}{φ} = Strict.Properties.wellfounded-induction(_<↑_) (\{ {intro vars φ} p → step{vars}{φ} \{vars}{ψ} ph → p{intro vars ψ} ⦃ ph ⦄}) {intro vars φ}

⊤-height-order : (height{vars} ⊤ ≤ height φ)
⊤-height-order = [≤]-minimum

⊥-height-order : (height{vars} ⊥ ≤ height φ)
⊥-height-order = [≤]-minimum

∧-height-orderₗ : (height φ < height(φ ∧ ψ))
∧-height-orderₗ = succ(Logic.[∧]-elimₗ max-order)

∧-height-orderᵣ : (height ψ < height(φ ∧ ψ))
∧-height-orderᵣ = succ(Logic.[∧]-elimᵣ max-order)

∨-height-orderₗ : (height φ < height(φ ∨ ψ))
∨-height-orderₗ = succ(Logic.[∧]-elimₗ max-order)

∨-height-orderᵣ : (height ψ < height(φ ∨ ψ))
∨-height-orderᵣ = succ(Logic.[∧]-elimᵣ max-order)

⟶-height-orderₗ : (height φ < height(φ ⟶ ψ))
⟶-height-orderₗ = succ(Logic.[∧]-elimₗ max-order)

⟶-height-orderᵣ : (height ψ < height(φ ⟶ ψ))
⟶-height-orderᵣ = succ(Logic.[∧]-elimᵣ max-order)

Ɐ-height-order : (height φ < height(Ɐ φ))
Ɐ-height-order = succ(reflexivity(_≤_))

∃-height-order : (height φ < height(∃ φ))
∃-height-order = succ(reflexivity(_≤_))

-- induction-on-height : ∀{P : ∀{vars} → Formula(vars) → Type{ℓ}} → (∀{vars} → P{vars}(⊤)) → (∀{vars} → P{vars}(⊥)) → ((∀{vars}{ψ : Formula(vars)} → (height ψ < height φ) → P(ψ)) → P(φ)) → P(φ)
-- induction-on-height {φ = φ} base⊤ base⊥ step = step {!Strict.Properties.wellfounded-induction(_<↑_)!}
