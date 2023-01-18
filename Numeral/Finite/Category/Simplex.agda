module Numeral.Finite.Category.Simplex where

open import Functional using (_∘_ ; id)
open import Logic.Predicate
open import Logic.Predicate.Equiv
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Relation.Order using (_≤_)
open import Numeral.Natural
open import Structure.Category
open import Type
open import Type.Identity
open import Type.Identity.Proofs

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B I : Type{ℓ}
private variable a b c d : T
private variable f g h : A → B
private variable _▫_ _▫₁_ _▫₂_ _▫₃_ _▫ₗ₁_ _▫ₗ₂_ _▫ᵣ₁_ _▫ᵣ₂_ : T → T → Type{ℓ}

open import Functional.Instance
open import Structure.Relator.Properties
module _ (_▫ₗ_ : A → A → Type{ℓ₁}) (_▫ᵣ_ : B → B → Type{ℓ₂}) where
  module _ (f : A → B) where
    record Preserving : Type{Lvl.of(A) Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x y} → (x ▫ₗ y) → (f(x) ▫ᵣ f(y))
    preserving = inferArg Preserving.proof

  PreservingMap : Type
  PreservingMap = ∃(Preserving)

[∘]-preserving : (let _ = _▫₁_) → ⦃ Preserving(_▫₂_)(_▫₃_)(f) ⦄ → ⦃ Preserving(_▫₁_)(_▫₂_)(g) ⦄ → Preserving(_▫₁_)(_▫₃_)(f ∘ g)
[∘]-preserving {_▫₁_ = _▫₁_}{_▫₂_ = _▫₂_}{_▫₃_ = _▫₃_} {f}{g} = intro(preserving(_▫₂_)(_▫₃_)(f) ∘ preserving(_▫₁_)(_▫₂_)(g))

id-preserving : Preserving(_▫_)(_▫_)(id)
id-preserving = intro id

sub-preserving : ⦃ (_▫ₗ₁_) ⊇₂ (_▫ₗ₂_) ⦄ → ⦃ (_▫ᵣ₁_) ⊆₂ (_▫ᵣ₂_) ⦄ → ⦃ Preserving(_▫ₗ₁_)(_▫ᵣ₁_)(f) ⦄ → Preserving(_▫ₗ₂_)(_▫ᵣ₂_)(f)
sub-preserving {_▫ₗ₁_ = _▫ₗ₁_} {_▫ₗ₂_ = _▫ₗ₂_} {_▫ᵣ₁_ = _▫ᵣ₁_} {_▫ᵣ₂_ = _▫ᵣ₂_} {f = f} = intro(sub₂(_▫ᵣ₁_)(_▫ᵣ₂_) ∘ preserving(_▫ₗ₁_)(_▫ᵣ₁_)(f) ∘ sub₂(_▫ₗ₂_)(_▫ₗ₁_))

instance
  [⊆₂]-reflexivity : Reflexivity(_⊆₂_ {A = A}{B = B}{ℓ})
  [⊆₂]-reflexivity = intro(intro id)



-- Also called: Order preserving mappings, monotonically non-decreasing functions.
_<→>_ : ℕ → ℕ → Type
a <→> b = PreservingMap{A = 𝕟(a)}{B = 𝕟(b)} (_≤_)(_≤_)

open import Structure.Relator.Properties.Proofs
_<∘>_ : let _ = a in (b <→> c) → (a <→> b) → (a <→> c)
([∃]-intro f) <∘> ([∃]-intro g) = [∃]-intro (f ∘ g) ⦃ [∘]-preserving ⦄

<id> : a <→> a
<id> = [∃]-intro id ⦃ id-preserving ⦄

open import Function.Equiv as Fn
open import Function.Equiv.Proofs
open import Function.Proofs
open import Logic.Propositional
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Setoid

private instance _ = \{n} → Id-equiv {T = 𝕟(n)}
private instance _ = Id-to-function

module _
  {ℓₑ}
  ⦃ equiv : ∀{a b} → Equiv{ℓₑ}(𝕟(a) → 𝕟(b)) ⦄
  ⦃ ext : ∀{a b} → Fn.Extensionality Id-equiv (equiv{a}{b}) ⦄
  where

  simplexCategory : Category{Obj = ℕ} (_<→>_) -- TODO: on₂-category
  Category._∘_ simplexCategory = _<∘>_
  Category.id  simplexCategory = <id>
  Category.binaryOperator simplexCategory = intro(congruence₂(_∘_))
  Category.associativity  simplexCategory = Morphism.intro \{a}{b}{c}{d} {f}{g}{h} → [∘]-associativity {a = 𝕟 a}{𝕟 b}{𝕟 c}{𝕟 d} {[∃]-witness f}{[∃]-witness g}{[∃]-witness h}
  Category.identity       simplexCategory = [∧]-intro
    (Morphism.intro [∘]-identityₗ)
    (Morphism.intro [∘]-identityᵣ)

  Δ : CategoryObject 
  Δ = intro simplexCategory

  open import Structure.Category.Dual
  open import Structure.Category.Functor
  open import Type.Category.FakeExtensionalFunctionsCategory

  simplicialSet : Type{ℓₑ Lvl.⊔ Lvl.𝐒(ℓ)}
  simplicialSet{ℓ} = dual(Δ) →ᶠᵘⁿᶜᵗᵒʳ FakeExtensionalTypeᶜᵃᵗ{ℓ} -- TODO: Presheaf
