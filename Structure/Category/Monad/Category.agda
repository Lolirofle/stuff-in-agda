open import Structure.Setoid
open import Structure.Category
open import Structure.Category.Monad
open import Type

module Structure.Category.Monad.Category
  {ℓₒ ℓₘ}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  {cat : Category(Morphism)}
  {T : Obj → Obj}
  (monad : Monad{cat = cat}(T))
  where

open import Data.Tuple as Tuple using ()
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
import      Function.Equals
open        Function.Equals.Dependent
open import Logic.Predicate
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors
open import Structure.Category.Monad.ExtensionSystem {cat = cat}
open import Structure.Category.NaturalTransformation
open import Structure.Category.NaturalTransformation.NaturalTransformations
open import Structure.Category.Proofs
open import Structure.Categorical.Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Transitivity

open Category.ArrowNotation(cat)
open Category(cat)
open Components(cat)(cat)
open Monad(monad)
open Morphism.OperModule{Morphism = Morphism}(_∘_)
open Morphism.OperModule.IdModule{Morphism = Morphism}(_∘_)(id)
open Functor(functor)
private instance _ = cat
private open module MorphismEquiv {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

-- Extension operator
-- Also called: _*
ext : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))
ext {x}{y} f = μ(y) ∘ map(f)

extension-system : ExtensionSystem(T)
ExtensionSystem.η extension-system = η
ExtensionSystem.ext extension-system = ext
Function.congruence (ExtensionSystem.ext-function extension-system) xy = congruence₂ᵣ(_∘_)(_) (congruence₁(map) xy)
ExtensionSystem.ext-inverse extension-system = _⊜_.proof μ-functor-[∘]-identityₗ
ExtensionSystem.ext-identity extension-system {x} {y} {f} =
  ext(f) ∘ η(x)          🝖[ _≡_ ]-[]
  (μ(y) ∘ map(f)) ∘ η(x) 🝖-[ Morphism.associativity(_∘_) ]
  μ(y) ∘ (map(f) ∘ η(x)) 🝖-[ congruence₂ᵣ(_∘_)(_) (symmetry(_≡_) η-natural) ]
  μ(y) ∘ (η(T(y)) ∘ f)   🝖-[ symmetry(_≡_) (Morphism.associativity(_∘_)) ]
  (μ(y) ∘ η(T(y))) ∘ f   🝖-[ congruence₂ₗ(_∘_)(_) (_⊜_.proof μ-functor-[∘]-identityᵣ) ]
  id ∘ f                 🝖-[ Morphism.identityₗ(_∘_)(id) ]
  f                      🝖-end
ExtensionSystem.ext-distribute extension-system {x} {y} {z} {f} {g} =
  ext(ext(f) ∘ g)                               🝖[ _≡_ ]-[]
  μ(z) ∘ map((μ(z) ∘ map(f)) ∘ g)               🝖-[ congruence₂ᵣ(_∘_)(_) op-preserving ]
  μ(z) ∘ (map(μ(z) ∘ map(f)) ∘ map(g))          🝖-[ congruence₂ᵣ(_∘_)(_) (congruence₂ₗ(_∘_)(_) op-preserving) ]
  μ(z) ∘ ((map(μ(z)) ∘ map(map(f))) ∘ map(g))   🝖-[ associate4-231-123(cat) ]
  ((μ(z) ∘ map(μ(z))) ∘ map(map(f))) ∘ map(g)   🝖-[  congruence₂ₗ(_∘_)(_) ( congruence₂ₗ(_∘_)(_) (_⊜_.proof μ-functor-[∘]-commutativity)) ]
  ((μ(z) ∘ μ(T(z))) ∘ map(map(f))) ∘ map(g)     🝖-[ associate4-123-213(cat) ]
  (μ(z) ∘ (μ(T(z)) ∘ map(map(f)))) ∘ map(g)     🝖-[ congruence₂ₗ(_∘_)(_) (congruence₂ᵣ(_∘_)(_) (NaturalTransformation.natural([∃]-proof Μ))) ]
  (μ(z) ∘ (map(f) ∘ μ(y))) ∘ map(g)             🝖-[ associate4-213-121(cat) ]
  (μ(z) ∘ map(f)) ∘ (μ(y) ∘ map(g))             🝖[ _≡_ ]-[]
  ext(f) ∘ ext(g)                               🝖-end

-- Also called: Kleisli category
monad-category : Category(\x y → (x ⟶ T(y)))
Category._∘_ monad-category f g = ext(f) ∘ g
Category.id monad-category {x} = η(x)
BinaryOperator.congruence (Category.binaryOperator monad-category {x}{y}{z}) {f₁}{f₂} f₁f₂ {g₁}{g₂} g₁g₂ =
  ext(f₁) ∘ g₁         🝖[ _≡_ ]-[]
  (μ(z) ∘ map f₁) ∘ g₁ 🝖-[ Morphism.associativity(_∘_) ]
  μ(z) ∘ (map f₁ ∘ g₁) 🝖-[ congruence₂ᵣ(_∘_)(μ(z)) (congruence₂(_∘_) (congruence₁(map) f₁f₂) g₁g₂) ]
  μ(z) ∘ (map f₂ ∘ g₂) 🝖-[ Morphism.associativity(_∘_) ]-sym
  (μ(z) ∘ map f₂) ∘ g₂ 🝖[ _≡_ ]-[]
  ext(f₂) ∘ g₂         🝖-end
Morphism.Associativity.proof (Category.associativity monad-category) {x} {y} {z} {w} {f} {g} {h} =
  ext(ext(f) ∘ g) ∘ h   🝖-[ congruence₂ₗ(_∘_)(_) (ExtensionSystem.ext-distribute extension-system) ]
  (ext(f) ∘ ext(g)) ∘ h 🝖-[ Morphism.associativity(_∘_) ]
  ext(f) ∘ (ext(g) ∘ h) 🝖-end
Morphism.Identityₗ.proof (Tuple.left (Category.identity monad-category)) {x} {y} {f} =
  ext(η(y)) ∘ f          🝖[ _≡_ ]-[]
  (μ(y) ∘ map(η(y))) ∘ f 🝖-[ congruence₂ₗ(_∘_)(f) (_⊜_.proof μ-functor-[∘]-identityₗ) ]
  id ∘ f                 🝖-[ Morphism.identityₗ(_∘_)(id) ]
  f                      🝖-end
Morphism.Identityᵣ.proof (Tuple.right (Category.identity monad-category)) {x} {y} {f} = ExtensionSystem.ext-identity extension-system
