import      Lvl
open import Structure.Category
open import Structure.Setoid using (Equiv ; intro)
open import Type

module Structure.Category.Functor.Equiv
  {ℓₗₒ ℓᵣₒ ℓₗₘ ℓᵣₘ : Lvl.Level}
  {Objₗ : Type{ℓₗₒ}}
  {Morphismₗ : Objₗ → Objₗ → Type{ℓₗₘ}}
  ⦃ morphism-equivₗ : ∀{x y : Objₗ} → Equiv(Morphismₗ x y) ⦄
  {catₗ : Category(Morphismₗ) ⦃ morphism-equivₗ ⦄}
  {Objᵣ : Type{ℓᵣₒ}}
  {Morphismᵣ : Objᵣ → Objᵣ → Type{ℓᵣₘ}}
  ⦃ morphism-equivᵣ : ∀{x y : Objᵣ} → Equiv(Morphismᵣ x y) ⦄
  {catᵣ : Category(Morphismᵣ) ⦃ morphism-equivᵣ ⦄}
  where

open import Functional.Dependent as Fn using (_$_)
import      Function.Equals
open        Function.Equals.Dependent
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
open import Relator.Equals.Proofs.Equivalence
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors as Functors
import      Structure.Category.Morphism.IdTransport
import      Structure.Category.Names as Names
open import Structure.Category.NaturalTransformation
open import Structure.Category.Proofs
open import Structure.Category.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Transitivity

open Structure.Category
open Functors.Wrapped
open module MorphismEquivₗ {x}{y} = Equiv(morphism-equivₗ{x}{y}) using () renaming (_≡_ to _≡ₗₘ_)
open module MorphismEquivᵣ {x}{y} = Equiv(morphism-equivᵣ{x}{y}) using () renaming (_≡_ to _≡ᵣₘ_)
open Names.ArrowNotation(Morphismₗ) using () renaming (_⟶_ to _⟶ₗ_)
open Names.ArrowNotation(Morphismᵣ) using () renaming (_⟶_ to _⟶ᵣ_)

open Category ⦃ … ⦄
open Structure.Category.Morphism.IdTransport ⦃ … ⦄
private instance _ = catₗ
private instance _ = catᵣ

module _ (f₁@([∃]-intro F₁ ⦃ functor₁ ⦄) f₂@([∃]-intro F₂ ⦃ functor₂ ⦄) : (catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)) where
  open Functor(functor₁) using () renaming (map to map₁)
  open Functor(functor₂) using () renaming (map to map₂)

  record _≡ᶠᵘⁿᶜᵗᵒʳ_ : Type{Lvl.of(type-of(catₗ)) ⊔ Lvl.of(type-of(catᵣ))} where
    constructor intro
    field
      functor-proof : (F₁ ⊜ F₂)
      map-proof : NaturalTransformation(f₁)(f₂) (\x → transport(_⊜_.proof functor-proof {x}))

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-reflexivity : Reflexivity(_≡ᶠᵘⁿᶜᵗᵒʳ_)
  _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (Reflexivity.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-reflexivity) = intro [≡]-intro
  NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (Reflexivity.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-reflexivity {functor})) {f = f} =
    trans-refl ∘ map(f) 🝖[ _≡ᵣₘ_ ]-[]
    id ∘ map(f)         🝖[ _≡ᵣₘ_ ]-[ Morphism.identityₗ(_∘_)(id) ]
    map(f)              🝖[ _≡ᵣₘ_ ]-[ Morphism.identityᵣ(_∘_)(id) ]-sym
    map(f) ∘ id         🝖[ _≡ᵣₘ_ ]-[]
    map(f) ∘ trans-refl 🝖-end
    where
      open Functor ⦃ … ⦄
      trans-refl = \{x : Objᵣ} → transport([≡]-intro {x = x})

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-symmetry : Symmetry(_≡ᶠᵘⁿᶜᵗᵒʳ_)
  _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (Symmetry.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-symmetry xy) = symmetry(_⊜_) (_≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof xy)
  NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (Symmetry.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-symmetry {[∃]-intro F₁} {[∃]-intro F₂} (intro (intro fe) (intro me)))) {x}{y} {f = f} =
    trans-sym(y) ∘ map(f)                               🝖[ _≡ᵣₘ_ ]-[ Morphism.identityᵣ(_∘_)(id) ]-sym
    (trans-sym(y) ∘ map(f)) ∘ id                        🝖[ _≡ᵣₘ_ ]-[ congruence₂ᵣ(_∘_)(_) ([∘]-on-transport-inverseᵣ {ab = fe}) ]-sym
    (trans-sym(y) ∘ map(f)) ∘ (trans(x) ∘ trans-sym(x)) 🝖[ _≡ᵣₘ_ ]-[ associate4-213-121 catᵣ ]-sym
    (trans-sym(y) ∘ (map(f) ∘ trans(x))) ∘ trans-sym(x) 🝖[ _≡ᵣₘ_ ]-[ congruence₂ₗ(_∘_)(_) (congruence₂ᵣ(_∘_)(_) me) ]-sym
    (trans-sym(y) ∘ (trans(y) ∘ map(f))) ∘ trans-sym(x) 🝖[ _≡ᵣₘ_ ]-[ associate4-213-121 catᵣ ]
    (trans-sym(y) ∘ trans(y)) ∘ (map(f) ∘ trans-sym(x)) 🝖[ _≡ᵣₘ_ ]-[ congruence₂ₗ(_∘_)(_) ([∘]-on-transport-inverseₗ {ab = fe}) ]
    id ∘ (map(f) ∘ trans-sym(x))                        🝖[ _≡ᵣₘ_ ]-[ Morphism.identityₗ(_∘_)(id) ]
    map(f) ∘ trans-sym(x)                               🝖-end
    where
      open Functor ⦃ … ⦄
      trans     = \(x : Objₗ) → transport(fe{x})
      trans-sym = \(x : Objₗ) → transport(symmetry(_≡ₑ_) (fe{x}))

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-transitivity : Transitivity(_≡ᶠᵘⁿᶜᵗᵒʳ_)
  _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (Transitivity.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-transitivity (intro fe₁ _) (intro fe₂ _)) = transitivity(_⊜_) fe₁ fe₂
  NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (Transitivity.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-transitivity {[∃]-intro F₁} {[∃]-intro F₂} {[∃]-intro F₃} (intro (intro fe₁) (intro me₁)) (intro (intro fe₂) (intro me₂)))) {x}{y} {f = f} =
    transport(transitivity(_≡ₑ_) (fe₁{y}) (fe₂{y})) ∘ map(f) 🝖[ _≡ᵣₘ_ ]-[ congruence₂ₗ(_∘_)(_) (transport-of-transitivity {ab = fe₁}{bc = fe₂}) ]
    (transport(fe₂{y}) ∘ transport(fe₁{y})) ∘ map(f)         🝖[ _≡ᵣₘ_ ]-[ Morphism.associativity(_∘_) ]
    transport(fe₂{y}) ∘ (transport(fe₁{y}) ∘ map(f))         🝖[ _≡ᵣₘ_ ]-[ congruence₂ᵣ(_∘_)(_) me₁ ]
    transport(fe₂{y}) ∘ (map(f) ∘ transport(fe₁{x}))         🝖[ _≡ᵣₘ_ ]-[ Morphism.associativity(_∘_) ]-sym
    (transport(fe₂{y}) ∘ map(f)) ∘ transport(fe₁{x})         🝖[ _≡ᵣₘ_ ]-[ congruence₂ₗ(_∘_)(_) me₂ ]
    (map(f) ∘ transport(fe₂{x})) ∘ transport(fe₁{x})         🝖[ _≡ᵣₘ_ ]-[ Morphism.associativity(_∘_) ]
    map(f) ∘ (transport(fe₂{x}) ∘ transport(fe₁{x}))         🝖[ _≡ᵣₘ_ ]-[ congruence₂ᵣ(_∘_)(_) (transport-of-transitivity {ab = fe₁}{bc = fe₂}) ]-sym
    map(f) ∘ transport(transitivity(_≡ₑ_) (fe₁{x}) (fe₂{x})) 🝖-end
    where
      open Functor ⦃ … ⦄

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-equivalence : Equivalence(_≡ᶠᵘⁿᶜᵗᵒʳ_)
  [≡ᶠᵘⁿᶜᵗᵒʳ]-equivalence = intro

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-equiv : Equiv(catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)
  [≡ᶠᵘⁿᶜᵗᵒʳ]-equiv = intro(_≡ᶠᵘⁿᶜᵗᵒʳ_) ⦃ [≡ᶠᵘⁿᶜᵗᵒʳ]-equivalence ⦄
