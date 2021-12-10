import      Lvl
open import Structure.Category

module Structure.Category.Functor.Equiv
  {ℓₗₒ ℓᵣₒ ℓₗₘ ℓᵣₘ ℓₗₑ ℓᵣₑ : Lvl.Level}
  {catₗ : CategoryObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ}}
  {catᵣ : CategoryObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ}}
  where

open import Functional.Dependent as Fn using (_$_)
import      Function.Equals
open        Function.Equals.Dependent
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
open import Relator.Equals.Proofs.Equiv
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors as Functors
open import Structure.Category.Morphism.IdTransport
import      Structure.Categorical.Names as Names
open import Structure.Category.NaturalTransformation
open import Structure.Category.Proofs
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

open Structure.Category

open Category ⦃ … ⦄
open CategoryObject
open Functor ⦃ … ⦄
private instance _ = category catₗ
private instance _ = category catᵣ
private open module MorphismEquivₗ {x}{y} = Equiv(morphism-equiv(catₗ){x}{y}) using () renaming (_≡_ to _≡ₗₘ_)
private open module MorphismEquivᵣ {x}{y} = Equiv(morphism-equiv(catᵣ){x}{y}) using () renaming (_≡_ to _≡ᵣₘ_)

module _
  (f₁@([∃]-intro F₁) f₂@([∃]-intro F₂) : (catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ))
  where

  record _≡ᶠᵘⁿᶜᵗᵒʳ_ : Type{Lvl.of(Type.of(catₗ)) Lvl.⊔ Lvl.of(Type.of(catᵣ))} where
    constructor intro
    field
      functor-proof : (F₁ ⊜ F₂)
      map-proof : NaturalTransformation(f₁)(f₂) (\x → transport(catᵣ) (_⊜_.proof functor-proof {x}))

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
      trans-refl = \{x} → transport(catᵣ) ([≡]-intro {x = x})

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-symmetry : Symmetry(_≡ᶠᵘⁿᶜᵗᵒʳ_)
  _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (Symmetry.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-symmetry xy) = symmetry(_⊜_) (_≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof xy)
  NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (Symmetry.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-symmetry {[∃]-intro F₁} {[∃]-intro F₂} (intro (intro fe) (intro me)))) {x}{y} {f = f} =
    trans-sym(y) ∘ map(f)                               🝖[ _≡ᵣₘ_ ]-[ Morphism.identityᵣ(_∘_)(id) ]-sym
    (trans-sym(y) ∘ map(f)) ∘ id                        🝖[ _≡ᵣₘ_ ]-[ congruence₂-₂(_∘_)(_) ([∘]-on-transport-inverseᵣ catᵣ {ab = fe}) ]-sym
    (trans-sym(y) ∘ map(f)) ∘ (trans(x) ∘ trans-sym(x)) 🝖[ _≡ᵣₘ_ ]-[ associate4-213-121 (category catᵣ) ]-sym
    (trans-sym(y) ∘ (map(f) ∘ trans(x))) ∘ trans-sym(x) 🝖[ _≡ᵣₘ_ ]-[ congruence₂-₁(_∘_)(_) (congruence₂-₂(_∘_)(_) me) ]-sym
    (trans-sym(y) ∘ (trans(y) ∘ map(f))) ∘ trans-sym(x) 🝖[ _≡ᵣₘ_ ]-[ associate4-213-121 (category catᵣ) ]
    (trans-sym(y) ∘ trans(y)) ∘ (map(f) ∘ trans-sym(x)) 🝖[ _≡ᵣₘ_ ]-[ congruence₂-₁(_∘_)(_) ([∘]-on-transport-inverseₗ catᵣ {ab = fe}) ]
    id ∘ (map(f) ∘ trans-sym(x))                        🝖[ _≡ᵣₘ_ ]-[ Morphism.identityₗ(_∘_)(id) ]
    map(f) ∘ trans-sym(x)                               🝖-end
    where
      trans     = \(x : Object(catₗ)) → transport catᵣ (fe{x})
      trans-sym = \(x : Object(catₗ)) → transport catᵣ (symmetry(_≡ₑ_) (fe{x}))

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-transitivity : Transitivity(_≡ᶠᵘⁿᶜᵗᵒʳ_)
  _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (Transitivity.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-transitivity (intro fe₁ _) (intro fe₂ _)) = transitivity(_⊜_) fe₁ fe₂
  NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (Transitivity.proof [≡ᶠᵘⁿᶜᵗᵒʳ]-transitivity {[∃]-intro F₁} {[∃]-intro F₂} {[∃]-intro F₃} (intro (intro fe₁) (intro me₁)) (intro (intro fe₂) (intro me₂)))) {x}{y} {f = f} =
    transport catᵣ (transitivity(_≡ₑ_) (fe₁{y}) (fe₂{y})) ∘ map(f) 🝖[ _≡ᵣₘ_ ]-[ congruence₂-₁(_∘_)(_) (transport-of-transitivity catᵣ {ab = fe₁}{bc = fe₂}) ]
    (transport catᵣ (fe₂{y}) ∘ transport catᵣ (fe₁{y})) ∘ map(f)         🝖[ _≡ᵣₘ_ ]-[ Morphism.associativity(_∘_) ]
    transport catᵣ (fe₂{y}) ∘ (transport catᵣ (fe₁{y}) ∘ map(f))         🝖[ _≡ᵣₘ_ ]-[ congruence₂-₂(_∘_)(_) me₁ ]
    transport catᵣ (fe₂{y}) ∘ (map(f) ∘ transport catᵣ (fe₁{x}))         🝖[ _≡ᵣₘ_ ]-[ Morphism.associativity(_∘_) ]-sym
    (transport catᵣ (fe₂{y}) ∘ map(f)) ∘ transport catᵣ (fe₁{x})         🝖[ _≡ᵣₘ_ ]-[ congruence₂-₁(_∘_)(_) me₂ ]
    (map(f) ∘ transport catᵣ (fe₂{x})) ∘ transport catᵣ (fe₁{x})         🝖[ _≡ᵣₘ_ ]-[ Morphism.associativity(_∘_) ]
    map(f) ∘ (transport catᵣ (fe₂{x}) ∘ transport catᵣ (fe₁{x}))         🝖[ _≡ᵣₘ_ ]-[ congruence₂-₂(_∘_)(_) (transport-of-transitivity catᵣ {ab = fe₁}{bc = fe₂}) ]-sym
    map(f) ∘ transport catᵣ (transitivity(_≡ₑ_) (fe₁{x}) (fe₂{x})) 🝖-end

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-equivalence : Equivalence(_≡ᶠᵘⁿᶜᵗᵒʳ_)
  [≡ᶠᵘⁿᶜᵗᵒʳ]-equivalence = intro

instance
  [≡ᶠᵘⁿᶜᵗᵒʳ]-equiv : Equiv(catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)
  [≡ᶠᵘⁿᶜᵗᵒʳ]-equiv = intro(_≡ᶠᵘⁿᶜᵗᵒʳ_) ⦃ [≡ᶠᵘⁿᶜᵗᵒʳ]-equivalence ⦄
