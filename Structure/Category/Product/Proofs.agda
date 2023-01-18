import      Lvl
open import Structure.Category

module Structure.Category.Product.Proofs
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C)) (let open ArrowNotation)
  where

open import Functional using (_$_ ; const)
open import Logic.Predicate
open import Structure.Categorical.Properties
open import Structure.Category.Functor
open import Structure.Category.Product {C = C}
open import Structure.Function
open import Structure.IndexedOperator.Properties.Preserving
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type
open import Type.Dependent.PiFunction.Category

module _
  {ℓ} {I : Type{ℓ}}
  {Π : (I → Object) → Object}
  ⦃ product : Product(I)(Π) ⦄
  where

  open Product(product)

  private open module MorphismEquiv{x}{y} = Equiv(morphism-equiv{x}{y}) using ()

  prod-proj-inverse : ∀{f} → (prod{f = f} proj ≡ id)
  prod-proj-inverse = symmetry(_≡_) (uniqueness-condition(Morphism.identityᵣ(_∘_)(id)))

  prod-function : ∀{x}{f : I → Object}{F G : (i : I) → (x ⟶ f(i))} → (∀{i} → (F(i) ≡ G(i))) → (prod(F) ≡ (prod G))
  prod-function FG = uniqueness-condition(inverse-condition 🝖 FG)

  map-functor : Functor ⦃ _ ⦄ (productCategory \_ → category) category Π
  Functor.map map-functor = map
  Functor.map-function  map-functor = intro \{f}{g} fg → prod-function \{i} → congruence₂-₁(_∘_)(proj(i)) (fg{i})
  Functor.op-preserving map-functor = intro \{f}{g} →
    map(\i → f(i) ∘ g(i))                                 🝖[ _≡_ ]-[]
    prod(\i → (f(i) ∘ g(i)) ∘ proj(i))                    🝖[ _≡_ ]-[ (uniqueness-condition \{i} →
      proj(i) ∘ (prod(\i → f(i) ∘ proj(i)) ∘ prod(\i → g(i) ∘ proj(i))) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
      (proj(i) ∘ prod(\i → f(i) ∘ proj(i))) ∘ prod(\i → g(i) ∘ proj(i)) 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(_) inverse-condition ]
      (f(i) ∘ proj(i)) ∘ prod(\i → g(i) ∘ proj(i))                      🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
      f(i) ∘ (proj(i) ∘ prod(\i → g(i) ∘ proj(i)))                      🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(_) inverse-condition ]
      f(i) ∘ (g(i) ∘ proj(i))                                           🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
      (f(i) ∘ g(i)) ∘ proj i                                            🝖-end
    ) ]-sym
    prod(\i → f(i) ∘ proj(i)) ∘ prod(\i → g(i) ∘ proj(i)) 🝖[ _≡_ ]-[]
    map f ∘ map g                                         🝖-end
  Functor.id-preserving map-functor = intro $
    map(\i → id)            🝖[ _≡_ ]-[]
    prod(\i → id ∘ proj(i)) 🝖[ _≡_ ]-[ prod-function(Morphism.identityₗ(_∘_)(id)) ]
    prod(\i → proj(i))      🝖[ _≡_ ]-[ prod-proj-inverse ]
    id                      🝖-end

  Πᶠᵘⁿᶜᵗᵒʳ : (Πᶜᵃᵗ I (const C)) →ᶠᵘⁿᶜᵗᵒʳ C
  Πᶠᵘⁿᶜᵗᵒʳ = [∃]-intro _ ⦃ map-functor ⦄
