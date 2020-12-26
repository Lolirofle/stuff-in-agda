module Structure.Operator.Monoid.Monoids.Coset where

open import Functional
open import Function.Equals
open import Function.Equals.Proofs
import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function.Multi
open import Structure.Operator.Monoid
open import Structure.Operator.Monoid.Homomorphism
open import Structure.Operator.Monoid.Monoids.Function
open import Structure.Operator.Monoid.Submonoid
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ function : ∀{f : T → T} → Function(f) ⦄ {_▫_ : T → T → T} (monoid : Monoid(_▫_)) where
  cosetₗ-submonoid : Submonoid(function-monoid)(⊶(_▫_))
  Submonoid.contains-identity cosetₗ-submonoid = [∃]-intro (_) ⦃ intro(identityₗ(_▫_)(_)) ⦄
  Submonoid.operator-closure  cosetₗ-submonoid {f}{g} ⦃ [∃]-intro a ⦃ pa ⦄ ⦄ ⦃ [∃]-intro b ⦃ pb ⦄ ⦄ =
    [∃]-intro (a ▫ b) ⦃ intro (\{x} →
      ((a ▫ b) ▫ x) 🝖[ _≡ₑ_ ]-[ associativity(_▫_) ]
      (a ▫ (b ▫ x)) 🝖[ _≡ₑ_ ]-[ _⊜_.proof pa ]
      f(b ▫ x)      🝖[ _≡ₑ_ ]-[ congruence₁(f) (_⊜_.proof pb) ]
      f(g(x))       🝖[ _≡ₑ_ ]-[]
      (f ∘ g)(x)    🝖-end
    ) ⦄

  cosetᵣ-submonoid : Submonoid(function-monoid)(⊶(swap(_▫_)))
  Submonoid.contains-identity cosetᵣ-submonoid = [∃]-intro (_) ⦃ intro(identityᵣ(_▫_)(_)) ⦄
  Submonoid.operator-closure  cosetᵣ-submonoid {f}{g} ⦃ [∃]-intro a ⦃ pa ⦄ ⦄ ⦃ [∃]-intro b ⦃ pb ⦄ ⦄ =
    [∃]-intro (b ▫ a) ⦃ intro (\{x} →
      (x ▫ (b ▫ a)) 🝖[ _≡ₑ_ ]-[ associativity(_▫_) ]-sym
      ((x ▫ b) ▫ a) 🝖[ _≡ₑ_ ]-[ _⊜_.proof pa ]
      f(x ▫ b)      🝖[ _≡ₑ_ ]-[ congruence₁(f) (_⊜_.proof pb) ]
      f(g(x))       🝖[ _≡ₑ_ ]-[]
      (f ∘ g)(x)    🝖-end
    ) ⦄

  cosetₗ-homomorphism : ∃(Homomorphism monoid (Submonoid.monoid cosetₗ-submonoid))
  ∃.witness cosetₗ-homomorphism a = [∃]-intro (a ▫_) ⦃ [∃]-intro a ⦃ reflexivity(_≡ₑ_) {a ▫_} ⦄ ⦄
  _⊜_.proof (Function.congruence (Homomorphism.function (∃.proof cosetₗ-homomorphism)) ab) {x}  = congruence₂ₗ(_▫_)(x) ab
  _⊜_.proof (Preserving.proof (Homomorphism.preserve-op (∃.proof cosetₗ-homomorphism))     {x}) = associativity(_▫_)
  _⊜_.proof (Preserving.proof (Homomorphism.preserve-id (∃.proof cosetₗ-homomorphism)))    {x}  = identityₗ(_▫_)(_)

  instance
    cosetₗ-surjective : Surjective([∃]-witness cosetₗ-homomorphism)
    Surjective.proof cosetₗ-surjective {[∃]-intro f ⦃ pf ⦄} = pf

  instance
    cosetₗ-injective : Injective([∃]-witness cosetₗ-homomorphism)
    Injective.proof cosetₗ-injective {x} {y} (intro xy) =
      x                    🝖[ _≡ₑ_ ]-[ identityᵣ(_▫_)(_) ]-sym
      x ▫ Monoid.id monoid 🝖[ _≡ₑ_ ]-[ xy {Monoid.id monoid} ]
      y ▫ Monoid.id monoid 🝖[ _≡ₑ_ ]-[ identityᵣ(_▫_)(_) ]
      y                    🝖-end

  instance
    cosetₗ-bijective : Bijective([∃]-witness cosetₗ-homomorphism)
    cosetₗ-bijective = injective-surjective-to-bijective([∃]-witness cosetₗ-homomorphism)

  {-
  cosetᵣ-homomorphism : ∃(Homomorphism monoid (Submonoid.monoid cosetᵣ-submonoid))
  ∃.witness cosetᵣ-homomorphism a = [∃]-intro (_▫ a) ⦃ [∃]-intro a ⦃ reflexivity(_≡ₑ_) {_▫ a} ⦄ ⦄
  _⊜_.proof (Function.congruence (Homomorphism.function (∃.proof cosetᵣ-homomorphism)) ab) {x}  = congruence₂ᵣ(_▫_)(x) ab
  _⊜_.proof (Preserving.proof (Homomorphism.preserve-op (∃.proof cosetᵣ-homomorphism)) {a} {b}) {x} =
    (x ▫ (a ▫ b)) 🝖[ _≡ₑ_ ]-[ {!!} ]
    ((x ▫ b) ▫ a) 🝖-end
  _⊜_.proof (Preserving.proof (Homomorphism.preserve-id (∃.proof cosetᵣ-homomorphism)))    {x}  = identityᵣ(_▫_)(_)
  -}
