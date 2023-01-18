module Structure.Category.Comma where

open import Data.Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equivalence
import      Lvl
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Logic.Propositional
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Categorical.Functor.Properties
open import Structure.Categorical.Names as Names
open import Structure.Categorical.Properties
open import Structure.Operator
open import Structure.Operator.Names as Names
open import Structure.Setoid
open import Syntax.Transitivity
open import Type
open import Type.Dependent.Sigma

private variable ℓ ℓₒ ℓₘ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level
private variable A B Obj Obj₁ Obj₂ Obj₃ : Type{ℓₒ}
private variable _⟶₁_ _⟶₂_ _⟶₃_ : Obj → Obj → Type{ℓₘ}
private variable s t : A → B

module _
  ⦃ morphism-equiv₁ : ∀{x y : Obj₁} → Equiv{ℓₑ₁}(x ⟶₁ y) ⦄
  ⦃ morphism-equiv₂ : ∀{x y : Obj₂} → Equiv{ℓₑ₂}(x ⟶₂ y) ⦄
  ⦃ morphism-equiv₃ : ∀{x y : Obj₃} → Equiv{ℓₑ₃}(x ⟶₃ y) ⦄
  {A : Category(_⟶₁_)}
  {B : Category(_⟶₂_)}
  {C : Category(_⟶₃_)}
  (S : Functor A C s)
  (T : Functor B C t)
  where

  open Category ⦃ … ⦄
  open Functor

  private open module MorphismEquiv₁ {x}{y} = Equiv(morphism-equiv₁{x}{y}) hiding (_≡_)
  private open module MorphismEquiv₂ {x}{y} = Equiv(morphism-equiv₂{x}{y}) hiding (_≡_)
  private open module MorphismEquiv₃ {x}{y} = Equiv(morphism-equiv₃{x}{y}) hiding (_≡_)

  private instance _ = A
  private instance _ = B
  private instance _ = C

  CommaObject : Type
  CommaObject = Σ(Obj₁ ⨯ Obj₂) (\(x , y) → s(x) ⟶₃ t(y))

  CommaMorphism : CommaObject → CommaObject → Type
  CommaMorphism (intro(x₁ , y₁) f) (intro(x₂ , y₂) g) = ∃(\((h₁ , h₂) : (x₁ ⟶₁ x₂) ⨯ (y₁ ⟶₂ y₂)) → map T(h₂) ∘ f ≡ g ∘ map S(h₁))

  _∘↓_ : ∀{x y z} → CommaMorphism y z → CommaMorphism x y → CommaMorphism x z
  _∘↓_ {intro(x₁ , y₁) xy₁} {intro(x₂ , y₂) xy₂} {intro(x₃ , y₃) xy₃} ([∃]-intro (f₁ , g₁) ⦃ p₁ ⦄) ([∃]-intro (f₂ , g₂) ⦃ p₂ ⦄) = [∃]-intro ((f₁ ∘ f₂) , (g₁ ∘ g₂)) ⦃ p ⦄ where
    p =
      map T(g₁ ∘ g₂) ∘ xy₁          🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(xy₁) (preserving₂(_⟶₂_)(_⟶₃_)(map T)(_∘_)(_∘_)) ]
      (map T(g₁) ∘ map T(g₂)) ∘ xy₁ 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
      map T(g₁) ∘ (map T(g₂) ∘ xy₁) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(map T(g₁)) p₂ ]
      map T(g₁) ∘ (xy₂ ∘ map S(f₂)) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
      (map T(g₁) ∘ xy₂) ∘ map S(f₂) 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(map S(f₂)) p₁ ]
      (xy₃ ∘ map S(f₁)) ∘ map S(f₂) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
      xy₃ ∘ (map S(f₁) ∘ map S(f₂)) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(xy₃) (preserving₂(_⟶₁_)(_⟶₃_)(map S)(_∘_)(_∘_)) ]-sym
      xy₃ ∘ (map S(f₁ ∘ f₂))        🝖-end

  id↓ : ∀{x} → CommaMorphism x x
  id↓ {intro(x , y) xy} = [∃]-intro(id , id) ⦃ p ⦄ where
    p =
      map T(id) ∘ xy 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(xy) (preserving₀(_⟶₂_)(_⟶₃_)(map T)(id)(id)) ]
      id ∘ xy        🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
      xy             🝖[ _≡_ ]-[ Morphism.identityᵣ(_∘_)(id) ]-sym
      xy ∘ id        🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(xy) (preserving₀(_⟶₁_)(_⟶₃_)(map S)(id)(id)) ]-sym
      xy ∘ map S(id) 🝖-end

  commaCategory : Category(CommaMorphism)
  Category._∘_ commaCategory = _∘↓_
  Category.id  commaCategory = id↓
  Category.binaryOperator commaCategory = intro \([∧]-intro p₁ p₂) ([∧]-intro q₁ q₂) → [∧]-intro
    (congruence₂(_∘_) p₁ q₁)
    (congruence₂(_∘_) p₂ q₂)
  Category.associativity  commaCategory = Morphism.intro ([∧]-intro (Morphism.associativity(_∘_)) (Morphism.associativity(_∘_)))
  Category.identity       commaCategory = [∧]-intro
    (Morphism.intro ([∧]-intro (Morphism.identityₗ(_∘_)(id)) (Morphism.identityₗ(_∘_)(id))))
    (Morphism.intro ([∧]-intro (Morphism.identityᵣ(_∘_)(id)) (Morphism.identityᵣ(_∘_)(id))))
