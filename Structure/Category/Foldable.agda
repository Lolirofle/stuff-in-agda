open import Structure.Setoid
open import Type

module Structure.Category.Foldable where

open import Functional as Fn using (pointwise₂,₁ ; const)
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Category
open import Structure.Category.Enriched.Monoid -- TODO: Or maybe use a hom-functor and Struture.Operator.Monoid instead?
open import Structure.Category.Monoidal
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Type.Function
open import Syntax.Function

module _
  {ℓₒ ℓₘ ℓₑ}
  (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}) (let open CategoryObject(C)) (let open ArrowNotation)
  ⦃ M : Monoidalᶜᵃᵗ(C) ⦄ (let open Monoidalᶜᵃᵗ(M) renaming (unitObject to 𝟏))
  (L : Object → Object)
  where

  record Foldable : Type{ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where -- Lvl.𝐒(ℓᵢ) Lvl.⊔ Lvl.𝐒(ℓₚ) Lvl.⊔ ℓᵣ Lvl.⊔ ℓ Lvl.⊔ ℓₑ
    field
      foldMap : ∀{a b} ⦃ monoid : Monoid(C)(b) ⦄ → (a ⟶ b) → (L(a) ⟶ b)

    fold : ∀{m} → ⦃ monoid : Monoid(C)(m) ⦄ → (L(m) ⟶ m)
    fold = foldMap id

    {-
    foldᵣ : ∀{a b} → ((a ⊗ b) ⟶ b) → (𝟏 ⟶ b) → (L(a) ⟶ b)
    foldᵣ{a}{b} (▫) e = f ∘ fold where
      f : a ⟶ b
      f = (▫) ∘ (id{a} <⊗> e) ∘ υᵣ⁻¹(a)

      instance
        monoid : Monoid(C)(a)
        ∃.witness monoid = ({!!} , {!!})
        ∃.proof monoid = {!!}
    -}  

    foldᵣ : ∀{a b} → ((a ⊗ b) ⟶ b) → (𝟏 ⟶ b) → (L(a) ⟶ b)
    foldᵣ{a}{b} (▫) e = foldMap((▫) ∘ (id{a} <⊗> e) ∘ υᵣ⁻¹(a)) where
      instance
        monoid : Monoid(C)(b)
        ∃.witness monoid = ((▫) ∘ ({!!} <⊗> id)) , e
        ∃.proof monoid = {!!}

open import Data.Tuple as Tuple
open import Data.List
-- TODO: This is how foldᵣ should be implemented using foldMap. Use a closed monoidal category.
test : (∀{a b : TYPE} → ((b ⨯ b) → b) → b → (a → b) → (List(a) → b)) → (∀{a b : TYPE} → ((a ⨯ b) → b) → b → (List(a) → b))
test foldMap {a}{b} _▫_ e l = foldMap {a}{b → b} (Tuple.uncurry Fn._∘_) Fn.id (Tuple.curry _▫_) l e

{-
 {ℓᵣ ℓ ℓₑ} (Range : Type{ℓᵣ}) {T : Type{ℓ}} (_▫_ : T → T → T) ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  field
    preserves-operator : ∀{r}{f g} → (∑(r) (pointwise₂,₁(_▫_) f g) ≡ (∑(r) f) ▫ (∑(r) g))
    preserves-identity : ∀{id} ⦃ ident  : Identity(_▫_)(id) ⦄ → ∀{r}{f} → (∀{i : Index(r)} → (f(i) ≡ id)) → (∑(r) f ≡ id)
    preserves-absorber : ∀{ab} ⦃ absorb : Absorber(_▫_)(ab) ⦄ → ∀{r}{f} → ∃(\(i : Index(r)) → (f(i) ≡ ab)) → (∑(r) f ≡ ab)

open Summation ⦃ … ⦄ using (∑) public
-}
