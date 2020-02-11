module Sets.Setoid where -- TODO: Move to Structure.Setoid

import Lvl
open import Functional
open import Lang.Instance
open import Logic.Propositional
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties using (Reflexivity ; Symmetry ; Transitivity)

module _ {ℓₒ} where
  -- An instance of `Equiv(T)` is that the type `T` has an equivalence relation which may be treated as a default one.
  -- Helps finding an instance of an equivalence relation for a type.
  record Equiv (T : Set(ℓₒ)) : Set(Lvl.𝐒(ℓₒ)) where
    constructor intro

    infixl 15 _≡_ _≢_
    field
      _≡_ : T → T → Set(ℓₒ)

    field
      instance ⦃ [≡]-equivalence ⦄ : Equivalence(_≡_)

    _≢_ : T → T → Set(ℓₒ)
    a ≢ b = ¬(a ≡ b)

    -- open Equivalence([≡]-equivalence) using () renaming (transitivity to [≡]-transitivity ; symmetry to [≡]-symmetry ; reflexivity to [≡]-reflexivity) public

  open Equiv ⦃ ... ⦄ public
  {-# STATIC _≡_ #-} -- TODO: Not sure if these are doing anything, but it would be nice if (_≡_) would be replaced by the corresponding equivalence relation before everything (specifically before projection elimination so that when the relation is a record so that the following would work: record _▫_ A B where field a : _ ; b : _ ; [▫]-reflexivity : Names.reflexivity(_▫_) ; a([▫]-reflexivity) = _ ; b([▫]-reflexivity) = _)
  {-# INLINE _≡_ #-}
  {-# DISPLAY Equiv._≡_ a b = a ≡ b #-}

  -- A set and an equivalence relation on it
  record Setoid : Set(Lvl.𝐒(ℓₒ)) where
    constructor intro
    field
      Type : Set(ℓₒ)
      instance ⦃ Eq ⦄ : Equiv(Type)

-- TODO: Maybe these should be moved and renamed to function like all other properties in Structure.Operator and Structure.Function

-- The function `f` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
module _ {ℓₒ₁}{ℓₒ₂} {A : Set(ℓₒ₁)} ⦃ _ : Equiv(A) ⦄ {B : Set(ℓₒ₂)} ⦃ _ : Equiv(B) ⦄ where
  record Function (f : A → B) : Set(ℓₒ₁ Lvl.⊔ ℓₒ₂) where
    constructor intro

    field
      congruence : ∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y))

  [≡]-with : (f : A → B) → ⦃ _ : Function(f) ⦄ → ∀{x y} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with f ⦃ inst ⦄ = Function.congruence{f} (inst)

module _ {ℓₒ₁}{ℓₒ₂}{ℓₒ₃} where
  open Structure.Relator.Properties

  -- The operator `_▫_` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
  record BinaryOperator {T₁ : Set(ℓₒ₁)} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Set(ℓₒ₂)} ⦃ _ : Equiv(T₂) ⦄ {T₃ : Set(ℓₒ₃)} ⦃ _ : Equiv(T₃) ⦄ (_▫_ : T₁ → T₂ → T₃) : Set(ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃) where
    constructor intro

    field
      congruence : ∀{x₁ y₁ : T₁} → (x₁ ≡ y₁) → ∀{x₂ y₂ : T₂} → (x₂ ≡ y₂) → (x₁ ▫ x₂ ≡ y₁ ▫ y₂)

    instance
      left : ∀{x} → Function(_▫ x)
      left = intro(proof ↦ congruence proof (reflexivity(_≡_)))

    instance
      right : ∀{x} → Function(x ▫_)
      right = intro(proof ↦ congruence (reflexivity(_≡_)) proof)

  module _ {A₁ : Set(ℓₒ₁)} ⦃ _ : Equiv(A₁) ⦄ {A₂ : Set(ℓₒ₂)} ⦃ _ : Equiv(A₂) ⦄ {B : Set(ℓₒ₃)} ⦃ _ : Equiv(B) ⦄ (_▫_ : A₁ → A₂ → B) ⦃ inst : BinaryOperator(_▫_) ⦄  where
    [≡]-congruence2-left : (x : _) → Function(_▫ x)
    [≡]-congruence2-left _ = BinaryOperator.left {_}{_}{_} {_▫_} (inst)

    [≡]-congruence2-right : (x : _) → Function(x ▫_)
    [≡]-congruence2-right _ = BinaryOperator.right {_}{_}{_} {_▫_} (inst)

    [≡]-with2 : ∀{x₁ y₁ : A₁} → (x₁ ≡ y₁) → ∀{x₂ y₂ : A₂} → (x₂ ≡ y₂) → (x₁ ▫ x₂ ≡ y₁ ▫ y₂)
    [≡]-with2 = BinaryOperator.congruence{_▫_ = _▫_} (inst)

    [≡]-with2ₗ : (a : A₂) → ∀{x y : A₁} → (x ≡ y) → (x ▫ a ≡ y ▫ a)
    [≡]-with2ₗ a = Function.congruence{f = _▫ a} ([≡]-congruence2-left(a))

    [≡]-with2ᵣ : (a : A₁) → ∀{x y : A₂} → (x ≡ y) → (a ▫ x ≡ a ▫ y)
    [≡]-with2ᵣ a = Function.congruence{f = a ▫_} ([≡]-congruence2-right(a))

-- The unary relator `P` "(behaves like)/is a relator" in the context of `_≡_` from the Equiv instance.
module _ {ℓₒ₁}{ℓₒ₂} {A : Set(ℓₒ₁)} ⦃ _ : Equiv(A) ⦄ (P : A → Set(ℓₒ₂)) where
  record UnaryRelator : Set(ℓₒ₁ Lvl.⊔ ℓₒ₂) where
    constructor intro
    field
      substitution : ∀{x y : A} → (x ≡ y) → P(x) → P(y)
  substitute₁ = inst-fn UnaryRelator.substitution

-- The binary relator `_▫_` "(behaves like)/is a relator" in the context of `_≡_` from the Equiv instance.
module _ {ℓₒ₁}{ℓₒ₂}{ℓₒ₃} {A : Set(ℓₒ₁)} ⦃ _ : Equiv(A) ⦄ {B : Set(ℓₒ₂)} ⦃ _ : Equiv(B) ⦄ (_▫_ : A → B → Set(ℓₒ₃)) where
  record BinaryRelator : Set(ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃) where
    constructor intro

    field
      substitution : ∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₁ ▫ x₂) → (y₁ ▫ y₂)
  substitute₂ = inst-fn BinaryRelator.substitution
