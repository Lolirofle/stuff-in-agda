module _ where
  private variable i i₁ i₂ : I
  private variable A B : Obj(i)

  -- A relation allowing "application" and "abstraction" of some kind.
  -- Note: This definition has some similarities to invertible Hom-functors of indexed categories, but the structure is only the signature of a category.
  record FunctionLike : Typeω where -- {ℓₒₗ Lvl.⊔ ℓₒᵣ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑₘ Lvl.⊔ Lvl.𝐒(ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ ℓₑ)}
    constructor intro
    field
      convert : (A ⟶ B) ↔ (type(A) → type(B))
      ⦃ convertₗ-func ⦄ : Function(convert{A = A}{B = B} $ₗ_)
      ⦃ convertᵣ-func ⦄ : Function(convert{A = A}{B = B} $ᵣ_)
      ⦃ correctness ⦄ : InversePair ⦃ morphism-equiv{i₁}{i₂}{A}{B} ⦄ ⦃ [⊜]-equiv ⦄ convert

    -- Function application.
    _$_ : (A ⟶ B) → (type(A) → type(B))
    _$_ = convert $ᵣ_

    -- Function abstraction.
    abstr : (type(A) → type(B)) → (A ⟶ B)
    abstr = convert $ₗ_

open FunctionLike ⦃ … ⦄ using (_$_ ; abstr) public

-- A relation isomorphic to the function type, allowing "application" and "abstraction".
FunctionType : ∀{ℓₘ : Lvl.Level → Lvl.Level → Lvl.Level} → (∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓₘ ℓ₁ ℓ₂}) → Typeω
FunctionType(_⟶_) = FunctionLike(\ℓ → Type{ℓ}) (_⟶_) Fn.id



open import Function
open import Function.Proofs
open import Structure.Relator.Properties
-- open import Relator.Equals.Proofs.Equiv

module _ {ℓₜ : Lvl.Level → Lvl.Level} ⦃ type-equiv : ∀{ℓ}{T : Type{ℓ}} → Equiv{ℓₜ(ℓ)}(T) ⦄ {ℓₘ : Lvl.Level → Lvl.Level → Lvl.Level} where
  module _ ⦃ function-equiv : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → Equiv{ℓₘ ℓ₁ ℓ₂}(A →ᶠ B) ⦄ where
    instance
      explicit-functionType : FunctionType(_→ᶠ_)
      explicit-functionType = intro
        ⦃ function-equiv ⦄
        (intro Fn.id (Fn._$_))
        ⦃ correctness = intro
          ⦃ left = intro(reflexivity(_≡_)) ⦄
          ⦃ right = intro(reflexivity(_≡_)) ⦄
        ⦄

  open import Functional.Implicit as Implicit
  module _ ⦃ function-equiv : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → Equiv{ℓₘ ℓ₁ ℓ₂}(A ﹛→﹜ B) ⦄ where
    instance
      implicit-functionType : FunctionType(_﹛→﹜_)
      implicit-functionType = intro (intro Implicit.inferArg (_﹛$﹜_))
        ⦃ intro \p → {!_⊜_.proof p!} ⦄
        ⦃ intro \p → Dependent.intro {!p!} ⦄
        ⦃ correctness = intro
          ⦃ left = intro(reflexivity(_≡_)) ⦄
          ⦃ right = intro(reflexivity(_≡_) ⦃ Equiv.reflexivity function-equiv ⦄) ⦄
        ⦄

  open import Functional.Instance as Instance
  module _ ⦃ function-equiv : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → Equiv{ℓₘ ℓ₁ ℓ₂}(A ⦃→⦄ B) ⦄ where
    instance
      instance-functionType : FunctionType(_⦃→⦄_)
      instance-functionType = intro (intro Instance.inferArg (_⦃$⦄_))
        ⦃ {!!} ⦄
        ⦃ {!!} ⦄
        ⦃ correctness = intro
          ⦃ left = intro(reflexivity(_≡_)) ⦄
          ⦃ right = intro(reflexivity(_≡_) ⦃ Equiv.reflexivity function-equiv ⦄) ⦄
        ⦄
