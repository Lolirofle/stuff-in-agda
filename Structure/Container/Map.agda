module Structure.Container.Map where

import      Lvl
open import Structure.Operator
open import Structure.Setoid
open import Type

module _
  {ℓₘ ℓₖ ℓᵥ ℓₑₘ ℓₑₖ ℓₑᵥ}
  (Map : Type{ℓₘ})
  (Key : Type{ℓₖ})
  (Value : Type{ℓᵥ})
  ⦃ equiv-Map : Equiv{ℓₑₘ}(Map) ⦄
  ⦃ equiv-Key : Equiv{ℓₑₖ}(Key) ⦄
  ⦃ equiv-Value : Equiv{ℓₑᵥ}(Value) ⦄
  where

  record Mapping : Type{ℓᵥ Lvl.⊔ ℓₘ Lvl.⊔ ℓₖ Lvl.⊔ ℓₑₘ Lvl.⊔ ℓₑₖ Lvl.⊔ ℓₑᵥ} where
    field
      get : Key → Map → Value

    field
      map-extensionality : ∀{m₁ m₂} → (∀{k} → (get k m₁ ≡ get k m₂)) → (m₁ ≡ m₂)
      ⦃ get-function ⦄ : BinaryOperator(get)

  record Settable ⦃ M : Mapping ⦄ : Type{ℓᵥ Lvl.⊔ ℓₘ Lvl.⊔ ℓₖ Lvl.⊔ ℓₑₘ Lvl.⊔ ℓₑₖ Lvl.⊔ ℓₑᵥ} where
    open Mapping(M)
    field
      set : Key → Value → Map → Map

    field
      ⦃ set-function ⦄ : TrinaryOperator(set)

      get-set-identity : ∀{k}{v}{m} → (get k (set k v m) ≡ v)
      set-duplicate    : ∀{k}{v₁ v₂}{m} → (set k v₁ (set k v₂ m) ≡ set k v₁ m)

      get-set-constant : ∀{k₁ k₂}{v}{m} → (k₁ ≢ k₂) → (get k₁ (set k₂ v m) ≡ get k₁ m)
      set-swap         : ∀{k₁ k₂}{v₁ v₂}{m} → (k₁ ≢ k₂) → (set k₁ v₁ (set k₂ v₂ m) ≡ set k₂ v₂ (set k₁ v₁ m))

{-
private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B : Type{ℓ}

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ ⦃ equiv-AB : Equiv{ℓₑ}(A → B) ⦄ where
  instance
    function-mapping : Mapping(A → B) A B
    Mapping.get                function-mapping x f = f(x)
    Mapping.map-extensionality function-mapping = {!!}
    Mapping.get-function       function-mapping = {!!}
-}
