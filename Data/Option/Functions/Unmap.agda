module Data.Option.Functions.Unmap where

import      Lvl
open import Data.Option
open import Data.Option.Equiv as Option
open import Lang.Inspect
open import Logic.Propositional
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ₁ ℓₑ₂ ℓₑₒ₁ ℓₑₒ₂ : Lvl.Level
private variable T A B : Type{ℓ}

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-optA : Equiv{ℓₑₒ₁}(Option(A)) ⦄
  ⦃ ext-A : Extensionality equiv-optA ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-optB : Equiv{ℓₑₒ₂}(Option(B)) ⦄
  ⦃ ext-B : Extensionality equiv-optB ⦄
  where

  module _ (f : Option(A) → Option(B)) ⦃ inj-f : Injective(f) ⦄ where
    private
      invalid-case : ∀{a} → (f(Some a) ≡ None) → (f(None) ≡ None) → ⊥
      invalid-case a-none none-none = Option.cases-inequality (injective(f) (transitivity(_≡_) none-none (symmetry(_≡_) a-none)))

    unmap : (A → B)
    unmap a with f(Some a) | inspect f(Some a)
    ... | Some b | _ = b
    ... | None   | intro a-none with f(None) | inspect f(None)
    ...   | None   | intro none-none with () ← invalid-case a-none none-none
    ...   | Some b | _ = b

    module _
      {ℓ}
      (P : A → B → Type{ℓ})
      (ps : ∀{a b} → (f(Some a) ≡ Some b) → P a b)
      (pn : ∀{a b} → (f(Some a) ≡ None) → (f(None) ≡ Some b) → P a b)
      where

      unmap-intro : ∀{a} → P a (unmap(a))
      unmap-intro {a} with f(Some a) | inspect f(Some a)
      ... | Some b | intro a-some = ps a-some
      ... | None   | intro a-none with f(None) | inspect f(None)
      ...   | None   | intro none-none with () ← invalid-case a-none none-none
      ...   | Some b | intro none-some = pn a-none (reflexivity(_≡_))
