module Numeral.Finite.Decidable.Quantifiers where

open import Data
open import Data.Boolean
open import Data.Boolean.Stmt.Proofs
open import Data.Option
import      Data.Option.Functions as Option
open import Functional
open import Lang.Inspect
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.LinearSearch
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs
open import Type

private variable ℓ : Lvl.Level
private variable A B : Type{ℓ}
private variable N : ℕ
private variable P : 𝕟(N) → Type
private variable f : 𝕟(N) → Bool

satisfiesAll : (𝕟(N) → Bool) → Bool
satisfiesAll{𝟎}   _ = 𝑇
satisfiesAll{𝐒 N} f with f(𝟎)
... | 𝑇 = satisfiesAll{N} (f ∘ 𝐒)
... | 𝐹 = 𝐹

instance
  [∀]-satisfiesAll-decider : ⦃ dec : Decider(1)(P)(f) ⦄ → Decider(0)(∀{n} → P(n))(satisfiesAll f)
  [∀]-satisfiesAll-decider {𝟎}   {P = P} {f = f} = true \{}
  [∀]-satisfiesAll-decider {𝐒 N} {P = P} {f = f} with f(𝟎) | inspect f(𝟎)
  ... | 𝑇 | intro f0t = [↔]-to-[→]
    (decider-relator
      ([↔]-intro (\p{n} → p{𝐒 n}) \p → \{ {𝟎} → [↔]-to-[←] (decider-true{P = P(𝟎)}) ([↔]-to-[←] IsTrue.is-𝑇 f0t) ; {𝐒 i} → p{i} })
      [≡]-intro
    )
    ([∀]-satisfiesAll-decider {N} {P = P ∘ 𝐒} {f = f ∘ 𝐒})
  ... | 𝐹 | intro f0f = false \p → [↔]-to-[←]
    (decider-false{P = P(𝟎)})
    ([↔]-to-[←] IsFalse.is-𝐹 f0f) (p{𝟎})

instance
  [∃]-findMin-decider : ⦃ dec : Decider(1)(P)(f) ⦄ → Decider(0)(∃ P)(Option.isSome(findMin f))
  [∃]-findMin-decider {𝟎}   {P = P} {f = f} = false \{([∃]-intro())}
  [∃]-findMin-decider {𝐒 N} {P = P} {f = f} with f(𝟎) | inspect f(𝟎)
  ... | 𝑇 | intro f0t = true ([∃]-intro 𝟎 ⦃ [↔]-to-[←] (decider-true{P = P(𝟎)}) ([↔]-to-[←] IsTrue.is-𝑇 f0t) ⦄)
  ... | 𝐹 | intro f0f = [↔]-to-[→]
    (decider-relator
      ([↔]-intro
        (\{([∃]-intro 𝟎 ⦃ p ⦄) → [⊥]-elim ([↔]-to-[←] (decider-false{P = P(𝟎)}) ([↔]-to-[←] IsFalse.is-𝐹 f0f) p) ; ([∃]-intro(𝐒(n))) → [∃]-intro n})
        (\([∃]-intro n) → [∃]-intro(𝐒 n))
      )
      isSome-map
    )
    ([∃]-findMin-decider {N} {P = P ∘ 𝐒} {f = f ∘ 𝐒})
    where
      isSome-map : ∀{f : A → B}{o : Option(A)} → (Option.isSome o ≡ Option.isSome (Option.map f o))
      isSome-map {o = None}   = [≡]-intro
      isSome-map {o = Some _} = [≡]-intro
