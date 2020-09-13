module Numeral.Finite.Oper.Comparisons.Proofs where

import      Lvl
open import Data
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Sign
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Syntax.Number

⋚-of-𝟎-not-+ : ∀{an bn}{b : 𝕟(bn)} → ⦃ _ : 𝟎 {an} ⋚? b ≡ ➕ ⦄ → ⊥
⋚-of-𝟎-not-+ {b = 𝟎}    ⦃ ⦄
⋚-of-𝟎-not-+ {b = 𝐒(_)} ⦃ ⦄

⋚-of-𝟎-not-− : ∀{an bn}{a : 𝕟(an)} → ⦃ _ : a ⋚? 𝟎 {bn} ≡ ➖ ⦄ → ⊥
⋚-of-𝟎-not-− {a = 𝟎}    ⦃ ⦄
⋚-of-𝟎-not-− {a = 𝐒(_)} ⦃ ⦄

⋚-of-𝐒𝟎-not-𝟎 : ∀{an bn}{a : 𝕟(an)} → ⦃ _ : 𝐒(a) ⋚? 𝟎 {bn} ≡ 𝟎 ⦄ → ⊥
⋚-of-𝐒𝟎-not-𝟎 {a = 𝟎}    ⦃ ⦄
⋚-of-𝐒𝟎-not-𝟎 {a = 𝐒(_)} ⦃ ⦄

⋚-of-𝟎𝐒-not-𝟎 : ∀{an bn}{b : 𝕟(bn)} → ⦃ _ : 𝟎 {an} ⋚? 𝐒(b) ≡ 𝟎 ⦄ → ⊥
⋚-of-𝟎𝐒-not-𝟎 {b = 𝟎}    ⦃ ⦄
⋚-of-𝟎𝐒-not-𝟎 {b = 𝐒(_)} ⦃ ⦄

⋚-surjective : ∀{an bn}{a : 𝕟(an)}{b : 𝕟(bn)} → ∃{Obj = (−|0|+)} (a ⋚? b ≡_)
⋚-surjective {a = 𝟎}   {𝟎}   = [∃]-intro 𝟎
⋚-surjective {a = 𝟎}   {𝐒 b} = [∃]-intro ➖
⋚-surjective {a = 𝐒 a} {𝟎}   = [∃]-intro ➕
⋚-surjective {a = 𝐒 a} {𝐒 b} = ⋚-surjective {a = a} {b}

⋚-to-< : ∀{an bn}{a : 𝕟(an)}{b : 𝕟(bn)} → ⦃ _ : a ⋚? b ≡ ➕ ⦄ → (a >? b ≡ 𝑇)
⋚-to-< {a = 𝐒 a} {𝟎} = [≡]-intro
⋚-to-< {a = 𝐒 a} {𝐒 b} = ⋚-to-< {a = a} {b}

⋚-to-> : ∀{an bn}{a : 𝕟(an)}{b : 𝕟(bn)} → ⦃ _ : a ⋚? b ≡ ➖ ⦄ → (a <? b ≡ 𝑇)
⋚-to-> {a = 𝟎}   {𝐒 b} = [≡]-intro
⋚-to-> {a = 𝐒 a} {𝐒 b} = ⋚-to-> {a = a} {b}

⋚-to-≡ : ∀{an bn}{a : 𝕟(an)}{b : 𝕟(bn)} → ⦃ _ : a ⋚? b ≡ 𝟎 ⦄ → (a ≡? b ≡ 𝑇)
⋚-to-≡ {a = 𝟎}   {𝟎}   = [≡]-intro
⋚-to-≡ {a = 𝐒 a} {𝐒 b} = ⋚-to-≡ {a = a} {b}

instance
  [≡?]-commutativity : ∀{n} → Commutativity{T₁ = 𝕟(n)} ⦃ [≡]-equiv ⦄ (_≡?_)
  [≡?]-commutativity{n} = intro(\{x y} → p{n}{x}{y}) where
    p : ∀{n} → Names.Commutativity{T₁ = 𝕟(n)} ⦃ [≡]-equiv ⦄ (_≡?_)
    p{x = 𝟎}  {y = 𝟎}   = [≡]-intro
    p{x = 𝟎}  {y = 𝐒 y} = [≡]-intro
    p{x = 𝐒 x}{y = 𝟎}   = [≡]-intro
    p{x = 𝐒 x}{y = 𝐒 y} = p {x = x}{y = y}
