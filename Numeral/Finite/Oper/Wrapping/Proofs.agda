module Numeral.Finite.Oper.Wrapping.Proofs where

open import Data
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Proofs
import      Numeral.Natural.Relation as ℕ
import      Numeral.Natural.Relation.Order as ℕ
import      Numeral.Natural.Relation.Order.Proofs as ℕ
open import Numeral.Finite as 𝕟
open import Numeral.Finite.Bound
open import Numeral.Finite.Bound.Proofs
open import Numeral.Finite.Oper using (module Exact)
open import Numeral.Finite.Oper.Wrapping renaming (𝐒 to [𝐒] ; 𝐏 to [𝐏])
open import Numeral.Finite.Proofs
open import Numeral.Finite.Recursion
open import Numeral.Finite.Relation.Order
open import Numeral.Finite.Relation.Order.Proofs
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type.Identity
open import Type.Identity.Proofs

private variable b₁ b₂ N : ℕ
private variable n x y z x₁ x₂ y₁ y₂ : 𝕟(N)

-- Alternative implementation: [−]-operator-raw {x₁ = x}{x₂ = y}{y₁ = 𝐒(𝟎 {𝟎})}{y₂ = 𝐒(𝟎 {𝟎})} pb xy (reflexivity(_≡_) {𝐒(𝟎 {𝟎})})
[𝐏]-function-raw : ((x ≡ 𝟎 {bound(x)}) → (y ≡ 𝟎 {bound(y)}) → Id(bound x) (bound y)) → (x ≡ y) → ([𝐏] x ≡ [𝐏] y)
[𝐏]-function-raw {x = 𝟎}   {y = 𝟎}   pb xy = maximum-function (pb <> <>)
[𝐏]-function-raw {x = 𝐒 x} {y = 𝐒 y} pb xy = bound-𝐒-function{n₁ = x}{n₂ = y} xy

-- Alternative implementation: 
--   [−]-operator-raw {x₁ = 𝟎}   {x₂ = 𝟎}   {y₁ = 𝟎}   {y₂ = 𝟎}    pb px py = <>
--   [−]-operator-raw {x₁ = 𝐒 x₁}{x₂ = 𝐒 x₂}{y₁ = 𝟎}   {y₂ = 𝟎}    pb px py = px
--   [−]-operator-raw {x₁ = 𝟎}   {x₂ = 𝟎}   {y₁ = 𝐒 y₁}{y₂ = 𝐒 y₂} pb px py = [−]-operator-raw {x₁ = maximum}{x₂ = maximum}{y₁ = y₁}{y₂ = y₂} pb (maximum-function pb) py
--   [−]-operator-raw {x₁ = 𝐒 x₁}{x₂ = 𝐒 x₂}{y₁ = 𝐒 y₁}{y₂ = 𝐒 y₂} pb px py = [−]-operator-raw {x₁ = bound-𝐒 x₁} {x₂ = bound-𝐒 x₂} {y₁ = y₁} {y₂ = y₂} pb (bound-𝐒-function{n₁ = x₁}{n₂ = x₂} px) py
[−]-operator-raw : Id(bound x₁) (bound x₂) → (x₁ ≡ x₂) → (y₁ ≡ y₂) → (x₁ [−] y₁ ≡ x₂ [−] y₂)
[−]-operator-raw                    {y₁ = 𝟎}   {y₂ = 𝟎}    pb px py = px
[−]-operator-raw {x₁ = x₁}{x₂ = x₂} {y₁ = 𝐒 y₁}{y₂ = 𝐒 y₂} pb px py = [−]-operator-raw {y₁ = y₁}{y₂ = y₂} pb ([𝐏]-function-raw {x = x₁}{y = x₂} (\_ _ → pb) px) py

instance
  [−]-identityᵣ : ⦃ pos : ℕ.Positive(b₂) ⦄ → Identityᵣ(_[−]_ {b₁}{b₂})(minimum)
  [−]-identityᵣ{b₂ = 𝐒 _} = intro \{x} → reflexivity(_≡_) {x}

instance
  [+]-identityᵣ : ⦃ pos : ℕ.Positive(b₂) ⦄ → Identityᵣ(_[+]_ {b₁}{b₂})(minimum)
  [+]-identityᵣ {b₂ = 𝐒 _} = intro \{ {𝟎} → <> ; {𝐒(x)} → reflexivity(_≡_) {𝐒(x)} }

{-
module _ where
  open import Numeral.Finite.Equiv2
  open import Syntax.Transitivity.Structure
  open import Type.Dependent.Sigma.Implicit renaming (intro to •_)

  [+exact][−]-inverseOperᵣ : (x Exact.+ y) [−] y ≡ x
  [+exact][−]-inverseOperᵣ {x = x} {y = 𝟎} = {!!}
  [+exact][−]-inverseOperᵣ {x = x} {y = 𝐒 y} = 🝖-begin
    • (x Exact.+ 𝐒(y)) [−] 𝐒(y)    🝖[ _≡*_ ]-[ {!!} ]
    • 𝐒(x Exact.+ y) [−] 𝐒(y)      🝖[ _≡*_ ]-[ {!!} ]
    • bound-𝐒(x Exact.+ y) [−] y   🝖[ _≡*_ ]-[ {!!} ]
    • (bound-𝐒(x) Exact.+ y) [−] y 🝖[ _≡*_ ]-[ {!!} ]
    • bound-𝐒(x)                   🝖[ _≡*_ ]-[ {!!} ]
    • x                            🝖[ _≡*_ ]-end
-}


neg-function-raw : ⦃ pos₁ : ℕ.Positive(b₁) ⦄ → ⦃ pos₂ : ℕ.Positive(b₂) ⦄ → Id b₁ b₂ → (x ≡ y) → (b₁ [ₙ−] x ≡ b₂ [ₙ−] y)
neg-function-raw {𝐒 b₁} {𝐒 b₂} {𝐒 bx} {x} {𝐒 by} {y} ⦃ pos₁ ⦄ ⦃ pos₂ ⦄ pb xy = [−]-operator-raw {x₁ = 𝟎}{x₂ = 𝟎}{y₁ = x}{y₂ = y} pb <> xy

[−]-function-raw : Id(bound x) (bound y) → (x ≡ y) → ([−] x ≡ [−] y)
[−]-function-raw {𝐒 b₁} {x} {𝐒 b₂} {y} = neg-function-raw{x = x}{y = y}

[+]-operator-raw : Id(bound x₁) (bound x₂) → (x₁ ≡ x₂) → (y₁ ≡ y₂) → (x₁ [+] y₁ ≡ x₂ [+] y₂)
[+]-operator-raw {𝐒 _}{x₁ = x₁} {𝐒 _}{x₂ = x₂} {y₁ = y₁} {y₂ = y₂} pb px py = [−]-operator-raw {x₁ = x₁} {x₂ = x₂} {y₁ = bound(x₁) [ₙ−] y₁} {y₂ = bound(x₂) [ₙ−] y₂} pb px (neg-function-raw {x = y₁}{y = y₂} pb py)

neg-of-minimum : ⦃ pos-N : ℕ.Positive(N) ⦄ → ⦃ pos-b₁ : ℕ.Positive(b₁) ⦄ → ⦃ pos-b₂ : ℕ.Positive(b₂) ⦄ → (N [ₙ−] minimum{b₁} ≡ minimum{b₂})
neg-of-minimum {𝐒 N} {𝐒 b₁} {𝐒 b₂} = <>

{-
module _ where
  open import Numeral.Finite.Equiv2
  open import Syntax.Transitivity.Structure
  open import Type.Dependent.Sigma.Implicit renaming (intro to •_)
  open import Logic.Propositional
  [−]ᵣ-involution : x [−] (x [−] y) ≡ y
  [−]ᵣ-involution{x = x}{y = y} = 𝕟-strong-recursion₂(P) p x y where
    P = \{X}{Y} (x : 𝕟(X)) (y : 𝕟(Y)) → x [−] (x [−] y) ≡ y
    p : ∀{X Y} → (x : 𝕟(X)) → (y : 𝕟(Y)) → (∀{I J} → (i : 𝕟(I)) → (j : 𝕟(J)) → (i < x) ∨ ((i ≤ x) ∧ (j < y)) → P i j) → P x y
    p 𝟎 𝟎 rec = <>
    p {𝐒 X}{𝐒 Y} 𝟎 (𝐒 y) rec = 🝖-begin
      • 𝟎 [−] (𝟎 [−] 𝐒(y))    🝖[ _≡*_ ]-[ [≡]-reflexivity-raw ]
      • 𝟎 [−] (maximum [−] y) 🝖[ _≡*_ ]-[ {!!} ] -- TODO: Maybe split into cases. When X divides Y or not?
      • 𝐒(y) 🝖-end
    p (𝐒 x) 𝟎 rec = {!!}
    p (𝐒 x) (𝐒 y) rec = {!!}
{-[−]ᵣ-involution {x = 𝟎} {y = 𝟎} = <>
[−]ᵣ-involution {x = 𝟎} {y = 𝐒 y} = {!!}
[−]ᵣ-involution {𝐒(𝐒 _)}{x = 𝐒 x} {y = 𝟎} = {![≡]-transitivity-raw {a = bound-𝐒 x}{b = x}{c = 𝟎} ? ([−]-self {bound x}{x = x})!}
[−]ᵣ-involution {x = 𝐒 x} {y = 𝐒 y} = {![−]ᵣ-involution {x = x} {y = y}!}
-}
-}

module _ where
  open import Numeral.Finite.Equiv2
  open import Syntax.Transitivity.Structure
  open import Type.Dependent.Sigma.Implicit renaming (intro to •_)
  open import Logic.Propositional

  [−]-self : ⦃ pos : ℕ.Positive(N) ⦄ → (x [−] x ≡ minimum{N})
  [−]-self {N = 𝐒 N}{x = x} = 𝕟-strong-recursion(\x → (x [−] x ≡ minimum{𝐒 N})) p x where
    p : ∀{N} → (x : 𝕟(N)) → ({I : ℕ} (i : 𝕟 I) → (i < x) → (i [−] i ≡ minimum)) → (x [−] x ≡ minimum)
    p(𝟎)    prev = <>
    p(𝐒(x)) prev = 🝖-begin
      • 𝐒(x) [−] 𝐒(x)             🝖-[]
      • bound-𝐒(x) [−] x          🝖-[ [−]-operator-raw {y₁ = bound-𝐒(x)}{y₂ = x} intro (reflexivity(_≡_) {bound-𝐒(x)}) ((bound-𝐒-identity {n = x})) ]-sym
      • bound-𝐒(x) [−] bound-𝐒(x) 🝖-[ prev(bound-𝐒(x)) ([<][≡]-subtransitivityₗ-raw {a = bound-𝐒(x)}{b = x}{c = 𝐒(x)} (bound-𝐒-identity {n = x}) ([<]-of-successor {a = x})) ]
      • 𝟎                         🝖-end

  [𝐒]-of-maximum : ⦃ pos-b₁ : ℕ.Positive(b₁) ⦄ → ⦃ pos-b₂ : ℕ.Positive(b₂) ⦄ → ([𝐒](maximum{b₁}) ≡ minimum{b₂})
  [𝐒]-of-maximum {b₁}{b₂} = [−]-self {N = b₂}{x = maximum{b₁}}

  {-
  open import Functional
  open import Type
  module _
    {ℓ}
    (T : ∀{n} → 𝕟(n) → Type{ℓ})
    (base : ∀{N} → ⦃ pos : ℕ.Positive(N) ⦄ → T{N}(maximum))
    (step : ∀{N} → (i : 𝕟(N)) → T(𝐒(i)) → T(i))
    where

    𝕟-flip-elim : ∀{N} → (n : 𝕟(N)) → T(n)
    𝕟-flip-elim{𝐒 N} n = {!𝕟-elim(T ∘ flip) ? ? !}

  [−][exact+]-inverse : (x Exact.+ y) [−] x ≡ y
  [−][exact+]-inverse {x = x} {y = 𝟎} = {!x Exact.+ 𝟎!}
  [−][exact+]-inverse {x = x} {y = 𝐒 y} = {!!}

  [𝐒]-bound-𝐒-is-𝐒 : [𝐒] (bound-𝐒(x)) ≡ 𝐒(x)
  [𝐒]-bound-𝐒-is-𝐒 {𝐒 X} {𝟎} = {![𝐒] (bound-𝐒 𝟎) ≡ 𝐒 𝟎!}
  [𝐒]-bound-𝐒-is-𝐒 {𝐒 (𝐒 X)} {𝐒 x} = {!!}

  [𝐏][𝐒]-inverse : [𝐏] ([𝐒] x) ≡ x
  [𝐏][𝐒]-inverse {𝐒 𝟎} {𝟎} = <>
  [𝐏][𝐒]-inverse {𝐒 (𝐒 X)} {𝟎} = {!!}
  [𝐏][𝐒]-inverse {𝐒 (𝐒 X)} {𝐒 x} = {!!}
  {-[𝐏][𝐒]-inverse {x = 𝟎 {𝟎}} = <>
  [𝐏][𝐒]-inverse {x = 𝟎 {𝐒 n}} = {![𝐏][𝐒]-inverse {x = 𝟎 {n}}!}
  [𝐏][𝐒]-inverse {x = 𝐒 x} = {!!}-}

  [𝐒][𝐏]-inverse : [𝐒] ([𝐏] x) ≡ x
  [𝐒][𝐏]-inverse {X}{𝟎}   = [𝐒]-of-maximum {X}
  [𝐒][𝐏]-inverse {X}{𝐒 x} = 🝖-begin
      • [𝐒] (bound-𝐒(x))            🝖-[ {![𝐒][𝐏]-inverse {x = bound-𝐒 x}!} ]
      • [𝐒] ([𝐒] ([𝐏] (bound-𝐒 x))) 🝖-[ {![𝐒][𝐏]-inverse {x = bound-𝐒 x}!} ]
      • 𝐒(bound-𝐒(x))               🝖-[ {![𝐒] (bound-𝐒(x))!} ]
      • 𝐒(x)                        🝖-end

  [𝐏]-injective-raw : ((x ≢ y) → Id(bound x) (bound y)) → ([𝐏] x ≡ [𝐏] y) → (x ≡ y)
  [𝐏]-injective-raw {x = 𝟎}   {y = 𝟎}   pb xy = <>
  [𝐏]-injective-raw {x = 𝟎 {X}} {y = 𝐒 {𝐒 Y} y} pb xy = {!!}
  [𝐏]-injective-raw {x = 𝐒 x} {y = 𝟎}   pb xy = {!!}
  -- [𝐏]-injective-raw {x = 𝟎}   {y = 𝐒 y} pb xy with () ← ℕ.[<]-to-[≢] (bound-𝐒-is-maximum-condition{n = y} ([≡]-symmetry-raw {b = bound-𝐒(y)} xy)) (injective ⦃ _ ⦄ ⦃ _ ⦄ (ℕ.𝐒) (pb <>))
  -- [𝐏]-injective-raw {x = 𝐒 x} {y = 𝟎}   pb xy with () ← ℕ.[<]-to-[≢] (bound-𝐒-is-maximum-condition{n = x} xy) (injective ⦃ _ ⦄ ⦃ _ ⦄ (ℕ.𝐒) (symmetry(Id) (pb <>)))
  [𝐏]-injective-raw {x = 𝐒 x} {y = 𝐒 y} pb xy = bound-𝐒-injective{n₁ = x}{n₂ = y} xy

  [−]-step-alternative : x [−] 𝕟.𝐒(y) ≡ [𝐏](x [−] y)
  [−]-step-alternative {x = x}   {y = 𝟎} = reflexivity(_≡_) {[𝐏] x}
  [−]-step-alternative {x = 𝟎}   {y = 𝐒 y} = [−]-step-alternative {x = maximum} {y = y}
  [−]-step-alternative {x = 𝐒 x} {y = 𝐒 y} = {![−]-step-alternative {x = bound-𝐒 x} {y = 𝐒 y}!}
  -}

  [−]ᵣ-of-𝐒 : x [−] 𝐒(y) ≡ [𝐏](x [−] y)
  [−]ᵣ-of-𝐒 {x = 𝟎 {X}} {y = 𝟎}   = reflexivity(_≡_) {maximum{𝐒(X)}}
  [−]ᵣ-of-𝐒 {x = 𝐒 x}   {y = 𝟎}   = reflexivity(_≡_) {bound-𝐒(x)}
  [−]ᵣ-of-𝐒 {x = 𝟎 {X}} {y = 𝐒 y} = [−]ᵣ-of-𝐒 {x = maximum{𝐒(X)}}{y = y}
  [−]ᵣ-of-𝐒 {x = 𝐒 x}   {y = 𝐒 y} = [−]ᵣ-of-𝐒 {x = bound-𝐒(x)}{y = y}

  [−]-associate-commute : (x [−] y) [−] z ≡ (x [−] z) [−] y
  [−]-associate-commute-𝐒 : (x [−] y) [−] 𝐒(z) ≡ (x [−] z) [−] 𝐒(y)
  [−]-associate-commute {x = x}    {y = 𝟎}   {z = z}   = reflexivity(_≡_) {x [−] z}
  [−]-associate-commute {x = x}    {y = 𝐒 y} {z = 𝟎}   = reflexivity(_≡_) {x [−] 𝐒(y)}
  [−]-associate-commute {x = 𝟎 {X}}{y = 𝐒 y} {z = 𝐒 z} = [−]-associate-commute-𝐒 {x = maximum{𝐒(X)}}{y = y}{z = z}
  [−]-associate-commute {x = 𝐒 x}  {y = 𝐒 y} {z = 𝐒 z} = [−]-associate-commute-𝐒 {x = bound-𝐒(x)}{y = y}{z = z}
  [−]-associate-commute-𝐒 {x = x}{y = y}{z = z} = 🝖-begin
    • (x [−] y) [−] 𝐒(z)    🝖[ _≡*_ ]-[ [−]ᵣ-of-𝐒 {x = x [−] y}{y = z} ]
    • [𝐏] ((x [−] y) [−] z) 🝖[ _≡*_ ]-[ [𝐏]-function-raw {x = (x [−] y) [−] z}{y = (x [−] z) [−] y} (\_ _ → intro) ([−]-associate-commute {x = x} {y = y} {z = z}) ]
    • [𝐏] ((x [−] z) [−] y) 🝖[ _≡*_ ]-[ [−]ᵣ-of-𝐒 {x = x [−] z}{y = y} ]-sym
    • (x [−] z) [−] 𝐒(y)    🝖-end

  [+]ₗ-of-𝐒 : [𝐒](x) [+] y ≡ [𝐒](x [+] y)
  [+]ₗ-of-𝐒 {X@(𝐒 _)}{x}{Y@(𝐒 _)}{y} = [−]-associate-commute {x = x}{y = maximum{X}}{z = 𝟎 [−] y}

  {-
  [+]-of-𝐒' : x [+] 𝐒(y) ≡ [𝐒](x) [+] y
  [+]-of-𝐒' {X}{x = 𝟎}   {y = 𝟎} = reflexivity(_≡_) {𝟎 [−] maximum{X}}
  [+]-of-𝐒' {X}{x = 𝐒 x} {y = 𝟎} = reflexivity(_≡_) {𝐒(x) [−] maximum{X}}
  [+]-of-𝐒' {x = 𝟎} {y = 𝐒 y} = {!(𝟎 [+] 𝐒 (𝐒 y)) ≡ ([𝐒] 𝟎 [+] 𝐒 y)!}
  [+]-of-𝐒' {x = 𝐒 x} {y = 𝐒 y} = {!maximum{𝐒(𝐒(bound x))}!}

  [+]ᵣ-of-𝐒 : x [+] 𝐒(y) ≡ [𝐒](x [+] y)
  [+]ᵣ-of-𝐒 {𝐒(X)}{x}{𝐒(Y)}{𝐒(y)} = 🝖-begin
    • x [+] 𝐒(𝐒(y))                                      🝖[ _≡*_ ]-[]
    • x [−] (minimum{𝐒(X)} [−] 𝐒(𝐒(y)))                  🝖[ _≡*_ ]-[]
    • x [−] (maximum{𝐒(X)} [−] 𝐒(y))                     🝖[ _≡*_ ]-[ {!!} ]
    • x [−] [𝐏] (maximum{𝐒(X)} [−] y)                    🝖[ _≡*_ ]-[ {!!} ]

    • (x [−] (maximum{𝐒(X)} [−] y)) [−] maximum{𝐒(X)}    🝖[ _≡*_ ]-[]
    • (x [−] (minimum{𝐒(X)} [−] 𝐒(y))) [−] maximum{𝐒(X)} 🝖[ _≡*_ ]-[]
    • [𝐒] (x [+] 𝐒(y))                       🝖-end
  {-[+]ᵣ-of-𝐒 {𝐒(X)}{x}{𝐒(Y)}{y} = 🝖-begin
    • x [+] 𝐒(y)                                      🝖[ _≡*_ ]-[]
    • x [−] (minimum{𝐒(X)} [−] 𝐒(y))                  🝖[ _≡*_ ]-[ [−]-operator-raw {y₁ = minimum{𝐒(X)} [−] 𝐒(y)}{y₂ = [𝐏] (minimum{𝐒(X)} [−] y)} intro ([≡]-reflexivity-raw {a = x}) ([−]ᵣ-of-𝐒 {x = 𝟎}{y = y}) ]
    • x [−] [𝐏] (minimum{𝐒(X)} [−] y)                 🝖[ _≡*_ ]-[]
    • (x [−] ((minimum{𝐒(X)} [−] y) [−] 𝕟.𝟏 {ℕ.𝟎}))   🝖[ _≡*_ ]-[ {!!} ]
    • (x [−] (minimum{𝐒(X)} [−] y)) [−] maximum{𝐒(X)} 🝖[ _≡*_ ]-[]
    • [𝐒] (x [+] y)                       🝖-end-}
  -- [+]ᵣ-of-𝐒 {𝐒 X} {x}   {𝐒 Y} {𝟎} = reflexivity(_≡_) {x [−] maximum{𝐒(X)}}
  -- [+]ᵣ-of-𝐒 {𝐒 X} {x}   {𝐒 Y} {𝐒 y} = {!x [+] 𝐒 (𝐒 y)!}
  -- [+]ᵣ-of-𝐒 {𝐒 X} {𝐒 x} {𝐒 Y} {𝐒 y} = {!([𝐒] x) [+] 𝐒 y!}

  [−][+]-semiassociativity : Id (bound(x)) (bound(y)) → ((x [−] y) [+] z ≡ x [−] (y [−] z))
  [−][+]-semiassociativity {x = x}{y = y}{z = 𝟎} _ = identityᵣ(_[+]_)(𝟎 {bound(y)}) {x [−] y}
  [−][+]-semiassociativity {X}{x = x}{𝐒 Y}{y = y@𝟎}{Z}{z = 𝐒 z} intro = 🝖-begin
    • x [+] 𝐒(z)                  🝖[ _≡*_ ]-[ {!!} ]
    • [𝐒](x) [+] z                🝖[ _≡*_ ]-[]
    • (x [−] maximum{𝐒(Y)}) [+] z 🝖[ _≡*_ ]-[ [−][+]-semiassociativity {x = x}{y = maximum{𝐒(Y)}}{z = z} intro ]
    • x [−] (maximum{𝐒(Y)} [−] z) 🝖-end
  [−][+]-semiassociativity {x = x}{y = 𝐒 y}{z = 𝐒 z} pb = 🝖-begin
    • (x [−] 𝐒(y)) [+] 𝐒(z)    🝖[ _≡*_ ]-[ {!!} ]
    • (x [−] bound-𝐒(y)) [+] z 🝖[ _≡*_ ]-[ [−][+]-semiassociativity {x = x}{y = bound-𝐒(y)}{z = z} pb ]
    • x [−] (bound-𝐒(y) [−] z) 🝖-end

  [−]ᵣ-involution : x [−] (x [−] y) ≡ y
  [−]ᵣ-involution{x = x}{y = y} = 𝕟-strong-recursion(\y → ∀{X} → (x : 𝕟(X)) → (x [−] (x [−] y) ≡ y)) p y x where
    p : ∀{N} → (y : 𝕟(N)) → ({I : ℕ} (i : 𝕟 I) → (i < y) → ∀{X} → (x : 𝕟(X)) → (x [−] (x [−] i) ≡ i)) → ∀{X} → (x : 𝕟(X)) → (x [−] (x [−] y) ≡ y)
    p(𝟎)    prev x      = [−]-self {x = x}
    p(𝐒(y)) prev 𝟎      = {!!}
    p(𝐒(y)) prev (𝐒(x)) = {!!}

  [+][−]-inverseOperᵣ : (x [+] y) [−] y ≡ x
  [+][−]-inverseOperᵣ {x = 𝟎}  {y = 𝟎}   = <>
  [+][−]-inverseOperᵣ {x = 𝟎}  {y = 𝐒 y} = 🝖-begin
    • (𝟎 [+] 𝐒(y)) [−] 𝐒(y) 🝖[ _≡*_ ]-[ [−]-operator-raw {x₁ = 𝟎 [+] 𝐒(y)}{x₂ = 𝐒(y)} intro {!!} ([≡]-reflexivity-raw {a = 𝐒(y)}) ]
    • 𝐒(y) [−] 𝐒(y)         🝖[ _≡*_ ]-[ [−]-self {x = 𝐒(y)} ]
    • 𝟎                     🝖-end
  [+][−]-inverseOperᵣ {x = 𝐒 x}{y = 𝟎}   = [≡]-reflexivity-raw {a = 𝐒 x}
  [+][−]-inverseOperᵣ {x = 𝐒 x}{y = 𝐒 y} = {![+][−]-inverseOperᵣ {x = x}{y = y}!}
  -}

{-
[−]-stepₗ : 𝐒(x) [−] y ≡ 𝐒(bound-𝐒(x) [−] y)
[−]-stepₗ {x = 𝟎} {y = 𝟎} = <>
[−]-stepₗ {x = 𝟎} {y = 𝐒 𝟎} = {!!}
[−]-stepₗ {x = 𝟎} {y = 𝐒 (𝐒 y)} = [−]-stepₗ {x = maximum} {y = y}
[−]-stepₗ {x = 𝐒 x} {y = 𝟎} = [≡]-symmetry-raw {a = bound-𝐒(𝐒 x)}{b = 𝐒 x} (bound-𝐒-identity{n = 𝐒 x})
[−]-stepₗ {x = 𝐒 x} {y = 𝐒 y} = {!!}
-}

maximum-step : ⦃ pos : ℕ.Positive(N) ⦄ → (maximum{𝐒 N} ≡ 𝐒(maximum{N}))
maximum-step {𝐒 N} = [≡]-reflexivity-raw {a = maximum{𝐒 N}}

[+]-to-𝐒 : x [+] 𝐒(𝟎{𝟎}) ≡ [𝐒](x)
[+]-to-𝐒 {N}{𝟎}   = [≡]-reflexivity-raw {a = minimum{N} [−] maximum{N}}
[+]-to-𝐒 {N}{𝐒 x} = [≡]-reflexivity-raw {a = 𝐒(x)       [−] maximum{N}}

{-
[+exact]-identityₗ : (Exact._+_ {b₁}{b₂} 𝟎 y) ≡ y
[+exact]-identityₗ {b₁} {b₂}   {𝟎}   = <>
[+exact]-identityₗ {b₁} {𝐒 b₂} {𝐒 y} = [+exact]-identityₗ {b₁} {b₂} {y}

open import Numeral.Finite.Equiv2
open import Structure.Relator.Equivalence
open import Syntax.Transitivity.Structure
open import Type.Dependent.Sigma.Implicit renaming (intro to •_)
[+exact][−]-inverseOperᵣ : (x Exact.+₀ y) [−] x ≡ y
[+exact][−]-inverseOperᵣ {𝐒 X} {𝟎} {𝐒 Y} {𝟎} = <>
[+exact][−]-inverseOperᵣ {𝐒 X} {𝟎} {𝐒 (𝐒 Y)} {𝐒 y} = [≡]-transitivity-raw {a = bound-𝐒(𝐒(𝟎 Exact.+ y))}{b = 𝐒(𝟎 Exact.+ y)}{c = 𝐒(y)} (bound-𝐒-identity{n = 𝐒(𝟎 Exact.+ y)}) ([+exact]-identityₗ {y = y})
[+exact][−]-inverseOperᵣ {𝐒 X} {𝐒 x} {𝐒 Y} {𝟎} = 🝖-begin
  • bound-𝐒(𝐒 x Exact.+ 𝟎) [−] 𝐒 x 🝖[ _≡*_ ]-[ {!!} ]
  • bound-𝐒(𝐒 x) [−] 𝐒 x           🝖[ _≡*_ ]-[ {!!} ]
  • 𝟎                              🝖[ _≡*_ ]-end
-- [≡]-transitivity-raw {a = bound-𝐒(𝐒(x) Exact.+ 𝟎) [−] 𝐒(x)}{b = (𝐒(x) Exact.+ 𝟎) [−] 𝐒(x)} {![−]-operator-raw {}!} {!!}
-- [≡]-transitivity-raw {b = 𝐒(x) [−] 𝐒(x)}{c = 𝟎} ([≡]-transitivity-raw {a = bound-𝐒(𝐒(x) Exact.+ 𝟎) [−] 𝐒(x)}{b = (𝐒(x) Exact.+ 𝟎) [−] 𝐒(x)}{c = 𝐒(x) [−] 𝐒(x)} {!!} {!!}) {!!}
-- ([≡]-transitivity-raw {a = bound-𝐒(𝐒(x) Exact.+ 𝟎) [−] 𝐒(x)}{b = (𝐒(x) Exact.+ 𝟎) [−] 𝐒(x)}{c = 𝐒(x) [−] 𝐒(x)})
[+exact][−]-inverseOperᵣ {𝐒 X} {𝐒 x} {𝐒 Y} {𝐒 y} = {!!}

[−]-stepₗ' : 𝐒(x) [−] y ≡ [𝐒] (bound-𝐒(x) [−] y)
[−]-stepₗ' {𝐒 X} {𝟎} {𝐒 Y} {𝟎} = {!!}
[−]-stepₗ' {𝐒 X} {𝟎} {𝐒 .(𝐒 _)} {𝐒 𝟎} = {!!}
[−]-stepₗ' {𝐒 X} {𝟎} {𝐒 .(𝐒 _)} {𝐒 (𝐒 y)} = [−]-stepₗ' {x = maximum} {y = y}
[−]-stepₗ' {𝐒 X} {𝐒 x} {𝐒 Y} {𝟎} = {!!}
[−]-stepₗ' {𝐒 X} {𝐒 x} {𝐒 Y} {𝐒 y} = {!!}
{-[−]-stepₗ' {x = 𝟎} {y = 𝟎} = {!!}
[−]-stepₗ' {x = 𝟎} {y = 𝐒 𝟎} = {!!}
[−]-stepₗ' {x = 𝟎} {y = 𝐒 (𝐒 y)} = [−]-stepₗ' {x = maximum} {y = y}
[−]-stepₗ' {x = 𝐒 x} {y = 𝟎} = {!!}
[−]-stepₗ' {x = 𝐒 x} {y = 𝐒 y} = {!!}
-}

open import Structure.Function
open import Relator.Equals.Proofs.Equiv
𝐒-bound-𝐒-swap : Id (𝐒(bound-𝐒(x))) (bound-𝐒(𝐒(x)))
𝐒-bound-𝐒-swap {x = 𝟎}   = intro
𝐒-bound-𝐒-swap {x = 𝐒 x} = congruence₁(𝐒) (𝐒-bound-𝐒-swap {x = x})

open import Structure.Function
open import Structure.Relator.Properties
instance
  [≡]-Id-sub : ∀{N} → ((_≡_ {N}) ⊆₂ Id)
  _⊆₂_.proof [≡]-Id-sub {𝟎}   {𝟎}   eq = intro
  _⊆₂_.proof [≡]-Id-sub {𝐒 x} {𝐒 y} eq = congruence₁(𝐒) (_⊆₂_.proof [≡]-Id-sub {x}{y} eq)


flip-of-minimum : ∀{N} ⦃ pos : ℕ.Positive(N) ⦄ → Id (flip(minimum{N})) maximum
flip-of-minimum {𝐒 N} = intro

flip-of-maximum : ∀{N} ⦃ pos : ℕ.Positive(N) ⦄ → Id (flip(maximum{N})) minimum
flip-of-maximum ⦃ pos ⦄ = sub₂(_≡_)(Id) ([−]-self {x = maximum ⦃ pos ⦄})
-}




















{-

open import Data
open import Logic.Propositional.Equiv
open import Numeral.Finite.Oper as 𝕟
open import Numeral.Finite.Recursion
import      Numeral.Natural.Relation as ℕ
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator
open import Type
module _
  {ℓ}
  (T : ∀{n} → 𝕟(n) → Type{ℓ})
  (base : ∀{N} → ⦃ pos : ℕ.Positive(N) ⦄ → T{N}(maximum))
  (step : ∀{N} → (i : 𝕟(𝐒(N))) → T(𝐒(i)) → T(i))
  where

  [−]-inverse' : ∀{N}{n : 𝕟(N)} → (n Wrapping.[−] n) ≡ minimum ⦃ 𝕟-to-positive-bound n ⦄
  [−]-inverse' {𝐒 N} {𝟎} = [≡]-intro
  [−]-inverse' {𝐒 N} {𝐒 n} = {!!}

  import      Numeral.Finite.Relation.Order as 𝕟  
  [−]-inverse : ∀{N}{n : 𝕟(N)} → (bound-𝐒(n) Wrapping.[−] n) 𝕟.≡ minimum ⦃ 𝕟-to-positive-bound n ⦄
  [−]-inverse {.(𝐒 _)} {𝟎} = <>
  [−]-inverse {.(𝐒 _)} {𝐒 n} = {![−]-inverse {n = n}!}

  [−]-of-[−] : ∀{A B}{a : 𝕟(A)}{b : 𝕟(B)} → a 𝕟.Wrapping.[−] (a 𝕟.Wrapping.[−] b) 𝕟.≡ b
  [−]-of-[−] {.(𝐒 _)} {.(𝐒 _)} {𝟎} {𝟎} = <>
  [−]-of-[−] {.(𝐒 _)} {.(𝐒 _)} {𝟎} {𝐒 b} = {!!}
  [−]-of-[−] {.(𝐒 _)} {.(𝐒 _)} {𝐒 a} {𝟎} = {!!}
  [−]-of-[−] {.(𝐒 _)} {.(𝐒 _)} {𝐒 a} {𝐒 b} = {!!}

  [−]-function : ∀{A₁ A₂ B₁ B₂}{a₁ : 𝕟(A₁)}{a₂ : 𝕟(A₂)}{b₁ : 𝕟(B₁)}{b₂ : 𝕟(B₂)} → (A₁ ≡ A₂) → (a₁ 𝕟.≡ a₂) → (b₁ 𝕟.≡ b₂) → (a₁ Wrapping.[−] b₁ 𝕟.≡ a₂ Wrapping.[−] b₂)
  [−]-function {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {𝟎} {𝟎} {𝟎} {𝟎} pA pa pb = <>
  [−]-function {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {𝟎} {𝟎} {𝐒 b₁} {𝐒 b₂} pA pa pb = [−]-function {a₁ = maximum}{maximum}{b₁}{b₂} pA {!!} pb
  [−]-function {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {𝐒 a₁} {𝐒 a₂} {𝟎} {𝟎} pA pa pb = pa
  [−]-function {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {𝐒 a₁} {𝐒 a₂} {𝐒 b₁} {𝐒 b₂} pA pa pb = [−]-function {a₁ = bound-𝐒 a₁}{bound-𝐒 a₂}{b₁}{b₂} {!!} {!!} pb

  test : ∀{A₁ A₂ B}{a₁ : 𝕟(A₁)}{a₂ : 𝕟(A₂)}{b : 𝕟(B)} → (a₁ 𝕟.≤ b) → (a₂ 𝕟.≤ b) → (a₁ 𝕟.≡ a₂) → (a₁ Wrapping.[−] b 𝕟.≡ a₂ Wrapping.[−] b)
  test {a₁ = 𝟎} {𝟎} {𝟎} a₁b a₂b a₁a₂ = <>
  test {a₁ = 𝟎} {𝟎} {𝐒 b} a₁b a₂b a₁a₂ = {![−]-function ? ?!}
  test {a₁ = 𝐒 a₁} {𝐒 a₂} {𝐒 b} a₁b a₂b a₁a₂ = test {a₁ = bound-𝐒 a₁} {bound-𝐒 a₂} {b} {!!} {!!} {!!}

  flip-of-𝐒 : ∀{N}{n : 𝕟(N)} → 𝕟.Wrapping.flip(𝐒(n)) 𝕟.≡ 𝕟.Wrapping.𝐏(𝕟.Wrapping.flip(n))
  flip-of-𝐒 {.(𝐒 _)} {𝟎} = {!𝕟.Wrapping.flip(𝐒(𝟎))!}
  flip-of-𝐒 {.(𝐒 _)} {𝐒 n} = {!Wrapping.𝐏 (Wrapping.flip 𝟎)!}

  flip-of-flip : ∀{N}{n : 𝕟(N)} → 𝕟.Wrapping.flip(𝕟.Wrapping.flip n) ≡ n
  flip-of-flip {N}{n} = sub₂(𝕟._≡_)(_≡_) ([−]-of-[−] {N}{N})

  𝕟-flip-elim : ∀{N} → (n : 𝕟(N)) → T(n)
  𝕟-flip-elim n = substitute₁ᵣ(T)
    flip-of-flip
    (𝕟-elim(T ∘ 𝕟.Wrapping.flip)
      (substitute₁ₗ(T) flip-of-minimum base)
      {!!}
      (𝕟.Wrapping.flip(n))
    )

-}
