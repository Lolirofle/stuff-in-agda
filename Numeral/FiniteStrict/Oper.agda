module Numeral.FiniteStrict.Oper where

import Lvl
open import Syntax.Number
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.FiniteStrict
open import Numeral.FiniteStrict.Bound{0}
open import Numeral.Natural hiding (𝐏)
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Relation.Order{0}
open import Numeral.Natural.Relation.Order.Proofs{0}
open import Relator.Equals{0}{0}
open import Relator.Equals.Proofs{0}{0}

𝐏₀ : ∀{n} → 𝕟(ℕ.𝐒(ℕ.𝐒(n))) → 𝕟(𝐒(n))
𝐏₀(𝟎)    = 𝟎
𝐏₀(𝐒(n)) = n

𝐏₀keep : ∀{n} → 𝕟(n) → 𝕟(n)
𝐏₀keep {ℕ.𝟎}    ()
𝐏₀keep {ℕ.𝐒(b)} (𝟎)       = 𝟎
𝐏₀keep {ℕ.𝐒(b)} (𝐒(𝟎))    = 𝟎
𝐏₀keep {ℕ.𝐒(b)} (𝐒(𝐒(n))) = 𝐒(𝐏₀keep {b} (𝐒(n)))

𝐒keep : ∀{b} → (n : 𝕟(𝐒(b))) → ⦃ _ : ℕ.𝐒 ([𝕟]-to-[ℕ] (n)) ≤ b ⦄ → 𝕟(𝐒(b)) -- (n ≢ b) would also work?
𝐒keep {ℕ.𝟎}    (_)    ⦃ ⦄
𝐒keep {ℕ.𝐒(b)} (𝟎)    ⦃ _ ⦄     = 𝐒(𝟎)
𝐒keep {ℕ.𝐒(b)} (𝐒(n)) ⦃ proof ⦄ = 𝐒(𝐒keep {b} (n) ⦃ [≤]-without-[𝐒] {ℕ.𝐒([𝕟]-to-[ℕ] (n))} {b} (proof) ⦄)

{- TODO: Cannot solve first. Unsure why
[𝐒]-not-0 : ∀{b : ℕ}{n : 𝕟(ℕ.𝐒(b))} → (𝐒{b}(n) ≢ 𝟎{ℕ.𝐒(b)})
[𝐒]-not-0 ()

𝐏keep : ∀{b} → (n : 𝕟(𝐒(b))) → ⦃ _ : n ≢ 𝟎 ⦄ → 𝕟(𝐒(b))
𝐏keep {ℕ.𝟎}    (𝟎)       ⦃ proof ⦄ with proof([≡]-intro)
... | ()
𝐏keep {ℕ.𝐒(b)} (𝟎)       ⦃ _ ⦄     = 𝟎
𝐏keep {ℕ.𝐒(b)} (𝐒(𝟎))    ⦃ _ ⦄     = 𝟎
𝐏keep {ℕ.𝐒(b)} (𝐒(𝐒(n))) ⦃ proof ⦄ = 𝐒(𝐏keep {b} (𝐒(n)) ⦃ [𝐒]-not-0 ⦄)
-}

-- _ : ∀{b} → (n : 𝕟(b)) → ([𝕟]-to-[ℕ] (n) < b)

_+small_ : ∀{b₁ b₂} → (x : 𝕟(𝐒(b₁))) → (y : 𝕟(𝐒(b₂))) → 𝕟(ℕ.𝐒([𝕟]-to-[ℕ] (x) ℕ.+ [𝕟]-to-[ℕ] (y)))
_+small_      𝟎       𝟎      = 𝟎
_+small_ {b₁} (𝐒(a))  𝟎      = 𝐒(a +small 𝟎{b₁})
_+small_      a       (𝐒(b)) = 𝐒(a +small b)

_−small_ : ∀{b} → (x : 𝕟(𝐒(b))) → (y : 𝕟(ℕ.𝐒([𝕟]-to-[ℕ] (x)))) → 𝕟(ℕ.𝐒([𝕟]-to-[ℕ] (x) ℕ.−₀ [𝕟]-to-[ℕ] (y)))
𝟎    −small 𝟎    = 𝟎
𝐒(a) −small 𝟎    = 𝐒(a −small 𝟎)
𝐒(a) −small 𝐒(b) = a −small b

_+_ : ∀{b₁ b₂} → (x : 𝕟(𝐒(b₁))) → (y : 𝕟(𝐒(b₂))) → 𝕟(𝐒(b₁ ℕ.+ b₂))
_+_          𝟎       𝟎      = 𝟎
_+_ {b₁}{b₂} (𝐒(a))  𝟎      = 𝐒(a + 𝟎{b₂})
_+_          a       (𝐒(b)) = 𝐒(a + b)

_−_ : ∀{b} → (x : 𝕟(𝐒(b))) → (y : 𝕟(ℕ.𝐒([𝕟]-to-[ℕ] (x)))) → 𝕟(𝐒(b))
𝟎    − 𝟎    = 𝟎
𝐒(a) − 𝟎    = 𝐒(a)
𝐒(a) − 𝐒(b) = bound-𝐒(a − b)
