module Numeral.Natural.Function.GreatestCommonDivisor.Algorithm where

import Lvl
open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Type
open import Type.Identity

-- TODO: Maybe mark (a > b) irrelevant? It is already an h-prop
module _
  {ℓ} (T : (a : ℕ) → (b : ℕ) → (a > b) → Type{ℓ})
  (s : (a : ℕ) → (b : ℕ) → ⦃ pos : Positive(b) ⦄ → (ord : a > b) → T b (a mod b) mod-maxᵣ → T a b ord)
  (z : (a : ℕ) → (ord : a > 𝟎) → T a 𝟎 ord)
  where

  -- The algorithm presented in its most general form.
  -- Note: Termination
  --   It terminates because both arguments are shrinking.
  --   (gcdAlgorithmElim a (𝐒(b))) calls (gcdAlgorithmElim (𝐒(b)) (a mod 𝐒(b))).
  --   First, (a > 𝐒(b)) holds, so the first argument is always strictly less.
  --   Second, (𝐒(b) > a mod 𝐒(b)), so the second argument is also always strictly less.
  {-# TERMINATING #-}
  gcdAlgorithmElim : (a : ℕ) → (b : ℕ) → (ab : a > b) → T a b ab
  gcdAlgorithmElim(a)(𝟎)    ord = z _ _
  gcdAlgorithmElim(a)(𝐒(b)) ord = s _ _ _ (gcdAlgorithmElim _ _ _)
  {-# INLINE gcdAlgorithmElim #-}

module _
  {ℓ} {T : Type{ℓ}}
  (s : (a : ℕ) → (b : ℕ) → ⦃ Positive(b) ⦄ → (a > b) → T → T)
  (c : T → T)
  (z : ℕ → T)
  where

  gcdAlgorithm : ℕ → ℕ → T
  gcdAlgorithm a b with [<]-trichotomy {a}{b}
  ... | [∨]-introₗ ([∨]-introₗ lt) = c(gcdAlgorithmElim(\_ _ _ → T) s (\a _ → z a) b a lt)
  ... | [∨]-introₗ ([∨]-introᵣ eq) = z a
  ... | [∨]-introᵣ             gt  = gcdAlgorithmElim(\_ _ _ → T) s (\a _ → z a) a b gt



module _
  {ℓ} {T : (a : ℕ) → (b : ℕ) → (a > b) → Type{ℓ}} {s}{z}
  {ℓₚ} (P : ∀{a b}{ord} → T a b ord → Type{ℓₚ})
  (ps : (a : ℕ) → (b : ℕ) → ⦃ pos : Positive(b) ⦄ → (ord : a > b) → let t = gcdAlgorithmElim T s z b (a mod b) mod-maxᵣ in P(t) → P(s a b ord t))
  (pz : (a : ℕ) → (ord : a > 𝟎) → P(z a ord))
  where

  gcdAlgorithmElimIntro : ∀(a)(b)(ord) → P(gcdAlgorithmElim T s z a b ord)
  gcdAlgorithmElimIntro = gcdAlgorithmElim(\a b ord → P{a}{b}{ord} (gcdAlgorithmElim T s z a b ord)) (\{ a (𝐒 b) ord → ps a (𝐒 b) ord }) pz

module _
  {ℓ₁} (T : Type{ℓ₁})
  {ℓ₂} (P : ∀{a b : ℕ} → T → Type{ℓ₂})
  {s : (a : ℕ) → (b : ℕ) → ⦃ Positive(b) ⦄ → (a > b) → T → T}
  {c : T → T}
  {z : ℕ → T}
  (ps : ∀{a b} ⦃ pos : Positive(b) ⦄ → (ord : a > b) → ∀{t} → P{b}{a mod b}(t) → P{a}{b}(s a b ord t))
  (pz : ∀{a} → (a > 0) → P{a}{𝟎}(z a))
  (pc : ∀{a b}{t} → (a > b) → P{a}{b}(t) → P{b}{a}(c t))
  (pe : ∀{a} → P{a}{a}(z a))
  where

  gcdAlgorithmIntro : ∀(a)(b) → P{a}{b}(gcdAlgorithm s c z a b)
  gcdAlgorithmIntro a b with [<]-trichotomy {a}{b}
  ... | [∨]-introₗ ([∨]-introₗ lt)    = pc lt (gcdAlgorithmElimIntro(\{a}{b} t → P{a}{b}(t)) (\_ _ ord → ps ord) (\_ → pz) b a lt)
  ... | [∨]-introₗ ([∨]-introᵣ intro) = pe
  ... | [∨]-introᵣ             gt     = gcdAlgorithmElimIntro(\{a}{b} t → P{a}{b}(t)) (\_ _ ord → ps ord) (\_ → pz) a b gt
