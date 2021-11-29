module Numeral.Natural.Inductions.Proofs where

open import Numeral.Natural
open import Numeral.Natural.Induction
open import Syntax.Function
open import Type

{-
module _ where
  import Lvl
  open import Data
  open import Logic
  open import Logic.Propositional
  open import Functional
  open import Numeral.Natural
  open import Numeral.Natural.Induction
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  open import Structure.Relator.Ordering
  open import Structure.Relator.Properties
  open import Type
  ℕ-strong-recursion2 : ∀{ℓ} → (P : ℕ → Type{ℓ}) → ((n : ℕ) → ((i : ℕ) → .(i < n) → P(i)) → P(n)) → ((n : ℕ) → P(n))
  ℕ-strong-recursion2 P step n = ℕ-elim(n ↦ ((i : ℕ) → .(i < n) → P(i)))
    (\_ ())
    (\n prev i i𝐒n → step i (\j ji → prev j (transitivity(_≤_) ji ([≤]-without-[𝐒] i𝐒n))))
    (𝐒(n)) n (reflexivity(_≤_))

  ℕ-strong-recursion3 : ∀{ℓ} → (P : ℕ → Type{ℓ}) → ((n : ℕ) → ((i : ℕ) → .(i < n) → P(i)) → P(n)) → ((n : ℕ) → .(n < 𝐒 n) → P(n))
  ℕ-strong-recursion3 P step n = ℕ-elim(n ↦ ((i : ℕ) → .(i < n) → P(i)))
    (\_ ())
    (\n prev i i𝐒n → step i (\j ji → prev j (transitivity(_≤_) ji ([≤]-without-[𝐒] i𝐒n))))
    (𝐒(n)) n

  module _ {ℓ₁ ℓ₂} {T : ℕ → Type{ℓ₁}} {P : (x : ℕ) → T(x) → Type{ℓ₂}} where
    ℕ-strong-recursion-intro' : ∀{rec : (x : ℕ) → ((i : ℕ) → .(i < x) → T(i)) → T(x)}
                              → ((y : ℕ)
                                → ((x : ℕ) → .(xy : x < y) → P x (ℕ-strong-recursion2(T) rec x))
                                → P y (rec y λ j .ji → {!ℕ-strong-recursion2(T) rec j!}
                                                 -- ℕ-strong-recursion2(T) rec j
                                                 -- ℕ-elim (λ n → (i : ℕ) → .(i < n) → T i) (λ i ()) (λ n prev i .i𝐒n → rec i (λ j₁ .ji₁ → prev j₁ (transitivity _≤_ ji₁ ([≤]-without-[𝐒] i𝐒n)))) y j (transitivity _≤_ ji ([≤]-without-[𝐒] (reflexivity _≤_)))
                                                )
                                -- TODO: Would be good if above was   or something similar instead
                              )
                              → ((x : ℕ) → P x (ℕ-strong-recursion2(T) rec x))
    ℕ-strong-recursion-intro'{rec = rec} = ℕ-strong-recursion2(\x → P x (ℕ-strong-recursion2(T) rec x))
-}

module _ {ℓ₁ ℓ₂} {T : ℕ → Type{ℓ₁}} {P : (x : ℕ) → T(x) → Type{ℓ₂}} where
  ℕ-elim-intro : ∀{base : T(𝟎)}{step : (x : ℕ) → T(x) → T(𝐒(x))}
                 → P(𝟎)(base)
                 → ((x : ℕ)
                   → P x (ℕ-elim T base step x)
                   → P(𝐒(x)) (step x (ℕ-elim T base step x))
                 )
                 → ((x : ℕ) → P x (ℕ-elim T base step x))
  ℕ-elim-intro{base = base}{step = step} = ℕ-elim(x ↦ P x (ℕ-elim T base step x))

  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Inductions

  ℕ-strong-recursion-intro : ∀{rec : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}
                             → ((y : ℕ)
                               → ((x : ℕ) → (xy : x < y) → P x (ℕ-strong-recursion(T) rec x))
                               → P y (ℕ-strong-recursion(T) rec y)
                               -- TODO: Would be good if above was rec y (\x _ → ℕ-strong-recursion(T) rec x) or something similar instead
                             )
                             → ((x : ℕ) → P x (ℕ-strong-recursion(T) rec x))
  ℕ-strong-recursion-intro{rec = rec} = ℕ-strong-recursion(x ↦ P x (ℕ-strong-recursion(T) rec x))

  {-
  open import Relator.Equals

  ℕ-strong-recursion-intro2 : ∀{rec : (x : ℕ) → ((i : ℕ) → .(i < x) → T(i)) → T(x)}
                            → ((y : ℕ)
                              → ((x : ℕ) → (xy : x < y) → P x (ℕ-strong-recursion2(T) rec x))
                              → (ℕ-strong-recursion2(T) rec y ≡ rec y (\x ord → ℕ-strong-recursion2(T) ? x))
                              → P y (ℕ-strong-recursion2(T) rec y)
                            )
                            → ((x : ℕ) → P x (ℕ-strong-recursion2(T) rec x))
  ℕ-strong-recursion-intro2{rec = rec} prec = ℕ-strong-recursion2(x ↦ P x (ℕ-strong-recursion2(T) rec x)) proof where
    proof : (n : ℕ) → ((i : ℕ) → .(i < n) → P i (ℕ-strong-recursion2 T rec i)) → P n (ℕ-strong-recursion2 T rec n)
    proof 𝟎 p = prec 𝟎 p [≡]-intro
    proof (𝐒 n) p = prec (𝐒 n) p {! ℕ-strong-recursion T rec (n)!}
    -- proof 𝟎 p = prec 𝟎 p {!ℕ-strong-recursion T rec 𝟎!}
    -- proof (𝐒 n) p with a ← ℕ-strong-recursion T rec (𝐒 n) = {!prec (𝐒 n) p!} -- prec (𝐒 n) p ([≡]-with(rec(𝐒 n)) {![≡]-intro!})
  -}

{-
ℕ-strong-recursion-function : ∀{ℓ}{T : ℕ → Type{ℓ}}{rec₁ rec₂ : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}
                              → (∀{x} → rec₁ x ≡ rec₂ x)
                              → (∀{x} → (ℕ-strong-recursion(T) rec₁ x ≡ ℕ-strong-recursion(T) rec₂ x))
ℕ-strong-recursion-function {T = T} {rec₁} {rec₂} receq {n} = ℕ-strong-recursion-intro{T = T}{rec = rec₂}{P = \x y → ℕ-strong-recursion T rec₁ x ≡ y} {!!} n
-}
