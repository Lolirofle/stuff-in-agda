module Numeral.Natural.Inductions.Proofs where

{-

open import Numeral.Natural.Induction
open import Type
ℕ-elim-intro : ∀{ℓ₁ ℓ₂}{T : ℕ → Type{ℓ₁}}{base : T(𝟎)}{step : (x : ℕ) → T(x) → T(𝐒(x))}{P : (x : ℕ) → T(x) → Type{ℓ₂}}
               → P(𝟎)(base)
               → ((x : ℕ)
                 → P x (ℕ-elim base step x)
                 → P(𝐒(x)) (step x (ℕ-elim base step x))
               )
               → ((x : ℕ) → P x (ℕ-elim base step x))
ℕ-elim-intro{base = base}{step = step}{P = P} = ℕ-elim{T = x ↦ P x (ℕ-elim base step x)}

{-
ℕ-strong-recursion-intro2 : ∀{ℓ₁ ℓ₂}{T : ℕ → Type{ℓ₁}}{rec : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}{P : (x : ℕ) → T(x) → Type{ℓ₂}}
                           → ((y : ℕ)
                             → ((x : ℕ) → (xy : x < y) → P x (ℕ-strong-recursion(T) rec x))
                             → (ℕ-strong-recursion(T) rec y ≡ rec y (\x _ → ℕ-strong-recursion(T) rec x))
                             → P y (ℕ-strong-recursion(T) rec y)
                           )
                           → ((x : ℕ) → P x (ℕ-strong-recursion(T) rec x))
ℕ-strong-recursion-intro2 {T = T} {rec = rec} {P = P} prec = ℕ-strong-recursion(x ↦ P x (ℕ-strong-recursion(T) rec x)) proof where
  proof : (n : ℕ) → ((i : ℕ) → i < n → P i (ℕ-strong-recursion T rec i)) → P n (ℕ-strong-recursion T rec n)
  proof 𝟎 p = prec 𝟎 p {!ℕ-strong-recursion T rec 𝟎!}
  proof (𝐒 n) p with a ← ℕ-strong-recursion T rec (𝐒 n) = {!prec (𝐒 n) p!} -- prec (𝐒 n) p ([≡]-with(rec(𝐒 n)) {![≡]-intro!})
-}
ℕ-strong-recursion-intro : ∀{ℓ₁ ℓ₂}{T : ℕ → Type{ℓ₁}}{rec : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}{P : (x : ℕ) → T(x) → Type{ℓ₂}}
                           → ((y : ℕ)
                             → ((x : ℕ) → (xy : x < y) → P x (ℕ-strong-recursion(T) rec x))
                             → P y (ℕ-strong-recursion(T) rec y)
                             -- TODO: Would be good if above was rec y (\x _ → ℕ-strong-recursion(T) rec x) or something similar instead
                           )
                           → ((x : ℕ) → P x (ℕ-strong-recursion(T) rec x))
ℕ-strong-recursion-intro{T = T}{rec = rec}{P = P} = ℕ-strong-recursion(x ↦ P x (ℕ-strong-recursion(T) rec x))

{-
ℕ-strong-recursion-function : ∀{ℓ}{T : ℕ → Type{ℓ}}{rec₁ rec₂ : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}
                              → (∀{x} → rec₁ x ≡ rec₂ x)
                              → (∀{x} → (ℕ-strong-recursion(T) rec₁ x ≡ ℕ-strong-recursion(T) rec₂ x))
ℕ-strong-recursion-function {T = T} {rec₁} {rec₂} receq {n} = ℕ-strong-recursion-intro{T = T}{rec = rec₂}{P = \x y → ℕ-strong-recursion T rec₁ x ≡ y} {!!} n
-}

-}
