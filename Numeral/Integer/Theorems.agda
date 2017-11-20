module Numeral.Integer.Theorems{ℓ} where

import      Lvl
open import Functional
open import Numeral.Integer
open import Numeral.Integer.Oper
open import Numeral.Natural.Proof
open import Numeral.Natural as ℕ using (ℕ)
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Theorems{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}

-- TODO: Prove the usual strcutures for ℤ

[𝐏]-negative-successor : (n : ℕ) → (𝐏(−𝐒ₙ(n)) ≡ −𝐒ₙ(ℕ.𝐒(n)))
[𝐏]-negative-successor (_) = [≡]-intro
  {-
  [ℕ]-induction base next where
    base : (𝐏(−𝐒ₙ(ℕ.𝟎)) ≡ −𝐒ₙ(ℕ.𝐒(ℕ.𝟎)))
    base = [≡]-intro

    next : (n : ℕ) → (𝐏(−𝐒ₙ(n)) ≡ −𝐒ₙ(ℕ.𝐒(n))) → (𝐏(−𝐒ₙ(ℕ.𝐒(n))) ≡ −𝐒ₙ(ℕ.𝐒(ℕ.𝐒(n))))
    next(n)(proof) = [≡]-with-[ 𝐏 ] (proof)
  -}

[−𝐒ₙ]-identity : (n : ℕ) → (−𝐒ₙ(n) ≡ −ₙ(ℕ.𝐒(n)))
[−𝐒ₙ]-identity (_) = [≡]-intro
  {-
  [ℕ]-induction base next where
    base : (−𝐒ₙ(ℕ.𝟎) ≡ −ₙ(ℕ.𝐒(ℕ.𝟎)))
    base = [≡]-intro

    postulate next : (n : ℕ) → (−𝐒ₙ(n) ≡ −ₙ(ℕ.𝐒(n))) → (−𝐒ₙ(ℕ.𝐒(n)) ≡ −ₙ(ℕ.𝐒(ℕ.𝐒(n))))
    -- next(n)(proof) = [≡]-with-[ 𝐏 ] (proof)
    -- −𝐒ₙ(n) ≡ −ₙ(ℕ.𝐒(n))
    -- 𝐏(−𝐒ₙ(n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n)))
    -- −𝐒ₙ(ℕ.𝐒(n))) ≡ 𝐏(−𝐒ₙ(n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n)))
    -- −𝐒ₙ(ℕ.𝐒(n))) ≡ 𝐏(−ₙ(ℕ.𝐒(n)))
  -}

[𝐏𝐏]-negative : ∀{n} → (𝐏(𝐏(−ₙ n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n))))
[𝐏]-negative : ∀{n} → (𝐏(−ₙ n) ≡ −𝐒ₙ(n))

[𝐏𝐏]-negative = [ℕ]-induction base next where
  base : (𝐏(𝐏(−ₙ ℕ.𝟎)) ≡ 𝐏(−ₙ(ℕ.𝐒(ℕ.𝟎))))
  base = [≡]-intro

  -- TODO: One proof of this would rely on [𝐏]-negative
  postulate next : ∀(n : ℕ) → (𝐏(𝐏(−ₙ n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n)))) → (𝐏(𝐏(−ₙ ℕ.𝐒(n))) ≡ 𝐏(−ₙ(ℕ.𝐒(ℕ.𝐒(n)))))
  {-next(n)(proof) =
    ([≡]-with-[ 𝐏 ]
      ([≡]-transitivity([∧]-intro
        ([≡]-transitivity([∧]-intro
          ([≡]-with-[ 𝐏 ] ([≡]-symmetry ([𝐏]-negative(n))))
          (proof)
        ))
        ([−𝐒ₙ]-identity(ℕ.𝐒(n)))
      ))
    )-}
    -- 𝐏(−𝐒ₙ(n)) ≡ 𝐏(𝐏(−ₙ n))
    -- 𝐏(−𝐒ₙ(n)) ≡ 𝐏(𝐏(−ₙ n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n))))
    -- 𝐏(−𝐒ₙ(n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n))))
    -- 𝐏(−𝐒ₙ(n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n)))) ≡ −𝐒ₙ(ℕ.𝐒(n))
    -- 𝐏(−𝐒ₙ(n)) ≡ −𝐒ₙ(ℕ.𝐒(n))
    -- 𝐏(𝐏(−𝐒ₙ(n))) ≡ 𝐏(−𝐒ₙ(ℕ.𝐒(n)))

[𝐏]-negative = [ℕ]-induction base next where
  base : 𝐏(−ₙ ℕ.𝟎) ≡ −𝐒ₙ(ℕ.𝟎)
  base = [≡]-intro

  next : ∀(n : ℕ) → (𝐏(−ₙ n) ≡ −𝐒ₙ(n)) → (𝐏(−ₙ(ℕ.𝐒(n))) ≡ −𝐒ₙ(ℕ.𝐒(n)))
  next(n)(proof) =
    (symmetry ([𝐏𝐏]-negative{n}))
    🝖 ([≡]-with-[ 𝐏 ] (proof))
    🝖 ([𝐏]-negative-successor(n))
    -- 𝐏(−ₙ n) ≡ −𝐒ₙ(n)
    -- 𝐏(𝐏(−ₙ n)) ≡ 𝐏(−𝐒ₙ(n))
    -- 𝐏(−ₙ(ℕ.𝐒(n))) ≡ 𝐏(𝐏(−ₙ n)) ≡ 𝐏(−𝐒ₙ(n)) ≡ −𝐒ₙ(ℕ.𝐒(n))

-- postulate [𝐏][−𝐒ₙ]-identity : ∀{n} → 𝐏(− n) ≡ − 𝐒(+₁ n)

-- An intuitive induction proof method on integers
record [ℤ]-simple-induction-data (P : ℤ → Stmt) : Set(ℓ) where
  constructor [ℤ]-simple-ind
  field
    [−] : ∀{n} → P(−ₙ n) → P(−𝐒ₙ(n))
    [0] : P(𝟎)
    [+] : ∀{n} → P(+ₙ n) → P(+𝐒ₙ(n))

{-# TERMINATING #-} -- TODO: Is the {+𝐒ₙ(n)}-case a problem because of (+_)?
[ℤ]-simple-induction : ∀{P} → [ℤ]-simple-induction-data(P) → (∀{n} → P(n))
[ℤ]-simple-induction {_} ([ℤ]-simple-ind [−] [0] [+]) {𝟎} = [0]
[ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {+𝐒ₙ(n)} = [+] ([ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {+ₙ n})
[ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {−𝐒ₙ(n)} = [−] ([ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {−ₙ n})

-- An intuitive induction proof method on integers
record [ℤ]-induction-data (P : ℤ → Stmt) : Set(ℓ) where
  constructor [ℤ]-ind
  field
    [−] : ∀{n} → P(n) → P(𝐏(n))
    [0] : ∃(n ↦ P(n))
    [+] : ∀{n} → P(n) → P(𝐒(n))

{-
[ℤ]-induction : ∀{P} → [ℤ]-induction-data(P) → (∀{n} → P(n))
[ℤ]-induction {_} ([ℤ]-ind [−] [0] [+]) {𝟎} with [0]
...                                         | [∃]-intro (𝟎)     base = base
...                                         | [∃]-intro (+𝐒ₙ(n)) base = [ℤ]-induction record{[0] = [∃]-intro (+ₙ n) ([−] {+𝐒ₙ(n)} (base)) ; [+] = [+] ; [−] = [−]} {𝟎}
...                                         | [∃]-intro (−𝐒ₙ(n)) base = [ℤ]-induction record{[0] = [∃]-intro (−ₙ n) ([+] {−𝐒ₙ(n)} (base)) ; [+] = [+] ; [−] = [−]} {𝟎}
[ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+𝐒ₙ(n)} = [+]  ([ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+ n})
[ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {−𝐒ₙ(n)} = [−]' ([ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+ n}) where
  [−]' : ∀{n} → P(− n) → P(𝐏(− n))
  [−]' = [≡]-elimᵣ [𝐏][−𝐒ₙ]-identity [−]
-}
