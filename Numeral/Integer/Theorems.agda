module Numeral.Integer.Theorems{ℓ} where

import      Level as Lvl
open import Functional
open import Numeral.Integer
open import Numeral.Integer.Oper
open import Numeral.Natural using (ℕ ; [ℕ]-induction) renaming (𝟎 to 𝟎ₙ ; 𝐒 to 𝐒ₙ)
import      Numeral.Natural as ℕ
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Relator.Equals{ℓ}{Lvl.𝟎}

[𝐏]-negative-successor : (n : ℕ) → (𝐏(−𝐒(n)) ≡ −𝐒(𝐒ₙ(n)))
[𝐏]-negative-successor (_) = [≡]-intro
  {-
  [ℕ]-induction base next where
    base : (𝐏(−𝐒(𝟎ₙ)) ≡ −𝐒(𝐒ₙ(𝟎ₙ)))
    base = [≡]-intro

    next : (n : ℕ) → (𝐏(−𝐒(n)) ≡ −𝐒(𝐒ₙ(n))) → (𝐏(−𝐒(𝐒ₙ(n))) ≡ −𝐒(𝐒ₙ(𝐒ₙ(n))))
    next(n)(proof) = [≡]-with-[ 𝐏 ] (proof)
  -}

[−𝐒]-identity : (n : ℕ) → (−𝐒(n) ≡ −(𝐒ₙ(n)))
[−𝐒]-identity (_) = [≡]-intro
  {-
  [ℕ]-induction base next where
    base : (−𝐒(𝟎ₙ) ≡ −(𝐒ₙ(𝟎ₙ)))
    base = [≡]-intro

    postulate next : (n : ℕ) → (−𝐒(n) ≡ −(𝐒ₙ(n))) → (−𝐒(𝐒ₙ(n)) ≡ −(𝐒ₙ(𝐒ₙ(n))))
    -- next(n)(proof) = [≡]-with-[ 𝐏 ] (proof)
    -- −𝐒(n) ≡ −(𝐒ₙ(n))
    -- 𝐏(−𝐒(n)) ≡ 𝐏(−(𝐒ₙ(n)))
    -- −𝐒(𝐒ₙ(n))) ≡ 𝐏(−𝐒(n)) ≡ 𝐏(−(𝐒ₙ(n)))
    -- −𝐒(𝐒ₙ(n))) ≡ 𝐏(−(𝐒ₙ(n)))
  -}

[𝐏𝐏]-negative : (n : ℕ) → (𝐏(𝐏(− n)) ≡ 𝐏(−(𝐒ₙ(n))))
[𝐏]-negative : (n : ℕ) → (𝐏(− n) ≡ −𝐒(n))

[𝐏𝐏]-negative = [ℕ]-induction base next where
  base : (𝐏(𝐏(− 𝟎ₙ)) ≡ 𝐏(−(𝐒ₙ(𝟎ₙ))))
  base = [≡]-intro

  -- TODO: One proof of this would rely on [𝐏]-negative
  postulate next : (n : ℕ) → (𝐏(𝐏(− n)) ≡ 𝐏(−(𝐒ₙ(n)))) → (𝐏(𝐏(− 𝐒ₙ(n))) ≡ 𝐏(−(𝐒ₙ(𝐒ₙ(n)))))
  {-next(n)(proof) =
    ([≡]-with-[ 𝐏 ]
      ([≡]-transitivity([∧]-intro
        ([≡]-transitivity([∧]-intro
          ([≡]-with-[ 𝐏 ] ([≡]-symmetry ([𝐏]-negative(n))))
          (proof)
        ))
        ([−𝐒]-identity(𝐒ₙ(n)))
      ))
    )-}
    -- 𝐏(−𝐒(n)) ≡ 𝐏(𝐏(− n))
    -- 𝐏(−𝐒(n)) ≡ 𝐏(𝐏(− n)) ≡ 𝐏(−(𝐒ₙ(n))))
    -- 𝐏(−𝐒(n)) ≡ 𝐏(−(𝐒ₙ(n))))
    -- 𝐏(−𝐒(n)) ≡ 𝐏(−(𝐒ₙ(n)))) ≡ −𝐒(𝐒ₙ(n))
    -- 𝐏(−𝐒(n)) ≡ −𝐒(𝐒ₙ(n))
    -- 𝐏(𝐏(−𝐒(n))) ≡ 𝐏(−𝐒(𝐒ₙ(n)))

[𝐏]-negative = [ℕ]-induction base next where
  base : 𝐏(− 𝟎ₙ) ≡ −𝐒(𝟎ₙ)
  base = [≡]-intro

  next : (n : ℕ) → (𝐏(− n) ≡ −𝐒(n)) → (𝐏(−(𝐒ₙ(n))) ≡ −𝐒(𝐒ₙ(n)))
  next(n)(proof) =
    [≡]-transitivity([∧]-intro
      ([≡]-symmetry ([𝐏𝐏]-negative(n)))
      ([≡]-transitivity([∧]-intro
        ([≡]-with-[ 𝐏 ] (proof))
        ([𝐏]-negative-successor(n))
      ))
    )
    -- 𝐏(− n) ≡ −𝐒(n)
    -- 𝐏(𝐏(− n)) ≡ 𝐏(−𝐒(n))
    -- 𝐏(−(𝐒ₙ(n))) ≡ 𝐏(𝐏(− n)) ≡ 𝐏(−𝐒(n)) ≡ −𝐒(𝐒ₙ(n))

-- postulate [𝐏][−𝐒]-identity : ∀{n} → 𝐏(−₁ n) ≡ −₁ 𝐒(+₁ n)

-- An intuitive induction proof method on integers
record [ℤ]-simple-induction-data (P : ℤ → Stmt) : Set(ℓ) where
  constructor [ℤ]-simple-ind
  field
    [−] : ∀{n} → P(− n) → P(−𝐒(n))
    [0] : P(𝟎)
    [+] : ∀{n} → P(+ n) → P(+𝐒(n))

{-# TERMINATING #-} -- TODO: Is the {+𝐒(n)}-case a problem because of (+_)?
[ℤ]-simple-induction : ∀{P} → [ℤ]-simple-induction-data(P) → (∀{n} → P(n))
[ℤ]-simple-induction {_} ([ℤ]-simple-ind [−] [0] [+]) {𝟎} = [0]
[ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {+𝐒(n)} = [+] ([ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {+ n})
[ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {−𝐒(n)} = [−] ([ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {− n})

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
...                                         | [∃]-intro (+𝐒(n)) base = [ℤ]-induction record{[0] = [∃]-intro (+ n) ([−] {+𝐒(n)} (base)) ; [+] = [+] ; [−] = [−]} {𝟎}
...                                         | [∃]-intro (−𝐒(n)) base = [ℤ]-induction record{[0] = [∃]-intro (− n) ([+] {−𝐒(n)} (base)) ; [+] = [+] ; [−] = [−]} {𝟎}
[ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+𝐒(n)} = [+]  ([ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+ n})
[ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {−𝐒(n)} = [−]' ([ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+ n}) where
  [−]' : ∀{n} → P(−₁ n) → P(𝐏(−₁ n))
  [−]' = [≡]-elimᵣ [𝐏][−𝐒]-identity [−]
-}
