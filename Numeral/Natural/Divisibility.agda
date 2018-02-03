module Numeral.Natural.Divisibility{ℓ} where

import Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Relator.Equals{ℓ}
open import Relator.Equals.Theorems{ℓ}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

data Even : ℕ → Stmt where
  instance
    Even0 : Even(𝟎)
    Even𝐒 : ∀{x : ℕ} → Even(x) → Even(𝐒(𝐒(x)))
{-# INJECTIVE Even #-}

even-unique-instance : ∀{n} → (proof₁ : Even(n)) → (proof₂ : Even(n)) → (proof₁ ≡ proof₂)
even-unique-instance (Even0) (Even0) = [≡]-intro
even-unique-instance (Even𝐒 proof₁) (Even𝐒 proof₂) = [≡]-with(Even𝐒) (even-unique-instance(proof₁)(proof₂))

data Odd : ℕ → Stmt where
  instance
    Odd0 : Odd(𝐒(𝟎))
    Odd𝐒 : ∀{x : ℕ} → Odd(x) → Odd(𝐒(𝐒(x)))
{-# INJECTIVE Odd #-}

-- Note on the definition of Div𝐒:
--   The order (y + x) works and depends on rewriting rules of ℕ at the moment (Specifically on the commuted identity and successor rules, I think).
--   Without rewriting rules, deconstruction of Div𝐒 seems not working.
--   Example:
--     div23 : ¬(2 divides 3)
--     div23(Div𝐒())
--     This is a "valid" proof, but would not type-check because deconstruction from (2 divides 3) to (2 divides 1) is impossible.
--     Seems like the compiler would see (3 = 2+x), but because of definition of (_+_), only (3 = x+2) can be found.
--   Defining Div𝐒 with (x + y) inside would work, but then the definition of DivN becomes more complicated because (_⋅_) is defined in this order.
data _divides_ (y : ℕ) : ℕ → Stmt where
  instance
    Div𝟎 : (y divides 𝟎)
    Div𝐒 : ∀{x : ℕ} → (y divides x) → (y divides (y + x))
_∣_ = _divides_

data _divides_withRemainder_ : ℕ → ℕ → ℕ → Stmt where -- TODO: Make _divides_ a special case of this. Tries (See below), but noticed that r<x would guarantee x≠0, which is good but not the same as the current definition of _divides_.
  instance
    DivRem𝟎 : ∀{x r : ℕ}   → ⦃ _ : r < x ⦄ → x divides r withRemainder r
    DivRem𝐒 : ∀{x y r : ℕ} → (x divides y withRemainder r) → (x divides (x + y) withRemainder r)
{-# INJECTIVE _divides_withRemainder_ #-}

{-
_divides_ : ℕ → ℕ → Stmt
_divides_ y x = _divides_withRemainder_ y x 𝟎
pattern Div𝟎 {x}    = DivRem𝟎 {x}
pattern Div𝐒 {x}{y} = DivRem𝐒 {x}{y}
-}

DivN : ∀{y : ℕ} → (n : ℕ) → y divides (y ⋅ n)
DivN {y}(𝟎)    = Div𝟎
DivN {y}(𝐒(n)) = Div𝐒(DivN{y}(n))

{-
Div𝐏 : ∀{x y : ℕ} → (y divides x) → (y divides (x −₀ y))
Div𝐏 {x}   {𝟎}    (0-div-x) = 0-div-x
Div𝐏 {𝟎}   {y}    (y-div-0) = [≡]-substitutionₗ ([−₀]-negative{y}) {expr ↦ (y divides expr)} (Div𝟎)
Div𝐏 {_}{y} (Div𝐒{x} (y-div-x)) = [≡]-substitutionᵣ [+][−₀]-nullify {expr ↦ (y divides expr)} y-div-x
-}

divides-intro : ∀{x y} → (∃ \(n : ℕ) → (y ⋅ n ≡ x)) → (y divides x)
divides-intro {x}{y} ([∃]-intro (n) ⦃ y⋅n≡x ⦄) = [≡]-elimᵣ (y⋅n≡x) {expr ↦ (y divides expr)} (DivN{y}(n))

divides-elim : ∀{x y} → (y divides x) → (∃ \(n : ℕ) → (y ⋅ n ≡ x))
divides-elim {_}{_} (Div𝟎) = [∃]-intro (0) ⦃ [≡]-intro ⦄
divides-elim {_}{y} (Div𝐒{x} (y-div-x)) with divides-elim(y-div-x)
...                                | ([∃]-intro (n) ⦃ y⋅n≡x ⦄) = [∃]-intro (𝐒(n)) ⦃ [≡]-with(expr ↦ y + expr) (y⋅n≡x) ⦄

{-
Div𝐏 : ∀{x y : ℕ} → (y divides (y + x)) → (y divides x)
Div𝐏 {x}{y} (proof) with divides-elim(proof)
...             | [∃]-intro (𝟎)    ⦃ y0≡yx ⦄  = divides-intro(y0≡yx) TODO
...             | [∃]-intro (𝐒(n)) ⦃ ySn≡yx ⦄ = divides-intro([∃]-intro (n) ⦃ [+]-injectivityᵣ {y} ySn≡yx ⦄)
-}

{-test : ∀{y}{x}{proof} → Div𝐒{y}{x}(proof) ≢ proof
test ()
-}
instance
  divides-transitivity : Transitivity (_divides_)
  transitivity{{divides-transitivity}} {a}{b}{c} (a-div-b) (b-div-c) with (divides-elim (a-div-b) , divides-elim (b-div-c))
  ...                                                     | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ b⋅n₂≡c ⦄)) =
    (divides-intro
      ([∃]-intro
        (n₁ ⋅ n₂)
        ⦃
          (symmetry ([⋅]-associativity {a}{n₁}{n₂}))
          🝖 ([≡]-with(expr ↦ expr ⋅ n₂) (a⋅n₁≡b))
          🝖 (b⋅n₂≡c)
        ⦄
      )
    )

divides-with-[+] : ∀{a b c} → (a divides b) → (a divides c) → (a divides (b + c))
divides-with-[+] {a}{b}{c} (a-div-b) (a-div-c) with (divides-elim (a-div-b) , divides-elim (a-div-c))
...                                                 | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
  (divides-intro
    ([∃]-intro
      (n₁ + n₂)
      ⦃
        ([⋅][+]-distributivityₗ {a}{n₁}{n₂})
        🝖 ([≡]-with-op(_+_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

divides-with-[⋅] : ∀{a b c} → (a divides b) → (a divides c) → (a divides (b ⋅ c))
divides-with-[⋅] {a}{b}{c} (a-div-b) (a-div-c) with (divides-elim (a-div-b) , divides-elim (a-div-c))
...                                                 | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
  (divides-intro
    ([∃]-intro
      (n₁ ⋅ (a ⋅ n₂))
      ⦃
        (symmetry ([⋅]-associativity {a}{n₁}{a ⋅ n₂}))
        🝖 ([≡]-with-op(_⋅_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

-- instance
--   divides-with-fn : ∀{a b} → (a divides b) → ∀{f : ℕ → ℕ} → {_ : ∀{x y : ℕ} → ∃{ℕ → ℕ}(\g → f(x ⋅ y) ≡ f(x) ⋅ g(y))} → ((f(a)) divides (f(b)))
--   divides-with-fn {a}{b} (a-div-b) {f} {{f-prop}}

-- instance
--   divides-[≡] : ∀{a b} → (a divides b) → (b divides a) → (a ≡ b)
--   divides-[≡] {a}{b}{c} ((a-div-b),(b-div-c)) with (divides-elim (a-div-b) , divides-elim (b-div-c))
--   ...                                                     | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ b⋅n₂≡c ⦄)) =

instance
  [1]-divides : ∀{n} → (1 divides n)
  [1]-divides {𝟎}    = Div𝟎
  [1]-divides {𝐒(n)} =
    [≡]-elimₗ
      ([+]-commutativity {n}{1})
      {expr ↦ (1 divides expr)}
      (Div𝐒([1]-divides{n}))

instance
  divides-id : ∀{n} → (n divides n)
  divides-id = Div𝐒(Div𝟎)

instance
  [0]-divides-[0] : (0 divides 0)
  [0]-divides-[0] = Div𝟎

[0]-only-divides-[0] : ∀{n} → (0 divides n) → (n ≡ 0)
[0]-only-divides-[0] {𝟎} _ = [≡]-intro
[0]-only-divides-[0] {𝐒(n)} (proof) = [⊥]-elim(([𝐒]-not-0 ∘ symmetry) ([∃]-proof(divides-elim(proof)))) -- ∃(i ↦ 0 ⋅ i ≡ 𝐒(n))

[0]-divides-not : ∀{n} → ¬(0 divides 𝐒(n))
[0]-divides-not (0divSn) = [𝐒]-not-0([0]-only-divides-[0] (0divSn))
-- [0]-divides-not {n} (Div𝐒(proof)) =  -- TODO: This makes Div𝐒(proof)≡proof ? Is Div𝐒(proof)≢proof provable?

divides-not-[1] : ∀{n} → ¬((n + 2) divides 1)
divides-not-[1] ()

postulate divides-upper-limit : ∀{a b} → (a divides b) → (a ≤ b)

postulate divides-not-lower-limit : ∀{a b} → (a > b) → ¬(a divides b)

-- Div𝐏 : ∀{x y : ℕ} → (y divides (y + x)) → (y divides x)
-- Div𝐏 {x}   {𝟎}    (0-div-x) = 0-div-x
-- Div𝐏 {𝟎}   {y}    (y-div-y) = Div𝟎
-- Div𝐏 {x₁}{y} (Div𝐒{x₂} y-div-x) =
