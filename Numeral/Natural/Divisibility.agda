module Numeral.Natural.Divisibility{ℓ} where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Relator.Equals{ℓ}
open import Relator.Equals.Proofs{ℓ}
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
--     div23 : ¬(2 ∣ 3)
--     div23(Div𝐒())
--     This is a "valid" proof, but would not type-check because deconstruction from (2 ∣ 3) to (2 ∣ 1) is impossible.
--     Seems like the compiler would see (3 = 2+x), but because of definition of (_+_), only (3 = x+2) can be found.
--   Defining Div𝐒 with (x + y) inside would work, but then the definition of DivN becomes more complicated because (_⋅_) is defined in this order.
data _∣_ (y : ℕ) : ℕ → Stmt where
  instance
    Div𝟎 : (y ∣ 𝟎)
    Div𝐒 : ∀{x : ℕ} → (y ∣ x) → (y ∣ (y + x))

_∤_ : ℕ → ℕ → Stmt
y ∤ x = ¬(y ∣ x)

data _∣_withRemainder_ : ℕ → ℕ → ℕ → Stmt where -- TODO: Make _∣_ a special case of this. Tries (See below), but noticed that r<x would guarantee x≠0, which is good but not the same as the current definition of _∣_. This is also the same as the congruence relation with mod?
  instance
    DivRem𝟎 : ∀{x r : ℕ}   → ⦃ _ : r < x ⦄ → x ∣ r withRemainder r
    DivRem𝐒 : ∀{x y r : ℕ} → (x ∣ y withRemainder r) → (x ∣ (x + y) withRemainder r)

{-
_∣_ : ℕ → ℕ → Stmt
_∣_ y x = _∣_withRemainder_ y x 𝟎
pattern Div𝟎 {x}    = DivRem𝟎 {x}
pattern Div𝐒 {x}{y} = DivRem𝐒 {x}{y}
-}

DivN : ∀{y : ℕ} → (n : ℕ) → y ∣ (y ⋅ n)
DivN {y}(𝟎)    = Div𝟎
DivN {y}(𝐒(n)) = Div𝐒(DivN{y}(n))

{-
Div𝐏 : ∀{x y : ℕ} → (y ∣ x) → (y ∣ (x −₀ y))
Div𝐏 {x}   {𝟎}    (0-div-x) = 0-div-x
Div𝐏 {𝟎}   {y}    (y-div-0) = [≡]-substitutionₗ ([−₀]-negative{y}) {expr ↦ (y ∣ expr)} (Div𝟎)
Div𝐏 {_}{y} (Div𝐒{x} (y-div-x)) = [≡]-substitutionᵣ [−₀]ₗ[+]ᵣ-nullify {expr ↦ (y ∣ expr)} y-div-x
-}

divides-intro : ∀{x y} → (∃ \(n : ℕ) → (y ⋅ n ≡ x)) → (y ∣ x)
divides-intro {x}{y} ([∃]-intro (n) ⦃ y⋅n≡x ⦄) = [≡]-elimᵣ (y⋅n≡x) {expr ↦ (y ∣ expr)} (DivN{y}(n))

divides-elim : ∀{x y} → (y ∣ x) → (∃ \(n : ℕ) → (y ⋅ n ≡ x))
divides-elim {_}{_} (Div𝟎) = [∃]-intro (0) ⦃ [≡]-intro ⦄
divides-elim {_}{y} (Div𝐒{x} (y-div-x)) with divides-elim(y-div-x)
... | ([∃]-intro (n) ⦃ y⋅n≡x ⦄) = [∃]-intro (𝐒(n)) ⦃ [≡]-with(expr ↦ y + expr) (y⋅n≡x) ⦄

{-
Div𝐏 : ∀{x y : ℕ} → (y ∣ (y + x)) → (y ∣ x)
Div𝐏 {x}{y} (proof) with divides-elim(proof)
... | [∃]-intro (𝟎)   ⦃ y0≡yx ⦄ = divides-intro(y0≡yx) TODO
... | [∃]-intro (𝐒(n)) ⦃ ySn≡yx ⦄ = divides-intro([∃]-intro (n) ⦃ [+]-injectivityᵣ {y} ySn≡yx ⦄)
-}

{-test : ∀{y}{x}{proof} → Div𝐒{y}{x}(proof) ≢ proof
test ()
-}
instance
  divides-transitivity : Transitivity (_∣_)
  transitivity ⦃ divides-transitivity ⦄ {a}{b}{c} (a-div-b) (b-div-c) with (divides-elim (a-div-b) , divides-elim (b-div-c))
  ... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ b⋅n₂≡c ⦄)) =
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

divides-with-[+] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b + c))
divides-with-[+] {a}{b}{c} (a-div-b) (a-div-c) with (divides-elim (a-div-b) , divides-elim (a-div-c))
... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
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

divides-with-[⋅] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b ⋅ c))
divides-with-[⋅] {a}{b}{c} (a-div-b) (a-div-c) with (divides-elim (a-div-b) , divides-elim (a-div-c))
... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
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

divides-with-[−₀] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b −₀ c))
divides-with-[−₀] {a}{b}{c} (a-div-b) (a-div-c) with (divides-elim (a-div-b) , divides-elim (a-div-c))
... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
  (divides-intro
    ([∃]-intro
      (n₁ −₀ n₂)
     ⦃
        ([⋅][−₀]-distributivityₗ {a}{n₁}{n₂})
        🝖 ([≡]-with-op(_−₀_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

divides-without-[+]ₗ : ∀{a b c} → (a ∣ (b + c)) → (a ∣ c) → (a ∣ b)
divides-without-[+]ₗ {a}{b}{c} = divides-with-[−₀] {a}{b + c}{c}

divides-without-[+]ᵣ : ∀{a b c} → (a ∣ (b + c)) → (a ∣ b) → (a ∣ c)
divides-without-[+]ᵣ {a}{b}{c} abc ab = divides-without-[+]ₗ {a}{c}{b} ([≡]-elimᵣ ([+]-commutativity{b}{c}) {expr ↦ a ∣ expr} abc) ab

-- divides-[⋅] : ∀{a b c} → Coprime(b)(c) → (a ∣ (b ⋅ c)) → ((a ∣ b) ∨ (a ∣ c))

-- instance
--   divides-with-fn : ∀{a b} → (a ∣ b) → ∀{f : ℕ → ℕ} → {_ : ∀{x y : ℕ} → ∃{ℕ → ℕ}(\g → f(x ⋅ y) ≡ f(x) ⋅ g(y))} → ((f(a)) ∣ (f(b)))
--   divides-with-fn {a}{b} (a-div-b) {f} ⦃ f-prop ⦄ 

-- instance
--   divides-[≡] : ∀{a b} → (a ∣ b) → (b ∣ a) → (a ≡ b)
--   divides-[≡] {a}{b}{c} ((a-div-b),(b-div-c)) with (divides-elim (a-div-b) , divides-elim (b-div-c))
--   ... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ b⋅n₂≡c ⦄)) =

instance
  [1]-divides : ∀{n} → (1 ∣ n)
  [1]-divides {𝟎}    = Div𝟎
  [1]-divides {𝐒(n)} =
    [≡]-elimₗ
      ([+]-commutativity {n}{1})
      {expr ↦ (1 ∣ expr)}
      (Div𝐒([1]-divides{n}))

instance
  divides-reflexivity : ∀{n} → (n ∣ n)
  divides-reflexivity = Div𝐒(Div𝟎)

instance
  [0]-divides-[0] : (0 ∣ 0)
  [0]-divides-[0] = Div𝟎

[0]-only-divides-[0] : ∀{n} → (0 ∣ n) → (n ≡ 0)
[0]-only-divides-[0] {𝟎} _ = [≡]-intro
[0]-only-divides-[0] {𝐒(n)} (proof) = [⊥]-elim(([𝐒]-not-0 ∘ symmetry) ([∃]-proof(divides-elim(proof)))) -- ∃(i ↦ 0 ⋅ i ≡ 𝐒(n))

[0]-divides-not : ∀{n} → ¬(0 ∣ 𝐒(n))
[0]-divides-not (0divSn) = [𝐒]-not-0([0]-only-divides-[0] (0divSn))
-- [0]-divides-not {n} (Div𝐒(proof)) =  -- TODO: This makes Div𝐒(proof)≡proof ? Is Div𝐒(proof)≢proof provable?

divides-not-[1] : ∀{n} → ¬((n + 2) ∣ 1)
divides-not-[1] ()

[1]-only-divides-[1] : ∀{n} → (n ∣ 1) → (n ≡ 1)
[1]-only-divides-[1] {𝟎}       (ndiv1) = [⊥]-elim ([0]-divides-not (ndiv1))
[1]-only-divides-[1] {𝐒(𝟎)}    (ndiv1) = [≡]-intro
[1]-only-divides-[1] {𝐒(𝐒(n))} ()

postulate divides-upper-limit : ∀{a b} → (a ∣ b) → (a ≤ b)

postulate divides-not-lower-limit : ∀{a b} → (a > b) → ¬(a ∣ b)

Div𝐏 : ∀{x y : ℕ} → (y ∣ (y + x)) → (y ∣ x)
Div𝐏 {x}{y} proof = divides-without-[+]ᵣ {y}{y}{x} (proof) (divides-reflexivity)

-- divides-factorial : ∀{n x} → (𝐒(x) < n) → (𝐒(x) ∣ n !)
