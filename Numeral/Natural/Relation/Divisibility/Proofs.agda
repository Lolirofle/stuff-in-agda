module Numeral.Natural.Relation.Divisibility.Proofs where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.GreatestCommonDivisor
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Order.Existence using ([≤]-equivalence)
open import Numeral.Natural.Relation.Order.Existence.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

even-unique-instance : ∀{n} → (proof₁ : Even(n)) → (proof₂ : Even(n)) → (proof₁ ≡ proof₂)
even-unique-instance (Even0) (Even0) = [≡]-intro
even-unique-instance (Even𝐒 proof₁) (Even𝐒 proof₂) = [≡]-with(Even𝐒) (even-unique-instance(proof₁)(proof₂))

DivN : ∀{y : ℕ} → (n : ℕ) → y ∣ (y ⋅ n)
DivN {y}(𝟎)    = Div𝟎
DivN {y}(𝐒(n)) = Div𝐒(DivN{y}(n))

{-
Div𝐏 : ∀{x y : ℕ} → (y ∣ x) → (y ∣ (x −₀ y))
Div𝐏 {x}   {𝟎}    (0-div-x) = 0-div-x
Div𝐏 {𝟎}   {y}    (y-div-0) = [≡]-substitutionₗ ([−₀]-negative{y}) {expr ↦ (y ∣ expr)} (Div𝟎)
Div𝐏 {_}{y} (Div𝐒{x} (y-div-x)) = [≡]-substitutionᵣ [−₀]ₗ[+]ᵣ-nullify {expr ↦ (y ∣ expr)} y-div-x
-}

divides-intro : ∀{x y} → (∃(n ↦ y ⋅ n ≡ x)) → (y ∣ x)
divides-intro {x}{y} ([∃]-intro (n) ⦃ y⋅n≡x ⦄) = [≡]-elimᵣ (y⋅n≡x) {expr ↦ (y ∣ expr)} (DivN{y}(n))

divides-elim : ∀{x y} → (y ∣ x) → (∃(n ↦ y ⋅ n ≡ x))
divides-elim {_}{_} (Div𝟎) = [∃]-intro (0) ⦃ [≡]-intro ⦄
divides-elim {_}{y} (Div𝐒{x} (y-div-x)) with divides-elim(y-div-x)
... | ([∃]-intro (n) ⦃ y⋅n≡x ⦄) = [∃]-intro (𝐒(n)) ⦃ [≡]-with(y +_) (y⋅n≡x) ⦄

divides-intro-alt : ∀{n x y} → ⦃ _ : y ⋅ n ≡ x ⦄ → (y ∣ x)
divides-intro-alt {n}{x}{y} ⦃ proof ⦄ = ([↔]-to-[←] ([∀]-unrelatedₗ-[→] {X = ℕ} {n ↦ y ⋅ n ≡ x} {y ∣ x})) divides-intro {n} (proof)

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
  Transitivity.proof (divides-transitivity) {a}{b}{c} (a-div-b) (b-div-c) with (divides-elim (a-div-b) , divides-elim (b-div-c))
  ... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ b⋅n₂≡c ⦄)) =
    (divides-intro
      ([∃]-intro
        (n₁ ⋅ n₂)
       ⦃
          (symmetry(_≡_) ([⋅]-associativity-raw {a}{n₁}{n₂}))
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
        ([⋅][+]-distributivityₗ-raw {a}{n₁}{n₂})
        🝖 ([≡]-with-op(_+_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

postulate divides-with-[⋅]ₗ : ∀{a b c} → (a ∣ b) → (a ∣ (b ⋅ c))
postulate divides-with-[⋅]ᵣ : ∀{a b c} → (a ∣ c) → (a ∣ (b ⋅ c))

divides-with-[⋅] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b ⋅ c)) -- TODO: Does it really need both? One of them should be enough?
divides-with-[⋅] {a}{b}{c} (a-div-b) (a-div-c) with (divides-elim (a-div-b) , divides-elim (a-div-c))
... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
  (divides-intro
    ([∃]-intro
      (n₁ ⋅ (a ⋅ n₂))
     ⦃
        (symmetry(_≡_) ([⋅]-associativity-raw {a}{n₁}{a ⋅ n₂}))
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
        ([⋅][−₀]-distributivityₗ-raw {a}{n₁}{n₂})
        🝖 ([≡]-with-op(_−₀_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

divides-without-[+]ₗ : ∀{a b c} → (a ∣ (b + c)) → (a ∣ c) → (a ∣ b)
divides-without-[+]ₗ {a}{b}{c} abc ac = [≡]-substitutionᵣ ([−₀]ₗ[+]ᵣ-nullify{b}{c}) {expr ↦ (a ∣ expr)} (divides-with-[−₀] {a}{b + c}{c} abc ac)

divides-without-[+]ᵣ : ∀{a b c} → (a ∣ (b + c)) → (a ∣ b) → (a ∣ c)
divides-without-[+]ᵣ {a}{b}{c} abc ab = divides-without-[+]ₗ {a}{c}{b} ([≡]-elimᵣ ([+]-commutativity-raw{b}{c}) {expr ↦ a ∣ expr} abc) ab

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
      ([+]-commutativity-raw {n}{1})
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
[0]-only-divides-[0] {𝐒(n)} (proof) = [⊥]-elim(([𝐒]-not-0 ∘ symmetry(_≡_)) ([∃]-proof(divides-elim(proof)))) -- ∃(i ↦ 0 ⋅ i ≡ 𝐒(n))

[0]-divides-not : ∀{n} → ¬(0 ∣ 𝐒(n))
[0]-divides-not (0divSn) = [𝐒]-not-0([0]-only-divides-[0] (0divSn))
-- [0]-divides-not {n} (Div𝐒(proof)) =  -- TODO: This makes Div𝐒(proof)≡proof ? Is Div𝐒(proof)≢proof provable?

divides-not-[1] : ∀{n} → ¬((n + 2) ∣ 1)
divides-not-[1] ()

[1]-only-divides-[1] : ∀{n} → (n ∣ 1) → (n ≡ 1)
[1]-only-divides-[1] {𝟎}       (ndiv1) = [⊥]-elim ([0]-divides-not (ndiv1))
[1]-only-divides-[1] {𝐒(𝟎)}    (ndiv1) = [≡]-intro
[1]-only-divides-[1] {𝐒(𝐒(n))} ()

divides-elim₊ : ∀{x y} → (y ∣ 𝐒(x)) → ∃(n ↦ y ⋅ 𝐒(n) ≡ 𝐒(x))
divides-elim₊ {x}{y} (proof) with divides-elim{𝐒(x)}{y} (proof)
...                             | [∃]-intro (𝟎)    ⦃ y𝟎≡𝐒x ⦄  = [⊥]-elim (([𝐒]-not-0 ∘ symmetry(_≡_)) (symmetry(_≡_) ([⋅]-absorberᵣ-raw {y}) 🝖 y𝟎≡𝐒x))
...                             | [∃]-intro (𝐒(n)) ⦃ y𝐒n≡𝐒x ⦄ = [∃]-intro (n) ⦃ y𝐒n≡𝐒x ⦄

divides-upper-limit : ∀{a b} → (a ∣ 𝐒(b)) → (a ≤ 𝐒(b))
divides-upper-limit {𝟎}   {_} (proof) = [⊥]-elim ([0]-divides-not (proof))
divides-upper-limit {𝐒(a)}{b} (proof) = ([↔]-to-[→] [≤]-equivalence) (existence2) where
  existence1 : ∃(n ↦ 𝐒(a) + (𝐒(a) ⋅ n) ≡ 𝐒(b))
  existence1 = divides-elim₊(proof)

  existence2 : ∃(n ↦ 𝐒(a) + n ≡ 𝐒(b))
  existence2 = [∃]-intro(𝐒(a) ⋅ [∃]-witness(existence1)) ⦃ [∃]-proof(existence1) ⦄

divides-not-lower-limit : ∀{a b} → (a > 𝐒(b)) → (a ∤ 𝐒(b))
divides-not-lower-limit {a}{b} = (contrapositiveᵣ (divides-upper-limit {a}{b})) ∘ [>]-to-[≰]

Div𝐏 : ∀{x y : ℕ} → (y ∣ (y + x)) → (y ∣ x)
Div𝐏 {x}{y} proof = divides-without-[+]ᵣ {y}{y}{x} (proof) (divides-reflexivity)

divides-with-[⋅]ₗ-both : ∀{x y z} → (x ∣ y) → (z ⋅ x ∣ z ⋅ y)
divides-with-[⋅]ₗ-both {x} {.0}       {z} Div𝟎 = Div𝟎
divides-with-[⋅]ₗ-both {x} {.(x + _)} {z} (Div𝐒 {_}{y} xy) rewrite [⋅][+]-distributivityₗ-raw {z}{x}{y} = Div𝐒 (divides-with-[⋅]ₗ-both {x}{y}{z} xy)

divides-with-[⋅]ᵣ-both : ∀{x y z} → (x ∣ y) → (x ⋅ z ∣ y ⋅ z)
divides-with-[⋅]ᵣ-both {x} {.0}       {z} Div𝟎 = Div𝟎
divides-with-[⋅]ᵣ-both {x} {.(x + _)} {z} (Div𝐒 {_}{y} xy) rewrite [⋅][+]-distributivityᵣ-raw {x}{y}{z} = Div𝐒 (divides-with-[⋅]ᵣ-both {x}{y}{z} xy)

-- divides-without-[⋅]ₗ-both : ∀{x y z} → (z ⋅ x ∣ z ⋅ y) → (x ∣ y)

-- divides-factorial : ∀{n x} → (𝐒(x) ≤ n) → (𝐒(x) ∣ (n !))

-- postulate gcd-identityₗ : ∀{b} → (gcd(𝟎)(b) ≡ b)
-- gcd-identityₗ {𝟎}    = [≡]-intro
-- gcd-identityₗ {𝐒(b)} = gcd-identityₗ {b}
  -- gcd(𝟎)(𝐒(b))
  -- = gcd(𝐒(b))(_mod_ 𝟎 (𝐒(b)) ⦃ [𝐒]-not-0 ⦄)
  -- = gcd(𝐒(b))(𝟎)

-- gcd-identityᵣ : ∀{a} → (gcd(a)(𝟎) ≡ a)
-- gcd-identityᵣ = [≡]-intro

-- postulate gcd-annihilatorₗ : ∀{b} → (gcd(1)(b) ≡ 1)

-- postulate gcd-annihilatorᵣ : ∀{a} → (gcd(a)(1) ≡ 1)

-- postulate gcd-of-mod : ∀{a b} → (gcd(𝐒(b))(a) ≡ gcd(𝐒(b))(_mod_ a (𝐒(b)) ⦃ [𝐒]-not-0 ⦄))

-- postulate gcd-commutativity : Commutativity(gcd)
-- gcd-commutativity {𝟎}   {𝟎}    = [≡]-intro
-- gcd-commutativity {𝟎}   {𝐒(b)} = [≡]-intro
-- gcd-commutativity {𝐒(a)}{𝟎}    = [≡]-intro
-- gcd-commutativity {𝐒(a)}{𝐒(b)} = [≡]-intro

-- postulate gcd-associativity : Associativity(gcd)

-- postulate gcd-same : ∀{a} → (gcd(a)(a) ≡ a)

-- postulate gcd-dividesₗ : ∀{a b} → (gcd(a)(b) ∣ a)
-- gcd-dividesₗ {a}{b} = 

-- postulate gcd-dividesᵣ : ∀{a b} → (gcd(a)(b) ∣ b)

-- postulate gcd-min : ∀{a b} → (gcd(a)(b) ≤ min(a)(b))

-- postulate gcd-with-[+] : ∀{a b} → (gcd(a + b)(b) ≡ gcd(a)(b))

-- postulate gcd-with-[⋅] : ∀{a b} → (gcd(a ⋅ b)(b) ≡ b)

-- postulate gcd-coprime : ∀{a b} → CoPrime(a / gcd(a)(b))(b / gcd(a)(b))

-- postulate gcd-divisors : ∀{a b d} → (d ∣ a) → (d ∣ b) → (d ∣ gcd(a)(b))
