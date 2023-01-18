module Numeral.Natural.Oper.Modulo.Proofs where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs.Algorithm
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Existence using ([≤]-equivalence)
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity
open import Syntax.Type
open import Type
open import Numeral.Natural.Oper.DivMod.Proofs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod₀ and mod

mod₀-mod : ∀{a b} ⦃ pos : Positive(b) ⦄ → ((a mod₀ b) ≡ (a mod b))
mod₀-mod {b = 𝐒 _} = [≡]-intro

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod

open import Numeral.Natural.Inductions
open import Structure.Relator
open import Structure.Relator.Ordering

{-
mod-elim : ∀{ℓ} → (P : {ℕ} → ℕ → Type{ℓ}) → ∀{b} ⦃ _ : Positive(b) ⦄ → (∀{a} → (a < b) → P{a}(a)) → (∀{a} → (a ≥ b) → P{a −₀ b}((a −₀ b) mod b) → P{a}(a mod b)) → (∀{a} → P{a}(a mod b))
mod-elim P {𝐒 b} base step {a} = Strict.Properties.wellfounded-recursion(_<_) {P = a ↦ P(a mod 𝐒(b))} p a where
  ord : ∀{a b} → (b < a) → (a −₀ 𝐒(b) < a)
  ord {𝐒 a} {b} _ = succ ([−₀]-lesser {a}{b})

  p : (a : ℕ) → ((prev : ℕ) ⦃ _ : prev < a ⦄ → P(prev mod 𝐒(b))) → P(a mod 𝐒(b))
  p a prev with [<][≥]-dichotomy {a}{𝐒 b}
  ... | [∨]-introₗ lt = substitute₁ₗ(P) (mod'-lesser-dividend ([≤]-without-[𝐒] lt)) (base{a} lt)
  ... | [∨]-introᵣ ge = step ge (prev(a −₀ 𝐒(b)) ⦃ ord{a}{b} ge ⦄)
-}

-- 0 is 0 in every modulus.
mod-of-0 : ∀{b} ⦃ pos : Positive(b) ⦄ → (0 mod b ≡ 0)
mod-of-0 {𝐒 _} = [≡]-intro

-- There is only one value when the modulus is 1, and that is 0.
mod-of-1 : ∀{a} → (a mod 1 ≡ 0)
mod-of-1 {a} = mod'-zero-all-except-dividend {a}

-- When the dividend is lesser than the modulus, the result is unchanged.
mod-lesser-than-modulus : ∀{a b} ⦃ pos : Positive(b) ⦄ → (a < b) → (a mod b ≡ a)
mod-lesser-than-modulus {a} {𝐒 b} (succ ab) = mod'-lesser-dividend ab

-- The value of the modulo operation is always strictly less than the modulus.
-- This is because the value loops around at the end by definition.
mod-maxᵣ : ∀{a b} → ⦃ _ : Positive(b) ⦄ → (a mod b < b)
mod-maxᵣ {𝟎}   {𝐒 𝟎}    = [≤]-with-[𝐒]
mod-maxᵣ {𝟎}   {𝐒(𝐒 b)} = [≤]-with-[𝐒]
mod-maxᵣ {𝐒 a} {𝐒 𝟎}    = mod-maxᵣ {a}{𝐒 𝟎}
mod-maxᵣ {𝐒 a} {𝐒(𝐒 b)} = [≤]-with-[𝐒] ⦃ mod'-maxᵣ {1}{b}{a}{b} ⦃ reflexivity(_≤_)⦄ ⦄

-- When proving properties about the modulo operation, only proofs about numbers lesser than the modulus is necessary.
mod-intro : ∀{ℓ} → (P : {ℕ} → ℕ → Type{ℓ}) → ∀{b} ⦃ _ : Positive(b) ⦄ → (∀{a n} → (a < b) → P{a + (n ⋅ b)}(a)) → (∀{a} → P{a}(a mod b))
mod-intro P {𝐒 b} proof {a} with [<][≥]-dichotomy {a}{𝐒 b}
... | [∨]-introₗ lt = substitute₂ᵣ(\x y → P{x}(y))
  (reflexivity(_≡_))
  (symmetry(_≡_) (mod-lesser-than-modulus lt))
  (proof{a}{0} lt)
... | [∨]-introᵣ ge = substitute₂ᵣ(\x y → P{x}(y))
  ([↔]-to-[→] ([−₀][+]-nullify2ᵣ {(a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b)}{a}) (subtransitivityᵣ(_≤_)(_≡_) ([≤]-of-[+]ₗ {(a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b)}{a mod 𝐒(b)}) ([⌊/⌋][mod]-is-division-with-remainder {a}{𝐒 b})))
  (symmetry(_≡_) ([⌊/⌋][⋅]-inverseOperatorᵣ-error {a}{𝐒 b}))
  (proof{a −₀ ((a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b))}{a ⌊/⌋ 𝐒(b)} (subtransitivityₗ(_<_)(_≡_) (symmetry(_≡_) ([⌊/⌋][⋅]-inverseOperatorᵣ-error {a}{𝐒 b})) (mod-maxᵣ{a}{𝐒 b})))

mod-intro₂ : ∀{ℓ} → (P : {ℕ} → {ℕ} → ℕ → ℕ → Type{ℓ}) → ∀{m} ⦃ _ : Positive(m) ⦄ → (∀{a b n₁ n₂} → (a < m) → (b < m) → P{a + (n₁ ⋅ m)}{b + (n₂ ⋅ m)}(a)(b)) → (∀{a b} → P{a}{b}(a mod m)(b mod m))
mod-intro₂ P {m} p {a}{b} = mod-intro(\{a} am → P{a}{b}(am)(b mod m)) {m} (\{a}{n₁} an₁ → mod-intro(\{b} bm → P{a + (n₁ ⋅ m)}{b}(a)(bm)) {m} (\{b}{n₂} bn₂ → p {a}{b}{n₁}{n₂} an₁ bn₂) {b}) {a}

-- The modulus is the loop point of the dividend.
mod-of-modulus : ∀{b} ⦃ pos : Positive(b) ⦄ → (b mod b ≡ 𝟎)
mod-of-modulus {𝐒 b} = mod'-equal-dividend {𝟎}{b}{b}

-- Adding the modulus to the dividend does not alter the result.
mod-of-modulus-add : ∀{a b} ⦃ pos : Positive(b) ⦄ → ((b + a) mod b ≡ a mod b)
mod-of-modulus-add {a}{𝐒 b} = mod'-sumₗ-modulo {𝟎}{b}{a}{b}

mod-of-modulus-addᵣ : ∀{a b} → ((a + 𝐒(b)) mod 𝐒(b) ≡ a mod 𝐒(b))
mod-of-modulus-addᵣ {a}{b} = mod'-sumᵣ-modulo {𝟎}{b}{a}{b}

-- A multiple of the modulus in the dividend is always 0.
mod-of-modulus-multiple : ∀{a b} ⦃ pos : Positive(b) ⦄ → ((b ⋅ a) mod b ≡ 𝟎)
mod-of-modulus-multiple {𝟎}   {b} = mod-of-0 {b}
mod-of-modulus-multiple {𝐒 a} {b} = mod-of-modulus-add {b ⋅ a}{b} 🝖 mod-of-modulus-multiple {a} {b}

mod-of-modulus-sum-multiple : ∀{a b c} ⦃ _ : Positive(b) ⦄ → ((a + (b ⋅ c)) mod b ≡ a mod b)
mod-of-modulus-sum-multiple {a} {𝐒 b} {𝟎} = [≡]-intro
mod-of-modulus-sum-multiple {a} {𝐒 b} {𝐒 c} =
  (a + (𝐒(b) ⋅ 𝐒(c))) mod 𝐒(b)       🝖[ _≡_ ]-[]
  (a + (𝐒(b) + (𝐒(b) ⋅ c))) mod 𝐒(b) 🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(b)) (associativity(_+_) {a}{𝐒(b)}{𝐒(b) ⋅ c}) ]-sym
  ((a + 𝐒(b)) + (𝐒(b) ⋅ c)) mod 𝐒(b) 🝖[ _≡_ ]-[ mod-of-modulus-sum-multiple {a + 𝐒(b)} {𝐒 b} {c} ]
  (a + 𝐒(b)) mod 𝐒(b)                🝖[ _≡_ ]-[ mod-of-modulus-addᵣ {a}{b} ]
  a mod 𝐒(b)                         🝖-end

mod-of-modulus-sum-multiple-commuted : ∀{a b c} ⦃ _ : Positive(b) ⦄ → ((a + (c ⋅ b)) mod b ≡ a mod b)
mod-of-modulus-sum-multiple-commuted {a}{𝐒 b}{c} = congruence₁(_mod 𝐒(b)) (congruence₂-₂(_+_)(a) (commutativity(_⋅_) {c}{𝐒 b})) 🝖 mod-of-modulus-sum-multiple{a}{𝐒 b}{c}

mod-of-modulus-sum-divisibleᵣ : ∀{a b c} ⦃ _ : Positive(c) ⦄ → (c ∣ b) → ((a + b) mod c ≡ a mod c)
mod-of-modulus-sum-divisibleᵣ {a} {b} {c} cb
  with [∃]-intro x ⦃ [≡]-intro ⦄ ← [↔]-to-[←] divides-[⋅]-existence cb
  = mod-of-modulus-sum-multiple {a}{c}{x}

mod-of-modulus-sum-divisibleₗ : ∀{a b c} ⦃ _ : Positive(c) ⦄ → (c ∣ a) → ((a + b) mod c ≡ b mod c)
mod-of-modulus-sum-divisibleₗ {a} {b} {c} ca = congruence₁(_mod c) (commutativity(_+_) {a}{b}) 🝖 mod-of-modulus-sum-divisibleᵣ {b} ca

-- When the dividend is greater than the modulus, the modulus can be subtracted from the dividend without altering the result.
mod-greater-than-modulus : ∀{a b} ⦃ pos : Positive(b) ⦄ → (a ≥ b) → (a mod b ≡ (a −₀ b) mod b)
mod-greater-than-modulus {a}{b} gt =
  a              mod b 🝖[ _≡_ ]-[ congruence₁(_mod b) ([↔]-to-[→] [−₀][+]-nullify2 gt) ]-sym
  (b + (a −₀ b)) mod b 🝖[ _≡_ ]-[ mod-of-modulus-add {a −₀ b}{b} ]
  (a −₀ b)       mod b 🝖-end

mod-nested : ∀{a b c} ⦃ pos-b : Positive(b) ⦄ ⦃ pos-c : Positive(c) ⦄ → (b ≤ c) → ((a mod b) mod c ≡ a mod b)
mod-nested {a} {b} {c} bc = mod-lesser-than-modulus {a mod b} (mod-maxᵣ{a} 🝖 bc)

mod-maxₗ : ∀{a b} → ⦃ _ : Positive(b) ⦄ → (a mod b ≤ a)
mod-maxₗ{a}{𝐒 b} = mod'-maxₗ{0}{b}{a}{b}

-- Alternative proof:
-- • Using [mod][∣ᵣₑₘ]-remainder-equality and that (_∣ᵣₑₘ_) using (r = 0) is equivalent to (_∣_).
-- • A special case of mod-congruence-[𝄩] and including an converse of mod-of-modulus-sum-divisibleₗ and mod-of-modulus-sum-divisibleᵣ.
mod-divisibility : ∀{a b} ⦃ pos : Positive(b) ⦄ → (a mod b ≡ 𝟎) ↔ (b ∣ a)
mod-divisibility = [↔]-intro l r where
  l : ∀{a b} ⦃ pos : Positive(b) ⦄ → (a mod b ≡ 𝟎) ← (b ∣ a)
  l {.0}           {b} Div𝟎          = mod-of-0 {b}
  l {.(b + a)} {b} (Div𝐒 {x = a} ba) = mod-of-modulus-add {a}{b} 🝖 l ba

  r : ∀{a b} ⦃ pos : Positive(b) ⦄ → (a mod b ≡ 𝟎) → (b ∣ a)
  r{a}{𝐒 b} = Strict.Properties.wellfounded-recursion(_<_) {P = a ↦ ((a mod 𝐒(b) ≡ 𝟎) → (𝐒(b) ∣ a))} p a where
    p : (a : ℕ) → ((prev : ℕ) ⦃ _ : prev < a ⦄ → (prev mod 𝐒(b) ≡ 𝟎) → (𝐒(b) ∣ prev)) → (a mod 𝐒(b) ≡ 𝟎) → (𝐒(b) ∣ a)
    p a prev ab0 with [≤][>]-dichotomy {a}{b}
    ... | [∨]-introₗ ab = substitute₂-₂ₗ(_∣_)(𝐒(b)) (symmetry(_≡_) (mod-lesser-than-modulus(succ ab)) 🝖 ab0) Div𝟎
    ... | [∨]-introᵣ ba =
      let [∃]-intro n ⦃ pa ⦄ = [↔]-to-[←] [≤]-equivalence ba
      in substitute₂-₂ᵣ(_∣_)(𝐒(b)) pa (divides-with-[+]
        (reflexivity(_∣_))
        (prev n ⦃ subtransitivityᵣ(_≤_)(_≡_) (succ([≤]-of-[+]ᵣ {b}{n})) pa ⦄ (
          n mod 𝐒(b)          🝖-[ mod-of-modulus-add {n}{𝐒(b)} ]-sym
          (𝐒(b) + n) mod 𝐒(b) 🝖-[ congruence₁(_mod 𝐒(b)) pa ]
          a mod 𝐒(b)          🝖-[ ab0 ]
          𝟎                   🝖-end
        ))
      )

mod-of-𝐒 : ∀{a b} → ⦃ pos : Positive(b) ⦄ → (𝐒(a) mod b ≡ 𝐒(a mod b) mod b)
mod-of-𝐒 {a} {𝐒 b} = mod-intro(\{a} → expr ↦ 𝐒(a) mod 𝐒(b) ≡ 𝐒(expr) mod 𝐒(b)) {𝐒(b)} (\{a}{n} → p{a}{n}) {a} where
  p : ∀{a n} → (a < 𝐒(b)) → (𝐒(a + (n ⋅ 𝐒(b))) mod 𝐒(b)) ≡ (𝐒(a) mod 𝐒(b))
  p {a}{n} ab =
    𝐒(a + (n ⋅ 𝐒(b))) mod 𝐒(b)   🝖[ _≡_ ]-[]
    (𝐒(a) + (n ⋅ 𝐒(b))) mod 𝐒(b) 🝖[ _≡_ ]-[ mod-of-modulus-sum-multiple-commuted {𝐒(a)}{𝐒(b)}{n} ]
    𝐒(a) mod 𝐒(b)                🝖-end

mod-of-[+] : ∀{a b m} → ⦃ pos : Positive(m) ⦄ → ((a + b) mod m ≡ ((a mod m) + (b mod m)) mod m)
mod-of-[+] {a}{b}{m} =
  (a + b) mod m                                                         🝖[ _≡_ ]-[ congruence₁(_mod m) (congruence₂(_+_) ([⌊/⌋][mod]-is-division-with-remainder{a}{m}) ([⌊/⌋][mod]-is-division-with-remainder{b}{m})) ]-sym
  ((((a ⌊/⌋ m) ⋅ m) + (a mod m)) + (((b ⌊/⌋ m) ⋅ m) + (b mod m))) mod m 🝖[ _≡_ ]-[ congruence₁(_mod m) (One.associate-commute4-c {_▫_ = _+_} {a = (a ⌊/⌋ m) ⋅ m}{a mod m}{(b ⌊/⌋ m) ⋅ m}{b mod m}) ]
  ((((a ⌊/⌋ m) ⋅ m) + ((b ⌊/⌋ m) ⋅ m)) + ((a mod m) + (b mod m))) mod m 🝖[ _≡_ ]-[ congruence₁(_mod m) (commutativity(_+_) {((a ⌊/⌋ m) ⋅ m) + ((b ⌊/⌋ m) ⋅ m)}{(a mod m) + (b mod m)}) ]
  (((a mod m) + (b mod m)) + (((a ⌊/⌋ m) ⋅ m) + ((b ⌊/⌋ m) ⋅ m))) mod m 🝖[ _≡_ ]-[ congruence₁(_mod m) (congruence₂-₂(_+_)((a mod m) + (b mod m)) (distributivityᵣ(_⋅_)(_+_) {a ⌊/⌋ m}{b ⌊/⌋ m}{m})) ]-sym
  (((a mod m) + (b mod m)) + (((a ⌊/⌋ m) + (b ⌊/⌋ m)) ⋅ m)) mod m       🝖[ _≡_ ]-[ mod-of-modulus-sum-multiple-commuted{(a mod m) + (b mod m)}{m}{(a ⌊/⌋ m) + (b ⌊/⌋ m)} ]
  ((a mod m) + (b mod m)) mod m                                         🝖-end

mod-nested-divisible : ∀{a b c} ⦃ pos-b : Positive(b) ⦄ ⦃ pos-c : Positive(c) ⦄ → (c ∣ b) → ((a mod b) mod c ≡ a mod c)
mod-nested-divisible {a}{b}{c} cb = mod-intro(\{a} m → (m mod c ≡ a mod c)) {b} \{a}{n} ab →
  a mod c                             🝖[ _≡_ ]-[ mod-nested {a}{c} (reflexivity(_≤_)) ]-sym
  (a mod c) mod c                     🝖[ _≡_ ]-[]
  ((a mod c) + 𝟎) mod c               🝖[ _≡_ ]-[ congruence₁(_mod c) (congruence₂-₂(_+_)(a mod c) ([↔]-to-[←] (mod-divisibility {n ⋅ b}{c}) (divides-with-[⋅] {b = n} ([∨]-introᵣ cb)))) ]-sym
  ((a mod c) + ((n ⋅ b) mod c)) mod c 🝖[ _≡_ ]-[ mod-of-[+] {a}{n ⋅ b}{c} ]-sym
  (a + (n ⋅ b)) mod c                 🝖-end

{-
open import Functional
open import Structure.Function
open import Structure.Function.Domain
{-# TERMINATING #-}
mod-of-𝐒 : ∀{a b} → ⦃ pos : Positive(b) ⦄ → (𝐒(a) mod b ≡ 𝐒(a mod b)) ∨ (𝐒(a) mod b ≡ 𝟎)
mod-of-𝐒 {𝟎} {𝐒 𝟎}     = [∨]-introᵣ [≡]-intro
mod-of-𝐒 {𝟎} {𝐒 (𝐒 b)} = [∨]-introₗ [≡]-intro
mod-of-𝐒 {a} {𝐒 b} with [<]-trichotomy {a}{b}
... | [∨]-introₗ([∨]-introₗ lt) = [∨]-introₗ $
  𝐒(a) mod 𝐒(b) 🝖[ _≡_ ]-[ mod-lesser-than-modulus ⦃ lt ⦄ ]
  𝐒(a)          🝖[ _≡_ ]-[ congruence₁(𝐒) (mod-lesser-than-modulus ⦃ [≤]-predecessor lt ⦄) ]-sym
  𝐒(a mod 𝐒(b)) 🝖-end
... | [∨]-introₗ([∨]-introᵣ [≡]-intro) = [∨]-introᵣ(mod-of-modulus{b})
... | [∨]-introᵣ gt with mod-of-𝐒 {a −₀ 𝐒(b)}{𝐒 b}
... |   [∨]-introₗ q = [∨]-introₗ ∘ injective(𝐒) $
  𝐒(𝐒(a) mod 𝐒(b))              🝖[ _≡_ ]-[ congruence₁(𝐒) (mod-greater-than-modulus ⦃ [≤]-successor gt ⦄) ]
  𝐒((𝐒(a) −₀ 𝐒(b)) mod 𝐒(b))    🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₁(_mod 𝐒(b)) ([↔]-to-[→] [−₀][𝐒]ₗ-equality gt)) ]
  𝐒(𝐒(a −₀ 𝐒(b)) mod 𝐒(b))      🝖[ _≡_ ]-[ congruence₁(𝐒) q ]
  𝐒(𝐒((a −₀ 𝐒(b)) mod 𝐒(b)))    🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₁(𝐒) (mod-greater-than-modulus ⦃ gt ⦄)) ]-sym
  𝐒(𝐒(a mod 𝐒(b)))              🝖-end
... |   [∨]-introᵣ q = [∨]-introᵣ $
  (𝐒(a) mod 𝐒(b))           🝖[ _≡_ ]-[ mod-greater-than-modulus ⦃ [≤]-successor gt ⦄ ]
  ((𝐒(a) −₀ 𝐒(b)) mod 𝐒(b)) 🝖[ _≡_ ]-[ congruence₁(_mod 𝐒(b)) ([↔]-to-[→] [−₀][𝐒]ₗ-equality gt) ]
  (𝐒(a −₀ 𝐒(b)) mod 𝐒(b))   🝖[ _≡_ ]-[ q ]
  0                         🝖-end
-}

{-mod-congruence-with-𝐒 {a}{b}{𝐒 m} p with mod-of-𝐒 {a}{𝐒 m} | mod-of-𝐒 {b}{𝐒 m}
... | [∨]-introₗ pa | [∨]-introₗ pb = pa 🝖 congruence₁(𝐒) p 🝖 symmetry(_≡_) pb
... | [∨]-introₗ pa | [∨]-introᵣ pb = {!pa 🝖 congruence₁(𝐒) p!}
... | [∨]-introᵣ pa | [∨]-introₗ pb = pa 🝖 {!!} 🝖 symmetry(_≡_) pb
... | [∨]-introᵣ pa | [∨]-introᵣ pb = pa 🝖 symmetry(_≡_) pb-}
{-mod-congruence-with-𝐒 {𝟎} {𝟎} {𝐒 m} p = [≡]-intro
mod-congruence-with-𝐒 {𝟎} {𝐒 b} {𝐒 m} p = {!!}
mod-congruence-with-𝐒 {𝐒 a} {𝟎} {𝐒 m} p = {!!}
mod-congruence-with-𝐒 {𝐒 a} {𝐒 b} {𝐒 m} p = {!!}-}
{-mod-congruence-without-𝐒 {𝟎}   {𝟎}   {𝐒 m} p = [≡]-intro
mod-congruence-without-𝐒 {𝟎}   {𝐒 b} {𝐒 m} p = {!!}
mod-congruence-without-𝐒 {𝐒 a} {𝟎}   {𝐒 m} p = {!!}
mod-congruence-without-𝐒 {𝐒 a} {𝐒 b} {𝐒 m} p = {!!}-}

{-
-- TODO: Use Structure.Arithmetic instead of the actual ℕ (without the induction principle). Then ℕ with (𝟎 , 𝐒) fulfills such a structure (hom is id), but also ℕ with (a , 𝐒) for any a (hom is (a +_)). Or maybe ℕ with (𝟎 , (a +_)) (hom is (a ⋅_)), or ℕ with (1 , (a ⋅_)). Though this will not help mod-congruence-linear because addition and modulo for example in this new structure also changes.
record Homomorphism(f : ℕ → ℕ) : Type{Lvl.𝟎} where
  field
    preserves-𝟎 : (f(𝟎) ≡ 𝟎)
    preserves-𝐒 : ∀{n} → (f(𝐒(n)) ≡ 𝐒(f(n)))

  preserves-[+] : ∀{a b} → (f(a + b) ≡ f(a) + f(b))
  preserves-[+] {a} {𝟎} = symmetry(_≡_) (congruence₂-₂(_+_)(f(a)) preserves-𝟎)
  preserves-[+] {a} {𝐒 b} = preserves-𝐒 🝖 congruence₁(𝐒) (preserves-[+] {a} {b}) 🝖 congruence₂-₂(_+_)(f(a)) (symmetry(_≡_) preserves-𝐒)

  preserves-[⋅]ₗ : ∀{a b} → (f(a ⋅ b) ≡ f(a) ⋅ b)
  preserves-[⋅]ₗ {a} {𝟎} = preserves-𝟎
  preserves-[⋅]ₗ {a} {𝐒 b} = preserves-[+] {a}{a ⋅ b} 🝖 congruence₂-₂(_+_)(f(a)) (preserves-[⋅]ₗ {a}{b})

  preserves-[−₀] : ∀{a b} → (f(a −₀ b) ≡ f(a) −₀ f(b))
  preserves-[−₀] {𝟎} {b} = preserves-𝟎 🝖 congruence₂-₁(_−₀_)(f(b)) (symmetry(_≡_) preserves-𝟎)
  preserves-[−₀] {𝐒 a} {𝟎} = congruence₂-₂(_−₀_)(f(𝐒(a))) (symmetry(_≡_) preserves-𝟎)
  preserves-[−₀] {𝐒 a} {𝐒 b} = preserves-[−₀] {a} {b} 🝖 symmetry(_≡_) (congruence₂(_−₀_) (preserves-𝐒{a}) (preserves-𝐒{b}))

  -- TODO: But we also need to prove that floored division is a function without mentioning modulo (otherwise, circle argument). Below is the proof of modulo being a function depending on floored division being a function

open import Syntax.Implication
mod-congruence-linear : ∀{a b m} ⦃ pos : Positive(m) ⦄ {f : ℕ → ℕ} ⦃ hom-f : Homomorphism(f) ⦄ → (a mod m ≡ b mod m) → (f(a) mod m ≡ f(b) mod m)
mod-congruence-linear {a}{b}{𝐒 m}{f} ⦃ hom-f ⦄ =
  a mod 𝐒(m) ≡ b mod 𝐒(m)                                         ⇒-[ (p ↦ symmetry(_≡_) ([⌊/⌋][⋅]-inverseOperatorᵣ-error{a}{m}) 🝖 p 🝖 [⌊/⌋][⋅]-inverseOperatorᵣ-error{b}{𝐒 m}) ]
  a −₀ (a ⌊/⌋ 𝐒(m) ⋅ 𝐒(m)) ≡ b −₀ (b ⌊/⌋ 𝐒(m) ⋅ 𝐒(m))             ⇒-[ congruence₁(f) ]
  f(a −₀ (a ⌊/⌋ 𝐒(m) ⋅ 𝐒(m))) ≡ f(b −₀ (b ⌊/⌋ 𝐒(m) ⋅ 𝐒(m)))       ⇒-[ {!!} ]
  f(a) −₀ f(a ⌊/⌋ 𝐒(m) ⋅ 𝐒(m)) ≡ f(b) −₀ f(b ⌊/⌋ 𝐒(m) ⋅ 𝐒(m))     ⇒-[ {!!} ]
  f(a) −₀ (f(a ⌊/⌋ 𝐒(m)) ⋅ 𝐒(m)) ≡ f(b) −₀ (f(b ⌊/⌋ 𝐒(m)) ⋅ 𝐒(m)) ⇒-[ {!!} ]
  f(a) −₀ (f(a) ⌊/⌋ 𝐒(m) ⋅ 𝐒(m)) ≡ f(b) −₀ (f(b) ⌊/⌋ 𝐒(m) ⋅ 𝐒(m)) ⇒-[ {!!} ]
  f(a) mod 𝐒(m) ≡ f(b) mod 𝐒(m)                                   ⇒-end
  where
    open Homomorphism(hom-f)
-}

postulate [⋅][mod]-distributivityₗ : ∀{a b c} → (c ⋅ (a mod₀ b) ≡ ((c ⋅ a) mod₀ (c ⋅ b)))
{-[⋅][mod]-distributivityₗ {𝟎}   {𝟎}   {𝟎}   = [≡]-intro
[⋅][mod]-distributivityₗ {𝟎}   {𝟎}   {𝐒 c} = [≡]-intro
[⋅][mod]-distributivityₗ {𝟎}   {𝐒 b} {𝟎}   = [≡]-intro
[⋅][mod]-distributivityₗ {𝟎}   {𝐒 b} {𝐒 c} = [≡]-intro
[⋅][mod]-distributivityₗ {𝐒 a} {𝟎}   {𝟎}   = [≡]-intro
[⋅][mod]-distributivityₗ {𝐒 a} {𝟎}   {𝐒 c} = [≡]-intro
[⋅][mod]-distributivityₗ {𝐒 a} {𝐒 b} {𝟎}   = [≡]-intro
[⋅][mod]-distributivityₗ {𝐒 a} {𝐒 b} {𝐒 c} = ?-}
{- TODO: Above is true. Prove using the division theorem
(((c ⋅ a) / (c ⋅ b)) ⋅ (c ⋅ b)) + ((c ⋅ a) mod₀ (c ⋅ b)) ≡ c ⋅ a //Division theorem on (c ⋅ a)
  (((c ⋅ a) / (c ⋅ b)) ⋅ (c ⋅ b)) + (c ⋅ (a mod₀ b)) ≡
  ((a / b) ⋅ (c ⋅ b)) + (c ⋅ (a mod₀ b)) ≡ //a/b = (c⋅a)/(c⋅b)
  (c ⋅ ((a / b) ⋅ b)) + (c ⋅ (a mod₀ b)) ≡ //Commuting and associating ⋅
  c ⋅ ((a / b) ⋅ b) + (a mod₀ b) ≡ c ⋅ a //...equal to LHS here by distributivity of (_⋅_) over (_+_), and this identity is division theorem on a with congruenced (c ⋅_)
  ((a / b) ⋅ b) + (a mod₀ b) ≡ a-}

{-
mod-equality-diff : ∀{a b m} → (a mod 𝐒(m) ≡ b mod 𝐒(m)) → ((a 𝄩 b) mod 𝐒(m) ≡ 𝟎)
mod-equality-diff {𝟎}   {𝟎}   {m} ab = [≡]-intro
mod-equality-diff {𝟎}   {𝐒 b} {m} ab = symmetry(_≡_) ab
mod-equality-diff {𝐒 a} {𝟎}   {m} ab = ab
mod-equality-diff {𝐒 a} {𝐒 b} {m} ab = mod-equality-diff {a} {b} {m} {!!}
-}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- mod₀

{-
-- mod₀-eq-predecessor : ∀{a b} → ((𝐒(a) mod₀ b) ≡ 𝐒(c)) → ((a mod₀ b) ≡ c)

postulate mod₀-of-𝐒 : ∀{a b} → (𝐒(a) mod₀ b ≡ 𝟎) ∨ (𝐒(a) mod₀ b ≡ 𝐒(a mod₀ b))

-- TODO: Should also be satisfied for b, not just 𝐒(b)
-- mod₀-of-modulus-pre-eq : ∀{a b} → (𝐒(a) mod₀ 𝐒(b) ≡ 𝟎) → (a mod₀ 𝐒(b) ≡ b)
-- mod₀-of-modulus-pre-eq : ∀{a b} → (𝐒(a) mod₀ 𝐒(b) ≡ 𝐒(c)) → (a mod₀ 𝐒(b) ≡ c)

postulate mod₀-[⋅]ₗ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (((k ⋅ a) mod₀ c) ≡ ((k ⋅ b) mod₀ c))
postulate mod₀-[⋅]ᵣ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (((a ⋅ k) mod₀ c) ≡ ((b ⋅ k) mod₀ c))
postulate mod₀-[⋅]-equality : ∀{a₁ b₁ a₂ b₂ c} → ((a₁ mod₀ c) ≡ (b₁ mod₀ c)) → ((a₂ mod₀ c) ≡ (b₂ mod₀ c)) → (((a₁ ⋅ a₂) mod₀ c) ≡ ((b₁ ⋅ b₂) mod₀ c))

-- postulate mod₀-[^]ᵣ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (((a ^ k) mod₀ c) ≡ ((b ^ k) mod₀ c))

-- postulate mod₀-[/]ₗ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) → (k ∣ a) → (k ∣ b) → (((k / a) mod₀ c) ≡ ((k / b) mod₀ c))
-- postulate mod₀-[/]ᵣ-equality : ∀{a b k c} → ((a mod₀ c) ≡ (b mod₀ c)) ∧ (k ∣ a) ∧ (k ∣ b) ← (((a / k) mod₀ c) ≡ ((b / k) mod₀ c))

-- postulate modulo-multiplication : ∀{a₁ a₂ b} → (((a₁ ⋅ a₂) mod₀ b) ≡ (((a₁ mod₀ b) ⋅ (a₂ mod₀ b)) mod₀ b))


-}
