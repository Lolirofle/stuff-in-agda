module Numeral.Natural.Relation.Divisibility.Proofs.FlooredDivision where

import Lvl
open import Data
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Natural
open import Numeral.Natural.Induction
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv

-- Alternative proof:
--   divides-[⌊/⌋] : ∀{a b c} ⦃ pos : Positive(c) ⦄ → (c ∣ a) → (a ∣ b) → ((a ⌊/⌋ c) ∣ (b ⌊/⌋ c))
--   divides-[⌊/⌋] {a}{b}{c} ca ab =
--     let [∃]-intro n ⦃ eq ⦄ = [↔]-to-[←] divides-[⋅]-existence ab
--     in [↔]-to-[→] divides-[⋅]-existence ([∃]-intro n ⦃ symmetry(_≡_) ([⌊/⌋][⋅]ₗ-compatibility {a}{n}{c} ca) 🝖 congruence₁(_⌊/⌋ c) eq ⦄)
module _
  {a b d}
  ⦃ pos-abd : Positive(a) ∨ Positive(b) ∨ Positive(d) ⦄
  (da : d ∣ a)
  (ab : a ∣ b)
  (let
    instance
      pos-d : Positive(d)
      pos-d = [∨]-elim ([∨]-elim (divides-positive da) (divides-positive da ∘ divides-positive ab)) id pos-abd
  )
  where

  divides-with-[⌊/⌋] : (a ⌊/⌋ d) ∣ (b ⌊/⌋ d)
  divides-with-[⌊/⌋] = divides-without-[⋅]ᵣ-both' {a ⌊/⌋ d}{b ⌊/⌋ d}{d}
    (substitute₂ₗ(_∣_)
      ([⋅][⌊/⌋]-inverseOperatorᵣ da)
      ([⋅][⌊/⌋]-inverseOperatorᵣ (da 🝖 ab))
      ab
    )

module _
  {a b d}
  ⦃ pos-abd : Positive(a) ∨ Positive(b) ∨ Positive(d) ⦄
  (da : d ∣ a)
  (db : d ∣ b)
  (let
    instance
      pos-d : Positive(d)
      pos-d = [∨]-elim ([∨]-elim (divides-positive da) (divides-positive db)) id pos-abd
  )
  (adbd : (a ⌊/⌋ d) ∣ (b ⌊/⌋ d))
  where

  divides-without-[⌊/⌋] : a ∣ b
  divides-without-[⌊/⌋] = substitute₂ᵣ(_∣_)
    ([⋅][⌊/⌋]-inverseOperatorᵣ da)
    ([⋅][⌊/⌋]-inverseOperatorᵣ db)
    (divides-with-[⋅]ᵣ-both {a ⌊/⌋ d}{b ⌊/⌋ d}{d} adbd)

module _
  {a b c}
  ⦃ pos-bc : Positive(b) ∨ Positive(c) ⦄
  (cab : (c ⋅ a) ∣ b)
  (let
    instance
      pos-c : Positive(c)
      pos-c = [∨]-elim ([∧]-elimₗ ∘ [↔]-to-[←] ([⋅]-positive {b = a}) ∘ divides-positive cab) id pos-bc
  )
  where

  divides-[⋅]ₗ⌊/⌋-transferᵣ : a ∣ (b ⌊/⌋ c)
  divides-[⋅]ₗ⌊/⌋-transferᵣ = substitute₂-₁ᵣ(_∣_) _
    ([⌊/⌋][swap⋅]-inverseOperatorᵣ {c}{a})
    (divides-with-[⌊/⌋] {c ⋅ a}{b}{c}
      ⦃ [∨]-elim ([∨]-introₗ ∘ [∨]-introᵣ) [∨]-introᵣ pos-bc ⦄
      (divides-with-[⋅] {c}{c}{a} ([∨]-introₗ (reflexivity(_∣_))))
      cab
    )

module _
  {b c a}
  ⦃ pos-bc : Positive(b) ∨ Positive(c) ⦄
  (acb : (a ⋅ c) ∣ b)
  (let
    instance
      pos-c : Positive(c)
      pos-c = [∨]-elim ([∧]-elimᵣ ∘ [↔]-to-[←] ([⋅]-positive {a = a}) ∘ divides-positive acb) id pos-bc
  )
  where

  divides-[⋅]ᵣ⌊/⌋-transferᵣ : a ∣ (b ⌊/⌋ c)
  divides-[⋅]ᵣ⌊/⌋-transferᵣ = substitute₂-₁ᵣ(_∣_) _
    ([⌊/⌋][⋅]-inverseOperatorᵣ {a}{c})
    (divides-with-[⌊/⌋] {a ⋅ c}{b}{c}
      ⦃ [∨]-elim ([∨]-introₗ ∘ [∨]-introᵣ) [∨]-introᵣ pos-bc ⦄
      (divides-with-[⋅] {c}{a}{c} ([∨]-introᵣ (reflexivity(_∣_))))
      acb
    )

module _
  {a b}
  ⦃ pos-ab : Positive(a) ∨ Positive(b) ⦄
  (ba : b ∣ a)
  (let
    instance
      pos-b : Positive(b)
      pos-b = [∨]-elim (divides-positive ba) id pos-ab
  )
  where

  divides-[⋅]ᵣ⌊/⌋-transfer : ∀{c} → ((c ⋅ b) ∣ a) ↔ (c ∣ (a ⌊/⌋ b))
  divides-[⋅]ᵣ⌊/⌋-transfer{c} = [↔]-intro
    (substitute₂-₂ᵣ(_∣_) _ ([⋅][⌊/⌋]-inverseOperatorᵣ ba) ∘ divides-with-[⋅]ᵣ-both {z = b})
    divides-[⋅]ᵣ⌊/⌋-transferᵣ

  divides-[⋅]ₗ⌊/⌋-transfer : ∀{c} → ((b ⋅ c) ∣ a) ↔ (c ∣ (a ⌊/⌋ b))
  divides-[⋅]ₗ⌊/⌋-transfer{c} = [↔]-intro
    (substitute₂-₂ᵣ(_∣_) _ ([⋅][⌊/⌋]-inverseOperatorₗ ba) ∘ divides-with-[⋅]ₗ-both {z = b})
    divides-[⋅]ₗ⌊/⌋-transferᵣ

  divides-withoutᵣ-⌊/⌋ : ∀{c} → (c ∣ (a ⌊/⌋ b)) → (c ∣ a)
  divides-withoutᵣ-⌊/⌋ cab = substitute₂-₂ᵣ(_∣_) _ ([⋅][⌊/⌋]-inverseOperatorᵣ ba) (divides-with-[⋅] {c = b} ([∨]-introₗ cab))

  dividesₗ-div : (a ⌊/⌋ b) ∣ a
  dividesₗ-div = divides-withoutᵣ-⌊/⌋ {a ⌊/⌋ b} (reflexivity(_∣_))

  divides-⌊/⌋[⋅]ₗ-transfer : ∀{c} → ((a ⌊/⌋ b) ∣ c) ↔ (a ∣ (b ⋅ c))
  divides-⌊/⌋[⋅]ₗ-transfer{c} = [↔]-intro
    (divides-without-[⋅]ₗ-both' {z = b} ∘ substitute₂-₁ₗ(_∣_)(_) ([⋅][⌊/⌋]-inverseOperatorₗ ba))
    (substitute₂-₁ᵣ(_∣_)(_) ([⋅][⌊/⌋]-inverseOperatorₗ ba) ∘ divides-with-[⋅]ₗ-both {z = b})

  divides-⌊/⌋[⋅]ᵣ-transfer : ∀{c} → ((a ⌊/⌋ b) ∣ c) ↔ (a ∣ (c ⋅ b))
  divides-⌊/⌋[⋅]ᵣ-transfer{c} = [↔]-intro
    (divides-without-[⋅]ᵣ-both' {z = b} ∘ substitute₂-₁ₗ(_∣_)(_) ([⋅][⌊/⌋]-inverseOperatorᵣ ba))
    (substitute₂-₁ᵣ(_∣_)(_) ([⋅][⌊/⌋]-inverseOperatorᵣ ba) ∘ divides-with-[⋅]ᵣ-both {z = b})



divides-with-[⌊/⌋₀] : ∀{a b d} → (d ∣ a) → (a ∣ b) → (a ⌊/⌋₀ d) ∣ (b ⌊/⌋₀ d)
divides-with-[⌊/⌋₀] {_} {_} {𝟎}   da ab = Div𝟎
divides-with-[⌊/⌋₀] {_} {_} {𝐒 d} da ab = divides-with-[⌊/⌋] ⦃ [∨]-introᵣ <> ⦄ da ab

divides-[⋅]ₗ⌊/⌋₀-transferᵣ : ∀{a b c} → (c ⋅ a ∣ b) → (a ∣ (b ⌊/⌋₀ c))
divides-[⋅]ₗ⌊/⌋₀-transferᵣ {c = 𝟎}   _   = Div𝟎
divides-[⋅]ₗ⌊/⌋₀-transferᵣ {c = 𝐒 _} cab = divides-[⋅]ₗ⌊/⌋-transferᵣ ⦃ [∨]-introᵣ <> ⦄ cab

divides-[⋅]ᵣ⌊/⌋₀-transferᵣ : ∀{a b c} → (a ⋅ c ∣ b) → (a ∣ (b ⌊/⌋₀ c))
divides-[⋅]ᵣ⌊/⌋₀-transferᵣ {c = 𝟎}   _   = Div𝟎
divides-[⋅]ᵣ⌊/⌋₀-transferᵣ {c = 𝐒 _} acb = divides-[⋅]ᵣ⌊/⌋-transferᵣ ⦃ [∨]-introᵣ <> ⦄ acb

divides-[⋅]ᵣ⌊/⌋₀-transfer : ∀{a b c} → (b ∣ a) → ((c ⋅ b) ∣ a) ↔ (c ∣ (a ⌊/⌋₀ b))
divides-[⋅]ᵣ⌊/⌋₀-transfer {a}   {𝐒 b} ba = divides-[⋅]ᵣ⌊/⌋-transfer ⦃ [∨]-introᵣ <> ⦄ ba
divides-[⋅]ᵣ⌊/⌋₀-transfer {𝟎}   {𝟎}   ba = [↔]-intro (const Div𝟎) (const Div𝟎)
divides-[⋅]ᵣ⌊/⌋₀-transfer {𝐒 a} {𝟎}   ba = [↔]-intro (const ba) (const Div𝟎)

divides-[⋅]ₗ⌊/⌋₀-transfer : ∀{a b c} → (b ∣ a) → ((b ⋅ c) ∣ a) ↔ (c ∣ (a ⌊/⌋₀ b))
divides-[⋅]ₗ⌊/⌋₀-transfer {a}   {𝐒 b} ba = divides-[⋅]ₗ⌊/⌋-transfer ⦃ [∨]-introᵣ <> ⦄ ba
divides-[⋅]ₗ⌊/⌋₀-transfer {𝟎}   {𝟎}   ba = [↔]-intro (const Div𝟎) (const Div𝟎)
divides-[⋅]ₗ⌊/⌋₀-transfer {𝐒 a} {𝟎}   ba = [↔]-intro (const ba) (const Div𝟎)

divides-⌊/⌋₀[⋅]ₗ-transfer : ∀{a b c} ⦃ pos-ab : Positive(a) ∨ Positive(b) ⦄ → (b ∣ a) → ((a ⌊/⌋₀ b) ∣ c) ↔ (a ∣ (b ⋅ c))
divides-⌊/⌋₀[⋅]ₗ-transfer {a}   {𝐒 b} ba = divides-⌊/⌋[⋅]ₗ-transfer ⦃ [∨]-introᵣ <> ⦄ ba
divides-⌊/⌋₀[⋅]ₗ-transfer {𝟎}   {𝟎}   ⦃ [∨]-introₗ () ⦄
divides-⌊/⌋₀[⋅]ₗ-transfer {𝟎}   {𝟎}   ⦃ [∨]-introᵣ () ⦄
divides-⌊/⌋₀[⋅]ₗ-transfer {𝐒 a} {𝟎}   ba with () ← [0]-divides-not ba

-- TODO: Maybe c can be 0 also (in addition to the cases in pos-ab)
divides-⌊/⌋₀[⋅]ᵣ-transfer : ∀{a b c} ⦃ pos-ab : Positive(a) ∨ Positive(b) ⦄ → (b ∣ a) → ((a ⌊/⌋₀ b) ∣ c) ↔ (a ∣ (c ⋅ b))
divides-⌊/⌋₀[⋅]ᵣ-transfer {a}   {𝐒 b} ba = divides-⌊/⌋[⋅]ᵣ-transfer ⦃ [∨]-introᵣ <> ⦄ ba
divides-⌊/⌋₀[⋅]ᵣ-transfer {𝟎}   {𝟎}   ⦃ [∨]-introₗ () ⦄
divides-⌊/⌋₀[⋅]ᵣ-transfer {𝟎}   {𝟎}   ⦃ [∨]-introᵣ () ⦄
divides-⌊/⌋₀[⋅]ᵣ-transfer {𝐒 a} {𝟎}   ba with () ← [0]-divides-not ba

dividesₗ-div₀ : ∀{a b} ⦃ pos-ab : Positive(a) ∨ Positive(b) ⦄ → (b ∣ a) → ((a ⌊/⌋₀ b) ∣ a)
dividesₗ-div₀ {b = 𝐒 b} = dividesₗ-div
dividesₗ-div₀ {𝟎}   {𝟎} ⦃ [∨]-introₗ () ⦄ ba
dividesₗ-div₀ {𝟎}   {𝟎} ⦃ [∨]-introᵣ () ⦄ ba
dividesₗ-div₀ {𝐒 a} {𝟎} = id
