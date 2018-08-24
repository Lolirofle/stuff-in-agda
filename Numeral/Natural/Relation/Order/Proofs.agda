module Numeral.Natural.Relation.Order.Proofs{ℓ} where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Induction{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
import      Numeral.Natural.Relation.Order.Existence         {ℓ} as [≤∃]
open import Numeral.Natural.Relation.Order.Existence.Proofs{ℓ} using () renaming ([≤]-with-[𝐒] to [≤∃]-with-[𝐒])
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

-- TODO: The instance declarations probably do nothing for functions with arguments. Either make all the args implicit or remove the instance decls.
-- TODO: A method for pattern matching: https://stackoverflow.com/questions/20682013/agda-why-am-i-unable-to-pattern-match-on-refl

[≤]-equivalence : ∀{x y} → (x [≤∃].≤ y) ↔ (x ≤ y)
[≤]-equivalence{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x [≤∃].≤ y) ← (x ≤ y)
  l{𝟎}   {y}    ([≤]-minimum)      = [∃]-intro(y) ⦃ [≡]-intro ⦄
  l{𝐒(x)}{𝟎}    ()
  l{𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [≤∃]-with-[𝐒] {x}{y} (l{x}{y} (proof))

  r : ∀{x y} → (x [≤∃].≤ y) → (x ≤ y)
  r{𝟎}   {y}    ([∃]-intro(z) ⦃ 𝟎+z≡y   ⦄) = [≤]-minimum
  r{𝐒(x)}{𝟎}    ([∃]-intro(z) ⦃ ⦄)
  r{𝐒(x)}{𝐒(y)} ([∃]-intro(z) ⦃ 𝐒x+z≡𝐒y ⦄) = [≤]-with-[𝐒] ⦃ r{x}{y} ([∃]-intro(z) ⦃ [𝐒]-injectivity(𝐒x+z≡𝐒y) ⦄ ) ⦄

[≤]-from-[≡] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≤]-from-[≡] {𝟎}   {_}    ([≡]-intro) = [≤]-minimum
[≤]-from-[≡] {𝐒(x)}{𝐒(y)} ([≡]-intro) = [≤]-with-[𝐒] ⦃ [≤]-from-[≡] {x}{y} ([≡]-intro) ⦄

[≤][0]ᵣ : ∀{x : ℕ} → (x ≤ 0) → (x ≡ 0)
[≤][0]ᵣ {𝟎}    (_) = [≡]-intro
[≤][0]ᵣ {𝐒(_)} ()

[≤][0]ᵣ-negation : ∀{x : ℕ} → (𝐒(x) ≰ 0)
[≤][0]ᵣ-negation ()

[≤]-successor : ∀{x y : ℕ} → (x ≤ y) → (x ≤ 𝐒(y))
[≤]-successor {𝟎}   {_}    (_) = [≤]-minimum
[≤]-successor {𝐒(x)}{𝟎}    ()
[≤]-successor {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [≤]-with-[𝐒] ⦃ [≤]-successor {x}{y} (proof) ⦄

[≤]-predecessor : ∀{x y : ℕ} → (𝐒(x) ≤ y) → (x ≤ y)
[≤]-predecessor {x}   {𝟎}    ()
[≤]-predecessor {𝟎}   {𝐒(y)} (_) = [≤]-minimum
[≤]-predecessor {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [≤]-with-[𝐒] ⦃ [≤]-predecessor {x}{y} (proof) ⦄

[≤]-without-[𝐒] : ∀{x y : ℕ} → (𝐒(x) ≤ 𝐒(y)) → (x ≤ y)
[≤]-without-[𝐒] ([≤]-with-[𝐒] ⦃ proof ⦄) = proof

[≤][𝐒]ₗ : ∀{x : ℕ} → ¬(𝐒(x) ≤ x)
[≤][𝐒]ₗ {𝟎}    (1≤0)    = [≤][0]ᵣ-negation{0}(1≤0)
[≤][𝐒]ₗ {𝐒(n)} (SSn≤Sn) = [≤][𝐒]ₗ {n} ([≤]-without-[𝐒] {𝐒(n)}{n} (SSn≤Sn))

[≤]-with-[+]ᵣ : ∀{x y z : ℕ} → (x ≤ y) → (x + z ≤ y + z)
[≤]-with-[+]ᵣ {_}{_}{𝟎}    (proof)    = proof
[≤]-with-[+]ᵣ {_}{_}{𝐒(z)} (proof) = [≤]-with-[𝐒] ⦃ [≤]-with-[+]ᵣ {_}{_}{z} (proof) ⦄

-- [≤]-with-[+]ₗ : ∀{x y z : ℕ} → (x ≤ y) → (z + x ≤ z + y)
-- TODO: [≤]-with-[+] : ∀{x₁ y₁ : ℕ} → (x₁ ≤ y₁) → ∀{x₂ y₂ : ℕ} → (x₂ ≤ y₂) → (x₁ + x₂ ≤ y₁ + y₂)

[≤]ₗ[+] : ∀{x y : ℕ} → (x + y ≤ x) → (y ≡ 𝟎)
[≤]ₗ[+] {𝟎}               = [≤][0]ᵣ
[≤]ₗ[+] {𝐒(x)}{y} (proof) = [≤]ₗ[+] {x} ([≤]-without-[𝐒] {x + y} {x} (proof))

instance
  [≤]-reflexivity : Reflexivity (_≤_)
  reflexivity ⦃ [≤]-reflexivity ⦄ = [≤]-from-[≡] [≡]-intro

instance
  [≤]-transitivity : Transitivity (_≤_)
  transitivity ⦃ [≤]-transitivity ⦄ {𝟎}   {_}   {_} (_)(_) = [≤]-minimum
  transitivity ⦃ [≤]-transitivity ⦄ {𝐒(a)}{𝐒(b)}{𝐒(c)} ([≤]-with-[𝐒] ⦃ proofₗ ⦄) ([≤]-with-[𝐒] ⦃ proofᵣ ⦄ ) =
    [≤]-with-[𝐒] ⦃ transitivity ⦃ [≤]-transitivity ⦄ {a}{b}{c} (proofₗ) (proofᵣ) ⦄

instance
  [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {𝟎}    {𝟎}    (_) (_) = [≡]-intro
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {𝐒(_)} {𝟎}    ()
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {𝟎}    {𝐒(_)} (_) ()
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {𝐒(a)} {𝐒(b)} ([≤]-with-[𝐒] ⦃ proofₗ ⦄) ([≤]-with-[𝐒] ⦃ proofᵣ ⦄) =
    [≡]-with(𝐒) (antisymmetry ⦃ [≤]-antisymmetry ⦄ {a}{b} proofₗ proofᵣ)

instance
  [≤]-totality : ConverseTotal(_≤_)
  converseTotal ⦃ [≤]-totality ⦄ {𝟎}   {𝟎}    = [∨]-introₗ ([≤]-from-[≡] [≡]-intro)
  converseTotal ⦃ [≤]-totality ⦄ {𝐒(a)}{𝟎}    = [∨]-introᵣ ([≤]-minimum)
  converseTotal ⦃ [≤]-totality ⦄ {𝟎}   {𝐒(b)} = [∨]-introₗ ([≤]-minimum)
  converseTotal ⦃ [≤]-totality ⦄ {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ (proof ↦ [≤]-with-[𝐒] {a}{b} ⦃ proof ⦄)) ([∨]-introᵣ ∘ (proof ↦ [≤]-with-[𝐒] {b}{a} ⦃ proof ⦄)) (converseTotal ⦃ [≤]-totality ⦄ {a}{b})

instance
  [≤]-weakOrder : Weak.TotalOrder (_≤_) (_≡_)
  [≤]-weakOrder = record{
      partialOrder = record{
          antisymmetry = [≤]-antisymmetry;
          transitivity = [≤]-transitivity;
          reflexivity  = [≤]-reflexivity
        };
      totality = [≤]-totality
    }

[≥]-to-[≮] : ∀{a b : ℕ} → (a ≮ b) ← (a ≥ b)
[≥]-to-[≮] {a}{b} (b≤a) (𝐒a≤b) = [≤][𝐒]ₗ (transitivity {_}{_}{𝐒(a)}{b}{a} (𝐒a≤b) (b≤a))

[≤]-to-[≯] : ∀{a b : ℕ} → (a ≯ b) ← (a ≤ b)
[≤]-to-[≯] {a}{b} (a≤b) (𝐒b≤a) = [≥]-to-[≮] {b}{a} (a≤b) (𝐒b≤a)

[>]-to-[≰] : ∀{a b : ℕ} → (a ≰ b) ← (a > b)
[>]-to-[≰] {a}{b} (𝐒b≤a) (a≤b) = [≤]-to-[≯] (a≤b) (𝐒b≤a)

[<]-to-[≱] : ∀{a b : ℕ} → (a ≱ b) ← (a < b)
[<]-to-[≱] {a}{b} (𝐒a≤b) (b≤a) = [≥]-to-[≮] (b≤a) (𝐒a≤b)



[<][0]ᵣ : ∀{x : ℕ} → (x ≮ 0)
[<][0]ᵣ = [≤][0]ᵣ-negation

instance
  [<]-irreflexivity : Irreflexivity (_<_)
  irreflexivity ⦃ [<]-irreflexivity ⦄ = [≤][𝐒]ₗ

instance
  [<]-transitivity : Transitivity (_<_)
  transitivity ⦃ [<]-transitivity ⦄ {x}{y}{z} (l) (r) = transitivity ⦃ [≤]-transitivity ⦄ {𝐒(x)} {𝐒(y)} {z} ([≤]-successor (l)) (r)

instance
  [<]-asymmetry : Asymmetry (_<_)
  asymmetry ⦃ [<]-asymmetry ⦄ (l) (r) = irreflexivity ⦃ [<]-irreflexivity ⦄ (transitivity ⦃ [<]-transitivity ⦄ (l) (r))

instance
  [<]-strictOrder : Strict.Order (_<_)
  [<]-strictOrder = record{
      transitivity  = [<]-transitivity;
      asymmetry     = [<]-asymmetry;
      irreflexivity = [<]-irreflexivity
    }

[<]-minimum : ∀{x : ℕ} → (0 < 𝐒(x))
[<]-minimum {x} = [≤]-with-[𝐒] {0} ⦃ [≤]-minimum ⦄

[<]-of-[𝐒] : ∀{x : ℕ} → (x < 𝐒(x))
[<]-of-[𝐒] = reflexivity ⦃ [≤]-reflexivity ⦄

[≤]-of-[𝐒] : ∀{x : ℕ} → (x ≤ 𝐒(x))
[≤]-of-[𝐒] = [≤]-successor(reflexivity)

[<][≢]-equivalence : ∀{x} → (x > 0) ↔ (x ≢ 0)
[<][≢]-equivalence {x} = [↔]-intro (l{x}) (r{x}) where
  l : ∀{x} → (x > 0) ← (x ≢ 0)
  l{𝟎}    (x≢𝟎)  = [⊥]-elim((x≢𝟎)([≡]-intro))
  l{𝐒(x)} (𝐒x≢𝟎) = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄

  r : ∀{x} → (x > 0) → (x ≢ 0)
  r{𝟎}    ()
  r{𝐒(x)} (𝟏≤𝐒x) (𝐒x≡𝟎) with [≡]-substitutionᵣ (𝐒x≡𝟎) {expr ↦ 1 ≤ expr} (𝟏≤𝐒x)
  ... | ()



[≤]-to-[<][≡] : ∀{a b : ℕ} → (a ≤ b) → (a < b)∨(a ≡ b)
[≤]-to-[<][≡] {𝟎}   {𝟎}    ([≤]-minimum)    = [∨]-introᵣ([≡]-intro)
[≤]-to-[<][≡] {𝟎}   {𝐒(b)} ([≤]-minimum)    = [∨]-introₗ([<]-minimum)
[≤]-to-[<][≡] {𝐒(a)}{𝐒(b)} ([≤]-with-[𝐒] ⦃ a≤b ⦄) with [≤]-to-[<][≡] {a}{b} (a≤b)
... | [∨]-introₗ(a<b) = [∨]-introₗ([≤]-with-[𝐒] ⦃ a<b ⦄)
... | [∨]-introᵣ(a≡b) = [∨]-introᵣ([≡]-with(𝐒) (a≡b))

[<][≡]-to-[≤] : ∀{a b : ℕ} → (a < b)∨(a ≡ b) → (a ≤ b)
[<][≡]-to-[≤] {a}   {.a}   ([∨]-introᵣ([≡]-intro)) = [≤]-from-[≡] ([≡]-intro)
[<][≡]-to-[≤] {a}   {b}    ([∨]-introₗ(a<b))       = [≤]-predecessor (a<b)

[≥]-to-[>][≡] : ∀{a b : ℕ} → (a ≥ b) → (a > b)∨(a ≡ b)
[≥]-to-[>][≡] {a}{b} (proof) with [≤]-to-[<][≡] {b}{a} (proof)
... | [∨]-introₗ(a<b) = [∨]-introₗ(a<b)
... | [∨]-introᵣ(b≡a) = [∨]-introᵣ(symmetry(b≡a))

[>][≡]-to-[≥] : ∀{a b : ℕ} → (a > b)∨(a ≡ b) → (a ≥ b)
[>][≡]-to-[≥] {a}{b} ([∨]-introₗ(a<b)) = [<][≡]-to-[≤] {b}{a} ([∨]-introₗ(a<b))
[>][≡]-to-[≥] {a}{b} ([∨]-introᵣ(b≡a)) = [<][≡]-to-[≤] {b}{a} ([∨]-introᵣ(symmetry(b≡a)))

[−₀]-lesser-[𝐒]ₗ : ∀{x y} → ((x −₀ 𝐒(y)) ≤ (x −₀ y))
[−₀]-lesser-[𝐒]ᵣ : ∀{x y} → ((x −₀ y) ≤ (𝐒(x) −₀ y))

[−₀]-lesser-[𝐒]ₗ {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser-[𝐒]ₗ {𝐒(_)}{𝟎}    = [≤]-of-[𝐒]
[−₀]-lesser-[𝐒]ₗ {𝐒(x)}{𝐒(y)} = [−₀]-lesser-[𝐒]ᵣ {x}{𝐒(y)}

[−₀]-lesser-[𝐒]ᵣ {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser-[𝐒]ᵣ {𝐒(x)}{𝟎}    = [≤]-of-[𝐒]
[−₀]-lesser-[𝐒]ᵣ {𝐒(x)}{𝐒(y)} = [−₀]-lesser-[𝐒]ₗ {𝐒(x)}{y}

[≤][−₀][𝐒]ₗ : ∀{x y} → ((𝐒(x) −₀ y) ≤ 𝐒(x −₀ y))
[≤][−₀][𝐒]ₗ {x}   {𝟎}    = reflexivity
[≤][−₀][𝐒]ₗ {𝟎}   {𝐒(y)} = [≤]-minimum
[≤][−₀][𝐒]ₗ {𝐒(x)}{𝐒(y)} = [≤][−₀][𝐒]ₗ {x}{y}

[−₀]-lesser : ∀{x y} → ((x −₀ y) ≤ x)
[−₀]-lesser {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser {𝐒(x)}{𝟎}    = reflexivity
[−₀]-lesser {𝐒(x)}{𝐒(y)} = ([−₀]-lesser-[𝐒]ₗ {𝐒(x)}{y}) 🝖 ([−₀]-lesser {𝐒(x)}{y})

[−₀]-positive : ∀{x y} → (y > x) → (y −₀ x > 0) -- TODO: Converse is probably true too
[−₀]-positive {𝟎}   {𝟎}    ()
[−₀]-positive {𝐒(x)}{𝟎}    ()
[−₀]-positive {𝟎}   {𝐒(y)} (_) = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
[−₀]-positive {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [−₀]-positive {x}{y} (proof)
  -- (𝐒y > 𝐒x) → (𝐒y −₀ 𝐒x > 0)
  -- (𝐒x < 𝐒y) → (0 < 𝐒y −₀ 𝐒x)
  -- (𝐒𝐒x ≤ 𝐒y) → (𝐒0 ≤ 𝐒y −₀ 𝐒x)
  -- (𝐒x ≤ y) → (𝐒0 ≤ 𝐒y −₀ 𝐒x)
  -- (𝐒x ≤ y) → (𝐒0 ≤ y −₀ x)
  -- (x < y) → (0 < y −₀ x)
  -- (y > x) → (y −₀ x > 0)

 -- [≤]-with-[𝐒]

-- TODO: Prove using contraposition of [−₀]-positive. Negation of (>) is to be proven to be (≤), and then (≤0) is (≡0) by [≤][0]ᵣ
-- [−₀]-is-zero : ∀{x y} → (y −₀ x ≡ 0) → (y ≤ x)
