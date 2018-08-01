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

[≤]-equivalence : ∀{x y} → (x [≤∃].≤ y) ↔ (x ≤ y)
[≤]-equivalence{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x [≤∃].≤ y) ← (x ≤ y)
  l{𝟎}   {y}    ([≤][0]ᵣ-minimum)      = [∃]-intro(y) ⦃ [≡]-intro ⦄
  l{𝐒(x)}{𝟎}    ()
  l{𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒](proof)) = [≤∃]-with-[𝐒] {x}{y} (l{x}{y} (proof))

  r : ∀{x y} → (x [≤∃].≤ y) → (x ≤ y)
  r{𝟎}   {y}    ([∃]-intro(z) ⦃ 𝟎+z≡y   ⦄) = [≤][0]ᵣ-minimum
  r{𝐒(x)}{𝟎}    ([∃]-intro(z) ⦃ ⦄)
  r{𝐒(x)}{𝐒(y)} ([∃]-intro(z) ⦃ 𝐒x+z≡𝐒y ⦄) = [≤]-with-[𝐒] (r{x}{y} ([∃]-intro(z) ⦃ [𝐒]-injectivity(𝐒x+z≡𝐒y) ⦄))

instance
  [≤]-from-[≡] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
  [≤]-from-[≡] {𝟎}   {_}    ([≡]-intro) = [≤][0]ᵣ-minimum
  [≤]-from-[≡] {𝐒(x)}{𝐒(y)} ([≡]-intro) = [≤]-with-[𝐒] ([≤]-from-[≡] {x}{y} ([≡]-intro))

instance
  [≤][0]ᵣ : ∀{x : ℕ} → (x ≤ 0) → (x ≡ 0)
  [≤][0]ᵣ {𝟎}    (_) = [≡]-intro
  [≤][0]ᵣ {𝐒(_)} ()

instance
  [≤][0]ᵣ-negation : ∀{x : ℕ} → ¬(𝐒(x) ≤ 0)
  [≤][0]ᵣ-negation ()

instance
  [≤]-successor : ∀{x y : ℕ} → (x ≤ y) → (x ≤ 𝐒(y))
  [≤]-successor {𝟎}   {_}    (_) = [≤][0]ᵣ-minimum
  [≤]-successor {𝐒(x)}{𝟎}    ()
  [≤]-successor {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] (proof)) = [≤]-with-[𝐒] ([≤]-successor {x}{y} (proof))

instance
  [≤]-predecessor : ∀{x y : ℕ} → (𝐒(x) ≤ y) → (x ≤ y)
  [≤]-predecessor {x}   {𝟎}    ()
  [≤]-predecessor {𝟎}   {𝐒(y)} (_) = [≤][0]ᵣ-minimum
  [≤]-predecessor {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] (proof)) = [≤]-with-[𝐒] ([≤]-predecessor {x}{y} (proof))

instance
  [≤]-without-[𝐒] : ∀{x y : ℕ} → (𝐒(x) ≤ 𝐒(y)) → (x ≤ y)
  [≤]-without-[𝐒] ([≤]-with-[𝐒] (proof)) = proof

instance
  [≤][𝐒]ₗ : ∀{x : ℕ} → ¬(𝐒(x) ≤ x)
  [≤][𝐒]ₗ {𝟎}    (1≤0)    = [≤][0]ᵣ-negation{0}(1≤0)
  [≤][𝐒]ₗ {𝐒(n)} (SSn≤Sn) = [≤][𝐒]ₗ {n} ([≤]-without-[𝐒] {𝐒(n)}{n} (SSn≤Sn))

instance
  [≤]-reflexivity : Reflexivity (_≤_)
  reflexivity ⦃ [≤]-reflexivity ⦄ = [≤]-from-[≡] [≡]-intro

instance
  [≤]-transitivity : Transitivity (_≤_)
  transitivity ⦃ [≤]-transitivity ⦄ {𝟎}   {_}   {_} (_)(_) = [≤][0]ᵣ-minimum
  transitivity ⦃ [≤]-transitivity ⦄ {𝐒(a)}{𝐒(b)}{𝐒(c)} ([≤]-with-[𝐒] (proofₗ)) ([≤]-with-[𝐒] (proofᵣ)) =
    [≤]-with-[𝐒] (transitivity ⦃ [≤]-transitivity ⦄ {a}{b}{c} (proofₗ) (proofᵣ))

instance
  [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {𝟎}    {𝟎}    (_) = [≡]-intro
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {𝐒(_)} {𝟎}    ()
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {𝟎}    {𝐒(_)} ()
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {𝐒(a)} {𝐒(b)} ([≤]-with-[𝐒] (proofₗ) , [≤]-with-[𝐒] (proofᵣ)) =
    [≡]-with(𝐒) (antisymmetry ⦃ [≤]-antisymmetry ⦄ {a}{b} (proofₗ , proofᵣ))

instance
  [≤]-totality : Total(_≤_)
  total ⦃ [≤]-totality ⦄ {𝟎}   {𝟎}    = [∨]-introₗ ([≤]-from-[≡] [≡]-intro)
  total ⦃ [≤]-totality ⦄ {𝐒(a)}{𝟎}    = [∨]-introᵣ ([≤][0]ᵣ-minimum)
  total ⦃ [≤]-totality ⦄ {𝟎}   {𝐒(b)} = [∨]-introₗ ([≤][0]ᵣ-minimum)
  total ⦃ [≤]-totality ⦄ {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ ([≤]-with-[𝐒] {a}{b})) ([∨]-introᵣ ∘ ([≤]-with-[𝐒] {b}{a})) (total ⦃ [≤]-totality ⦄ {a}{b})

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

instance
  [≥]-to-[≮] : ∀{a b : ℕ} → (a ≮ b) ← (a ≥ b)
  [≥]-to-[≮] {a}{b} (b≤a) (𝐒a≤b) = [≤][𝐒]ₗ (transitivity {_}{_}{𝐒(a)}{b}{a} (𝐒a≤b) (b≤a))

instance
  [≤]-to-[≯] : ∀{a b : ℕ} → (a ≯ b) ← (a ≤ b)
  [≤]-to-[≯] {a}{b} (a≤b) (𝐒b≤a) = [≥]-to-[≮] {b}{a} (a≤b) (𝐒b≤a)

instance
  [>]-to-[≰] : ∀{a b : ℕ} → (a ≰ b) ← (a > b)
  [>]-to-[≰] {a}{b} (𝐒b≤a) (a≤b) = [≤]-to-[≯] (a≤b) (𝐒b≤a)

instance
  [<]-to-[≱] : ∀{a b : ℕ} → (a ≱ b) ← (a < b)
  [<]-to-[≱] {a}{b} (𝐒a≤b) (b≤a) = [≥]-to-[≮] (b≤a) (𝐒a≤b)



instance
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

instance
  [<][0]-minimum : ∀{x : ℕ} → (0 < 𝐒(x))
  [<][0]-minimum {x} = [≤]-with-[𝐒] {0} ([≤][0]ᵣ-minimum)

instance
  [<]-of-[𝐒] : ∀{x : ℕ} → (x < 𝐒(x))
  [<]-of-[𝐒] = reflexivity ⦃ [≤]-reflexivity ⦄

instance
  [<][≢]-equivalence : ∀{x} → (x > 0) ↔ (x ≢ 0)
  [<][≢]-equivalence {x} = [↔]-intro (l{x}) (r{x}) where
    l : ∀{x} → (x > 0) ← (x ≢ 0)
    l{𝟎}    (x≢𝟎)  = [⊥]-elim((x≢𝟎)([≡]-intro))
    l{𝐒(x)} (𝐒x≢𝟎) = [≤]-with-[𝐒] ([≤][0]ᵣ-minimum)

    r : ∀{x} → (x > 0) → (x ≢ 0)
    r{𝟎}    ()
    r{𝐒(x)} (𝟏≤𝐒x) (𝐒x≡𝟎) with [≡]-substitutionᵣ (𝐒x≡𝟎) {expr ↦ 1 ≤ expr} (𝟏≤𝐒x)
    ... | ()



instance
  lteq2-𝟎 : ∀{n} → (𝟎 lteq2 n)
  lteq2-𝟎 = [⊤]-intro

instance
  lteq2-𝐒 : ∀{n} → (n lteq2 n)
  lteq2-𝐒 {𝟎}    = [⊤]-intro
  lteq2-𝐒 {𝐒(n)} = lteq2-𝐒 {n}



instance
  [≤]-to-[<][≡] : ∀{a b : ℕ} → (a ≤ b) → (a < b)∨(a ≡ b)
  [≤]-to-[<][≡] {𝟎}   {𝟎}    ([≤][0]ᵣ-minimum)    = [∨]-introᵣ([≡]-intro)
  [≤]-to-[<][≡] {𝟎}   {𝐒(b)} ([≤][0]ᵣ-minimum)    = [∨]-introₗ([<][0]-minimum)
  [≤]-to-[<][≡] {𝐒(a)}{𝐒(b)} ([≤]-with-[𝐒] (a≤b)) with [≤]-to-[<][≡] {a}{b} (a≤b)
  ... | [∨]-introₗ(a<b) = [∨]-introₗ([≤]-with-[𝐒] (a<b))
  ... | [∨]-introᵣ(a≡b) = [∨]-introᵣ([≡]-with(𝐒) (a≡b))

instance
  [<][≡]-to-[≤] : ∀{a b : ℕ} → (a < b)∨(a ≡ b) → (a ≤ b)
  [<][≡]-to-[≤] {a}   {.a}   ([∨]-introᵣ([≡]-intro)) = [≤]-from-[≡] ([≡]-intro)
  [<][≡]-to-[≤] {a}   {b}    ([∨]-introₗ(a<b))       = [≤]-predecessor (a<b)

instance
  [≥]-to-[>][≡] : ∀{a b : ℕ} → (a ≥ b) → (a > b)∨(a ≡ b)
  [≥]-to-[>][≡] {a}{b} (proof) with [≤]-to-[<][≡] {b}{a} (proof)
  ... | [∨]-introₗ(a<b) = [∨]-introₗ(a<b)
  ... | [∨]-introᵣ(b≡a) = [∨]-introᵣ(symmetry(b≡a))

instance
  [>][≡]-to-[≥] : ∀{a b : ℕ} → (a > b)∨(a ≡ b) → (a ≥ b)
  [>][≡]-to-[≥] {a}{b} ([∨]-introₗ(a<b)) = [<][≡]-to-[≤] {b}{a} ([∨]-introₗ(a<b))
  [>][≡]-to-[≥] {a}{b} ([∨]-introᵣ(b≡a)) = [<][≡]-to-[≤] {b}{a} ([∨]-introᵣ(symmetry(b≡a)))
