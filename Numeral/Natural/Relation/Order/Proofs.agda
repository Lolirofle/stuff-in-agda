module Numeral.Natural.Relation.Order.Proofs where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs
import      Structure.Relator.Names as Names
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

-- TODO: A method for pattern matching: https://stackoverflow.com/questions/20682013/agda-why-am-i-unable-to-pattern-match-on-refl

[≡]-to-[≤] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≡]-to-[≤] {𝟎}   {_}    _         = [≤]-minimum
[≡]-to-[≤] {𝐒(x)}{𝐒(y)} [≡]-intro = [≤]-with-[𝐒] ⦃ [≡]-to-[≤] {x}{y} [≡]-intro ⦄

[≡]-to-[≥] : ∀{x y : ℕ} → (x ≡ y) → (x ≥ y)
[≡]-to-[≥] = [≡]-to-[≤] ∘ symmetry(_≡_)

[≰]-to-[≢] : ∀{x y : ℕ} → (x ≰ y) → (x ≢ y)
[≰]-to-[≢] = contrapositiveᵣ [≡]-to-[≤]

[≱]-to-[≢] : ∀{x y : ℕ} → (x ≱ y) → (x ≢ y)
[≱]-to-[≢] = contrapositiveᵣ [≡]-to-[≥]

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

instance
  [≤]-reflexivity : Reflexivity (_≤_)
  Reflexivity.proof([≤]-reflexivity) = [≡]-to-[≤] [≡]-intro

instance
  [≤]-transitivity : Transitivity (_≤_)
  Transitivity.proof([≤]-transitivity) = proof where
    proof : Names.Transitivity (_≤_)
    proof {𝟎}   {_}   {_} (_)(_) = [≤]-minimum
    proof {𝐒(a)}{𝐒(b)}{𝐒(c)} ([≤]-with-[𝐒] ⦃ proofₗ ⦄) ([≤]-with-[𝐒] ⦃ proofᵣ ⦄ ) =
      [≤]-with-[𝐒] ⦃ proof {a}{b}{c} (proofₗ) (proofᵣ) ⦄

instance
  [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
  Antisymmetry.proof([≤]-antisymmetry) = proof where
    proof : Names.Antisymmetry (_≤_) (_≡_)
    proof {𝟎}    {𝟎}    (_) (_) = [≡]-intro
    proof {𝐒(_)} {𝟎}    ()
    proof {𝟎}    {𝐒(_)} (_) ()
    proof {𝐒(a)} {𝐒(b)} ([≤]-with-[𝐒] ⦃ proofₗ ⦄) ([≤]-with-[𝐒] ⦃ proofᵣ ⦄) =
      [≡]-with(𝐒) (proof {a}{b} proofₗ proofᵣ)

instance
  [≤]-totality : ConverseTotal(_≤_)
  ConverseTotal.proof([≤]-totality) = proof where
    proof : Names.ConverseTotal(_≤_)
    proof {𝟎}   {𝟎}    = [∨]-introₗ ([≡]-to-[≤] [≡]-intro)
    proof {𝐒(a)}{𝟎}    = [∨]-introᵣ ([≤]-minimum)
    proof {𝟎}   {𝐒(b)} = [∨]-introₗ ([≤]-minimum)
    proof {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ (proof ↦ [≤]-with-[𝐒] {a}{b} ⦃ proof ⦄)) ([∨]-introᵣ ∘ (proof ↦ [≤]-with-[𝐒] {b}{a} ⦃ proof ⦄)) (proof {a}{b})

instance
  [≤]-weakPartialOrder : Weak.PartialOrder (_≤_) (_≡_)
  [≤]-weakPartialOrder = record{}

instance
  [≤]-weakTotalOrder : Weak.TotalOrder (_≤_) (_≡_)
  [≤]-weakTotalOrder = record{}

instance
  [≥]-reflexivity : Reflexivity (_≥_)
  Reflexivity.proof([≥]-reflexivity) = Reflexivity.proof([≤]-reflexivity)

instance
  [≥]-transitivity : Transitivity (_≥_)
  Transitivity.proof([≥]-transitivity) = swap(Transitivity.proof([≤]-transitivity))

instance
  [≥]-antisymmetry : Antisymmetry (_≥_) (_≡_)
  Antisymmetry.proof([≥]-antisymmetry) = swap(Antisymmetry.proof([≤]-antisymmetry))

instance
  [≥]-totality : ConverseTotal(_≥_)
  ConverseTotal.proof([≥]-totality) = ConverseTotal.proof([≤]-totality)

instance
  [≥]-weakPartialOrder : Weak.PartialOrder (_≥_) (_≡_)
  [≥]-weakPartialOrder = record{}

instance
  [≥]-weakTotalOrder : Weak.TotalOrder (_≥_) (_≡_)
  [≥]-weakTotalOrder = record{}

[≥]-to-[≮] : ∀{a b : ℕ} → (a ≮ b) ← (a ≥ b)
[≥]-to-[≮] {a}{b} (b≤a) (𝐒a≤b) = [≤][𝐒]ₗ (transitivity(_≤_) {𝐒(a)}{b}{a} (𝐒a≤b) (b≤a))

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
  Irreflexivity.proof([<]-irreflexivity) = [≤][𝐒]ₗ

instance
  [<]-transitivity : Transitivity (_<_)
  Transitivity.proof([<]-transitivity) {x}{y}{z} (l) (r) = Transitivity.proof([≤]-transitivity) {𝐒(x)} {𝐒(y)} {z} ([≤]-successor (l)) (r)

instance
  [<]-asymmetry : Asymmetry (_<_)
  Asymmetry.proof([<]-asymmetry) (l) (r) = Irreflexivity.proof([<]-irreflexivity) (Transitivity.proof([<]-transitivity) (l) (r))

instance
  [<]-strictOrder : Strict.PartialOrder (_<_)
  [<]-strictOrder = record{}

instance
  [>]-irreflexivity : Irreflexivity (_>_)
  Irreflexivity.proof([>]-irreflexivity) = Irreflexivity.proof([<]-irreflexivity)

instance
  [>]-transitivity : Transitivity (_>_)
  Transitivity.proof([>]-transitivity) = swap(Transitivity.proof([<]-transitivity))

instance
  [>]-asymmetry : Asymmetry (_>_)
  Asymmetry.proof([>]-asymmetry) = swap(Asymmetry.proof([<]-asymmetry))

instance
  [>]-strictOrder : Strict.PartialOrder (_>_)
  [>]-strictOrder = record{}

[<]-of-[𝐒] : ∀{x : ℕ} → (x < 𝐒(x))
[<]-of-[𝐒] = reflexivity(_≤_)

[<]-of-[𝟎][𝐒] : ∀{x : ℕ} → (𝟎 < 𝐒(x))
[<]-of-[𝟎][𝐒] {𝟎} = [<]-of-[𝐒]
[<]-of-[𝟎][𝐒] {𝐒 x} = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄

instance
  [≤]-of-[𝐒] : ∀{x : ℕ} → (x ≤ 𝐒(x))
  [≤]-of-[𝐒] = [≤]-successor(reflexivity(_≤_))

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

[≮][≢]-to-[≰] : ∀{a b : ℕ} → (a ≮ b) → (a ≢ b) → (a ≰ b)
[≮][≢]-to-[≰] (a≮b) (a≢b) (a≤b) with [≤]-to-[<][≡] (a≤b)
... | [∨]-introₗ (a<b) = a≮b a<b
... | [∨]-introᵣ (a≡b) = a≢b a≡b

[<][≡]-to-[≤] : ∀{a b : ℕ} → (a < b)∨(a ≡ b) → (a ≤ b)
[<][≡]-to-[≤] {a}   {.a}   ([∨]-introᵣ([≡]-intro)) = [≡]-to-[≤] ([≡]-intro)
[<][≡]-to-[≤] {a}   {b}    ([∨]-introₗ(a<b))       = [≤]-predecessor (a<b)

[<]-to-[≤] : ∀{a b : ℕ} → (a < b) → (a ≤ b)
[<]-to-[≤] = [≤]-predecessor

[≰]-to-[≮] : ∀{x y : ℕ} → (x ≰ y) → (x ≮ y)
[≰]-to-[≮] = contrapositiveᵣ [<]-to-[≤]

[≥]-to-[>][≡] : ∀{a b : ℕ} → (a ≥ b) → (a > b)∨(a ≡ b)
[≥]-to-[>][≡] {a}{b} (proof) with [≤]-to-[<][≡] {b}{a} (proof)
... | [∨]-introₗ(a<b) = [∨]-introₗ(a<b)
... | [∨]-introᵣ(b≡a) = [∨]-introᵣ(symmetry(_≡_) (b≡a))

[<]-trichotomy : ∀{x y} → (x < y) ∨ (x ≡ y) ∨ (x > y)
[<]-trichotomy {x}{y} with converseTotal(_≤_) ⦃ [≤]-totality ⦄
[<]-trichotomy {x}{y} | [∨]-introₗ x≤y with [≤]-to-[<][≡] {x}{y} x≤y
[<]-trichotomy {x}{y} | [∨]-introₗ x≤y | [∨]-introₗ x<y = [∨]-introₗ ([∨]-introₗ x<y)
[<]-trichotomy {x}{y} | [∨]-introₗ x≤y | [∨]-introᵣ x≡y = [∨]-introₗ ([∨]-introᵣ x≡y)
[<]-trichotomy {x}{y} | [∨]-introᵣ y≤x with [≥]-to-[>][≡] {x}{y} y≤x
[<]-trichotomy {x}{y} | [∨]-introᵣ y≤x | [∨]-introₗ y<x = [∨]-introᵣ y<x
[<]-trichotomy {x}{y} | [∨]-introᵣ y≤x | [∨]-introᵣ y≡x = [∨]-introₗ ([∨]-introᵣ y≡x)

[≤][>]-dichotomy : ∀{x y} → (x ≤ y) ∨ (x > y)
[≤][>]-dichotomy {x}{y} with [<]-trichotomy {x}{y}
[≤][>]-dichotomy {x} {y} | [∨]-introₗ ([∨]-introₗ x<y) = [∨]-introₗ([<]-to-[≤] x<y)
[≤][>]-dichotomy {x} {y} | [∨]-introₗ ([∨]-introᵣ x≡y) = [∨]-introₗ([≡]-to-[≤] x≡y)
[≤][>]-dichotomy {x} {y} | [∨]-introᵣ x>y              = [∨]-introᵣ(x>y)

[<][≥]-dichotomy : ∀{x y} → (x < y) ∨ (x ≥ y)
[<][≥]-dichotomy {x}{y} = [∨]-symmetry([≤][>]-dichotomy {y}{x})

[≯][≢]-to-[≱] : ∀{a b : ℕ} → (a ≯ b) → (a ≢ b) → (a ≱ b)
[≯][≢]-to-[≱] (a≯b) (a≢b) (a≥b) with [≥]-to-[>][≡] (a≥b)
... | [∨]-introₗ (a>b) = a≯b a>b
... | [∨]-introᵣ (a≡b) = a≢b a≡b

[>][≡]-to-[≥] : ∀{a b : ℕ} → (a > b)∨(a ≡ b) → (a ≥ b)
[>][≡]-to-[≥] {a}{b} ([∨]-introₗ(a<b)) = [<][≡]-to-[≤] {b}{a} ([∨]-introₗ(a<b))
[>][≡]-to-[≥] {a}{b} ([∨]-introᵣ(b≡a)) = [<][≡]-to-[≤] {b}{a} ([∨]-introᵣ(symmetry(_≡_)(b≡a)))

[>]-to-[≥] : ∀{a b : ℕ} → (a > b) → (a ≥ b)
[>]-to-[≥] {a}{b} (a<b) = [<][≡]-to-[≤] {b}{a} ([∨]-introₗ(a<b))

[≱]-to-[≯] : ∀{x y : ℕ} → (x ≱ y) → (x ≯ y)
[≱]-to-[≯] = contrapositiveᵣ [>]-to-[≥]

[≮][≯]-to-[≡] : ∀{a b : ℕ} → (a ≮ b) → (a ≯ b) → (a ≡ b)
[≮][≯]-to-[≡] {a}{b} (a≮b) (a≯b) with [<]-trichotomy {a}{b}
... | [∨]-introₗ ([∨]-introₗ a<b) = [⊥]-elim(a≮b a<b)
... | [∨]-introₗ ([∨]-introᵣ a≡b) = a≡b
... | [∨]-introᵣ b<a              = [⊥]-elim(a≯b b<a)

[≮][≢][≯]-not : ∀{a b : ℕ} → (a ≮ b) → (a ≢ b) → (a ≯ b) → ⊥
[≮][≢][≯]-not {a}{b} (a≮b) (a≢b) (a≯b) with [<]-trichotomy {a}{b}
... | [∨]-introₗ ([∨]-introₗ a<b) = a≮b a<b
... | [∨]-introₗ ([∨]-introᵣ a≡b) = a≢b a≡b
... | [∨]-introᵣ b<a              = a≯b b<a

[≰][≯]-not : ∀{a b : ℕ} → (a ≰ b) → (a ≯ b) → ⊥
[≰][≯]-not {a}{b} (a≰b) (a≯b) = [≮][≢][≯]-not ([≰]-to-[≮] a≰b) ([≰]-to-[≢] a≰b) (a≯b)

[≮][≱]-not : ∀{a b : ℕ} → (a ≮ b) → (a ≱ b) → ⊥
[≮][≱]-not {a}{b} (a≮b) (a≱b) = [≮][≢][≯]-not (a≮b) ([≱]-to-[≢] a≱b) ([≱]-to-[≯] a≱b)

[<]-non-zero-existence : ∀{a b : ℕ} → (a < b) → (𝟎 < b)
[<]-non-zero-existence [≤]-with-[𝐒] = [<]-of-[𝟎][𝐒]
