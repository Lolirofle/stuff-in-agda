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
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

-- TODO: A method for pattern matching: https://stackoverflow.com/questions/20682013/agda-why-am-i-unable-to-pattern-match-on-refl

[≡]-to-[≤] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≡]-to-[≤] {𝟎}   {_}    ([≡]-intro) = [≤]-minimum
[≡]-to-[≤] {𝐒(x)}{𝐒(y)} ([≡]-intro) = [≤]-with-[𝐒] ⦃ [≡]-to-[≤] {x}{y} ([≡]-intro) ⦄

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

-- TODO: Move some of the stuff here to Numeral.Natrual.Oper.Proofs.Order

{-
[+][−₀]-commutativity : ∀{x y} → ⦃ _ : y ≥ z ⦄ → (x + (y −₀ z) ≡ (x −₀ z) + y)
-}

[≤]ₗ[+] : ∀{x y : ℕ} → (x + y ≤ x) → (y ≡ 𝟎)
[≤]ₗ[+] {𝟎}               = [≤][0]ᵣ
[≤]ₗ[+] {𝐒(x)}{y} (proof) = [≤]ₗ[+] {x} ([≤]-without-[𝐒] {x + y} {x} (proof))

[≤]-with-[+]ᵣ : ∀{x y z : ℕ} → (x ≤ y) → (x + z ≤ y + z)
[≤]-with-[+]ᵣ {_}{_}{𝟎}    (proof)    = proof
[≤]-with-[+]ᵣ {_}{_}{𝐒(z)} (proof) = [≤]-with-[𝐒] ⦃ [≤]-with-[+]ᵣ {_}{_}{z} (proof) ⦄

[≤]-with-[+]ₗ : ∀{x y z : ℕ} → (x ≤ y) → (z + x ≤ z + y)
[≤]-with-[+]ₗ {.0} {𝟎}   {z } [≤]-minimum            = reflexivity(_≤_)
[≤]-with-[+]ₗ {.0} {𝐒 y} {z}  [≤]-minimum            = [≤]-successor([≤]-with-[+]ₗ {0}{y}{z} [≤]-minimum)
[≤]-with-[+]ₗ {𝐒 x} {𝐒 y} {z} ([≤]-with-[𝐒] ⦃ xy ⦄ ) = [≤]-with-[𝐒] ⦃ [≤]-with-[+]ₗ {x} {y} {z} xy ⦄

[≤]-of-[+]ᵣ : ∀{x y : ℕ} → (y ≤ x + y)
[≤]-of-[+]ᵣ {x}   {𝟎}   = [≤]-minimum
[≤]-of-[+]ᵣ {𝟎}   {𝐒 x} = reflexivity(_≤_)
[≤]-of-[+]ᵣ {𝐒 x} {𝐒 y} = [≤]-with-[𝐒] ⦃ [≤]-of-[+]ᵣ {𝐒 x}{y} ⦄

[≤]-of-[+]ₗ : ∀{x y : ℕ} → (x ≤ x + y)
[≤]-of-[+]ₗ {𝟎}   {y}   = [≤]-minimum
[≤]-of-[+]ₗ {𝐒 x} {𝟎}   = reflexivity(_≤_)
[≤]-of-[+]ₗ {𝐒 x} {𝐒 y} =  [≤]-with-[𝐒] ⦃ [≤]-of-[+]ₗ {x}{𝐒 y} ⦄

[≤]-with-[+] : ∀{x₁ y₁ : ℕ} → ⦃ _ : (x₁ ≤ y₁)⦄ → ∀{x₂ y₂ : ℕ} → ⦃ _ : (x₂ ≤ y₂)⦄ → (x₁ + x₂ ≤ y₁ + y₂)
[≤]-with-[+] {x₁} {y₁} ⦃ x1y1 ⦄ {.0}     {y₂}     ⦃ [≤]-minimum ⦄ = transitivity(_≤_) x1y1 [≤]-of-[+]ₗ
[≤]-with-[+] {x₁} {y₁} ⦃ x1y1 ⦄ {𝐒 x₂} {𝐒 y₂} ⦃ [≤]-with-[𝐒] ⦃ p ⦄ ⦄ = [≤]-with-[𝐒] ⦃ [≤]-with-[+] {x₁} {y₁} {x₂} {y₂} ⦄

[≤]-from-[+] : ∀{ℓ}{P : ℕ → Stmt{ℓ}}{x} → (∀{n} → P(x + n)) → (∀{y} → ⦃ _ : (x ≤ y) ⦄ → P(y))
[≤]-from-[+] {ℓ} {P} {𝟎}   anpxn {y}   ⦃ [≤]-minimum ⦄        = anpxn{y}
[≤]-from-[+] {ℓ} {P} {𝐒 x} anpxn {𝐒 y} ⦃ [≤]-with-[𝐒] ⦃ xy ⦄ ⦄ = [≤]-from-[+] {ℓ} {P ∘ 𝐒} {x} anpxn {y} ⦃ xy ⦄

[−₀][+]-nullify2 : ∀{x y} → (x ≤ y) ↔ (x + (y −₀ x) ≡ y)
[−₀][+]-nullify2 {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x + (y −₀ x) ≡ y)
  l {𝟎}   {_}    _     = [≤]-minimum
  l {𝐒(_)}{𝟎}    ()
  l {𝐒(x)}{𝐒(y)} proof = [≤]-with-[𝐒] ⦃ l{x}{y} ([𝐒]-injectivity-raw proof) ⦄

  r : ∀{x y} → (x ≤ y) → (x + (y −₀ x) ≡ y)
  r {𝟎}   {𝟎}    proof = [≡]-intro
  r {𝟎}   {𝐒(_)} proof = [≡]-intro
  r {𝐒(_)}{𝟎}    ()
  r {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [≡]-with(𝐒) (r{x}{y} (proof))

[−₀][+]-nullify2ᵣ : ∀{x y} → (x ≤ y) ↔ ((y −₀ x) + x ≡ y)
[−₀][+]-nullify2ᵣ {x}{y} = [↔]-transitivity [−₀][+]-nullify2 ([≡]-substitution (commutativity(_+_) {x}{y −₀ x}) {_≡ y})

[−₀]-when-0 : ∀{x y} → (x ≤ y) ↔ (x −₀ y ≡ 𝟎)
[−₀]-when-0 {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x −₀ y ≡ 𝟎)
  l {𝟎}   {_}    _     = [≤]-minimum
  l {𝐒(_)}{𝟎}    ()
  l {𝐒(x)}{𝐒(y)} proof = [≤]-with-[𝐒] ⦃ l{x}{y} proof ⦄

  r : ∀{x y} → (x ≤ y) → (x −₀ y ≡ 𝟎)
  r {𝟎}   {_}    proof = [≡]-intro
  r {𝐒(_)}{𝟎}    ()
  r {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = r{x}{y} (proof)

[−₀]-lesser-[𝐒]ₗ : ∀{x y} → ((x −₀ 𝐒(y)) ≤ (x −₀ y))
[−₀]-lesser-[𝐒]ᵣ : ∀{x y} → ((x −₀ y) ≤ (𝐒(x) −₀ y))

[−₀]-lesser-[𝐒]ₗ {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser-[𝐒]ₗ {𝐒(_)}{𝟎}    = [≤]-of-[𝐒]
[−₀]-lesser-[𝐒]ₗ {𝐒(x)}{𝐒(y)} = [−₀]-lesser-[𝐒]ᵣ {x}{𝐒(y)}

[−₀]-lesser-[𝐒]ᵣ {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser-[𝐒]ᵣ {𝐒(x)}{𝟎}    = [≤]-of-[𝐒]
[−₀]-lesser-[𝐒]ᵣ {𝐒(x)}{𝐒(y)} = [−₀]-lesser-[𝐒]ₗ {𝐒(x)}{y}

[≤][−₀][𝐒]ₗ : ∀{x y} → ((𝐒(x) −₀ y) ≤ 𝐒(x −₀ y))
[≤][−₀][𝐒]ₗ {x}   {𝟎}    = reflexivity(_≤_)
[≤][−₀][𝐒]ₗ {𝟎}   {𝐒(y)} = [≤]-minimum
[≤][−₀][𝐒]ₗ {𝐒(x)}{𝐒(y)} = [≤][−₀][𝐒]ₗ {x}{y}

[−₀][𝐒]ₗ-equality : ∀{x y} → (x ≥ y) ↔ ((𝐒(x) −₀ y) ≡ 𝐒(x −₀ y))
[−₀][𝐒]ₗ-equality = [↔]-intro l r where
  l : ∀{x y} → (x ≥ y) ← ((𝐒(x) −₀ y) ≡ 𝐒(x −₀ y))
  l {𝟎}   {𝟎}   p = [≤]-minimum
  l {𝐒 x} {𝟎}   p = [≤]-minimum
  l {𝐒 x} {𝐒 y} p = [≤]-with-[𝐒] ⦃ l{x}{y} p ⦄

  r : ∀{x y} → (x ≥ y) → ((𝐒(x) −₀ y) ≡ 𝐒(x −₀ y))
  r {x}   {.𝟎}  [≤]-minimum           = [≡]-intro
  r {𝐒 x} {𝐒 y} ([≤]-with-[𝐒] ⦃ xy ⦄) = r xy

[−₀]-lesser : ∀{x y} → ((x −₀ y) ≤ x)
[−₀]-lesser {𝟎}   {_}    = [≤]-minimum
[−₀]-lesser {𝐒(x)}{𝟎}    = reflexivity(_≤_)
[−₀]-lesser {𝐒(x)}{𝐒(y)} = ([−₀]-lesser-[𝐒]ₗ {𝐒(x)}{y}) 🝖 ([−₀]-lesser {𝐒(x)}{y})


-- TODO: Converse is probably also true. One way to prove the equivalence is contraposition of [−₀]-comparison. Another is by [≤]-with-[+]ᵣ and some other stuff, but it seems to require more work
[−₀]-positive : ∀{x y} → (y > x) → (y −₀ x > 0)
[−₀]-positive {𝟎}   {𝐒(y)} (_) = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
[−₀]-positive {𝐒(x)}{𝐒(y)} ([≤]-with-[𝐒] ⦃ proof ⦄) = [−₀]-positive {x}{y} (proof)

[−₀]-nested-sameₗ : ∀{x y} → (x ≥ y) ↔ (x −₀ (x −₀ y) ≡ y)
[−₀]-nested-sameₗ {x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≥ y) ← (x −₀ (x −₀ y) ≡ y)
  l {x}{y} proof =
    y             🝖[ _≤_ ]-[ [≡]-to-[≤] (symmetry(_≡_) proof) ]
    x −₀ (x −₀ y) 🝖[ _≤_ ]-[ [−₀]-lesser {x}{x −₀ y} ]
    x             🝖[ _≤_ ]-end

  r : ∀{x y} → (x ≥ y) → (x −₀ (x −₀ y) ≡ y)
  r{x}{y} x≥y =
    x −₀ (x −₀ y)              🝖[ _≡_ ]-[ [≡]-with(_−₀ (x −₀ y)) (symmetry(_≡_) ([↔]-to-[→] ([−₀][+]-nullify2 {y}{x}) (x≥y)) 🝖 [+]-commutativity-raw{y}{x −₀ y}) ]
    ((x −₀ y) + y) −₀ (x −₀ y) 🝖[ _≡_ ]-[ [−₀]ₗ[+]ₗ-nullify {x −₀ y}{y} ]
    y                          🝖-end

[𝄩]-of-𝐒ₗ : ∀{x y} → (x ≥ y) → (𝐒(x) 𝄩 y ≡ 𝐒(x 𝄩 y))
[𝄩]-of-𝐒ₗ {𝟎}   {𝟎}   xy = [≡]-intro
[𝄩]-of-𝐒ₗ {𝐒 x} {𝟎}   xy = [≡]-intro
[𝄩]-of-𝐒ₗ {𝐒 x} {𝐒 y} xy = [𝄩]-of-𝐒ₗ {x} {y} ([≤]-without-[𝐒] xy)

[𝄩]-of-𝐒ᵣ : ∀{x y} → (x ≤ y) → (x 𝄩 𝐒(y) ≡ 𝐒(x 𝄩 y))
[𝄩]-of-𝐒ᵣ {𝟎}   {𝟎}   xy = [≡]-intro
[𝄩]-of-𝐒ᵣ {𝟎}   {𝐒 y} xy = [≡]-intro
[𝄩]-of-𝐒ᵣ {𝐒 x} {𝐒 y} xy = [𝄩]-of-𝐒ᵣ {x} {y} ([≤]-without-[𝐒] xy)
