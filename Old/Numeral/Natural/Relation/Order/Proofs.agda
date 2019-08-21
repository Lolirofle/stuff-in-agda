{-# OPTIONS --with-K #-}

module Numeral.Natural.Relation.Order.Proofs{ℓ} where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Induction{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

-- TODO: The instance declarations probably do nothing for functions with arguments. Either make all the args implicit or remove the instance decls.
-- TODO: A method for pattern matching: https://stackoverflow.com/questions/20682013/agda-why-am-i-unable-to-pattern-match-on-refl

[<]-minimum : ∀{x : ℕ} → (0 < 𝐒(x))
[<]-minimum {x} = [≤]-with-[𝐒] {0} ⦃ [≤]-minimum ⦄

[≡]-to-[≤] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≡]-to-[≤] {𝟎}   {_}    ([≡]-intro) = [≤]-minimum
[≡]-to-[≤] {𝐒(x)}{𝐒(y)} ([≡]-intro) = [≤]-with-[𝐒] ⦃ [≡]-to-[≤] {x}{y} ([≡]-intro) ⦄

[≡]-to-[≥] : ∀{x y : ℕ} → (x ≡ y) → (x ≥ y)
[≡]-to-[≥] = [≡]-to-[≤] ∘ symmetry

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

[≤]-with-[+]ᵣ : ∀{x y z : ℕ} → (x ≤ y) → (x + z ≤ y + z)
[≤]-with-[+]ᵣ {_}{_}{𝟎}    (proof)    = proof
[≤]-with-[+]ᵣ {_}{_}{𝐒(z)} (proof) = [≤]-with-[𝐒] ⦃ [≤]-with-[+]ᵣ {_}{_}{z} (proof) ⦄

-- [≤]-with-[+]ₗ : ∀{x y z : ℕ} → (x ≤ y) → (z + x ≤ z + y)
-- TODO: [≤]-with-[+] : ∀{x₁ y₁ : ℕ} → (x₁ ≤ y₁) → ∀{x₂ y₂ : ℕ} → (x₂ ≤ y₂) → (x₁ + x₂ ≤ y₁ + y₂)

instance
  [≤]-reflexivity : Reflexivity (_≤_)
  reflexivity ⦃ [≤]-reflexivity ⦄ = [≡]-to-[≤] [≡]-intro

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
  [≤]-totality : SymmetricallyTotal(_≤_)
  converseTotal ⦃ [≤]-totality ⦄ {𝟎}   {𝟎}    = [∨]-introₗ ([≡]-to-[≤] [≡]-intro)
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

 -- [≤]-with-[𝐒]

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
... | [∨]-introᵣ(b≡a) = [∨]-introᵣ(symmetry(b≡a))

[<]-trichotomy : ∀{x y} → (x < y) ∨ (x ≡ y) ∨ (x > y)
[<]-trichotomy {x}{y} with converseTotal ⦃ [≤]-totality ⦄
[<]-trichotomy {x}{y} | [∨]-introₗ x≤y with [≤]-to-[<][≡] {x}{y} x≤y
[<]-trichotomy {x}{y} | [∨]-introₗ x≤y | [∨]-introₗ x<y = [∨]-introₗ ([∨]-introₗ x<y)
[<]-trichotomy {x}{y} | [∨]-introₗ x≤y | [∨]-introᵣ x≡y = [∨]-introₗ ([∨]-introᵣ x≡y)
[<]-trichotomy {x}{y} | [∨]-introᵣ y≤x with [≥]-to-[>][≡] {x}{y} y≤x
[<]-trichotomy {x}{y} | [∨]-introᵣ y≤x | [∨]-introₗ y<x = [∨]-introᵣ y<x
[<]-trichotomy {x}{y} | [∨]-introᵣ y≤x | [∨]-introᵣ y≡x = [∨]-introₗ ([∨]-introᵣ y≡x)


[≯][≢]-to-[≱] : ∀{a b : ℕ} → (a ≯ b) → (a ≢ b) → (a ≱ b)
[≯][≢]-to-[≱] (a≯b) (a≢b) (a≥b) with [≥]-to-[>][≡] (a≥b)
... | [∨]-introₗ (a>b) = a≯b a>b
... | [∨]-introᵣ (a≡b) = a≢b a≡b

[>][≡]-to-[≥] : ∀{a b : ℕ} → (a > b)∨(a ≡ b) → (a ≥ b)
[>][≡]-to-[≥] {a}{b} ([∨]-introₗ(a<b)) = [<][≡]-to-[≤] {b}{a} ([∨]-introₗ(a<b))
[>][≡]-to-[≥] {a}{b} ([∨]-introᵣ(b≡a)) = [<][≡]-to-[≤] {b}{a} ([∨]-introᵣ(symmetry(b≡a)))

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
