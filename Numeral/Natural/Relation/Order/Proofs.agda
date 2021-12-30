module Numeral.Natural.Relation.Order.Proofs where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs
import      Relator.Ordering.Proofs
open import Structure.Relator
import      Structure.Relator.Names as Names
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Syntax.Transitivity
open import Type.Properties.MereProposition
open import Type

instance
  [≤]-succ-injectivity : ∀{x y} → Injective(succ{x}{y})
  Injective.proof [≤]-succ-injectivity [≡]-intro = [≡]-intro

instance
  [≤]-mereProposition : ∀{x y} → MereProposition(x ≤ y)
  MereProposition.uniqueness [≤]-mereProposition {min}    {min}    = [≡]-intro
  MereProposition.uniqueness [≤]-mereProposition {succ x} {succ y} = congruence₁(succ) (MereProposition.uniqueness [≤]-mereProposition {x}{y})

instance
  [≤]-minimum = \{y} → _≤_.min {y}
  [≤]-with-[𝐒] = \{x}{y} ⦃ xy ⦄ → _≤_.succ {x}{y} xy
[<]-minimum = \{y} → succ([≤]-minimum {y})

[≡]-to-[≤] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≡]-to-[≤] {𝟎}   {_}    _         = [≤]-minimum
[≡]-to-[≤] {𝐒(x)}{𝐒(y)} [≡]-intro = succ([≡]-to-[≤] {x}{y} [≡]-intro)

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
[≤]-successor {𝐒(x)}{𝐒(y)} (succ proof) = succ([≤]-successor {x}{y} (proof))

[≤]-predecessor : ∀{x y : ℕ} → (𝐒(x) ≤ y) → (x ≤ y)
[≤]-predecessor {x}   {𝟎}    ()
[≤]-predecessor {𝟎}   {𝐒(y)} (_) = [≤]-minimum
[≤]-predecessor {𝐒(x)}{𝐒(y)} (succ proof) = succ([≤]-predecessor {x}{y} (proof))

[≤]-without-[𝐒] : ∀{x y : ℕ} → (𝐒(x) ≤ 𝐒(y)) → (x ≤ y)
[≤]-without-[𝐒] (succ proof) = proof

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
    proof {𝐒(a)}{𝐒(b)}{𝐒(c)} (succ proofₗ) (succ proofᵣ ) =
      succ(proof {a}{b}{c} (proofₗ) (proofᵣ))

instance
  [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
  Antisymmetry.proof([≤]-antisymmetry) = proof where
    proof : Names.Antisymmetry (_≤_) (_≡_)
    proof {𝟎}    {𝟎}    (_) (_) = [≡]-intro
    proof {𝐒(_)} {𝟎}    ()
    proof {𝟎}    {𝐒(_)} (_) ()
    proof {𝐒(a)} {𝐒(b)} (succ proofₗ) (succ proofᵣ) =
      congruence₁(𝐒) (proof {a}{b} proofₗ proofᵣ)

instance
  [≤]-totality : ConverseTotal(_≤_)
  ConverseTotal.proof([≤]-totality) = proof where
    proof : Names.ConverseTotal(_≤_)
    proof {𝟎}   {𝟎}    = [∨]-introₗ ([≡]-to-[≤] [≡]-intro)
    proof {𝐒(a)}{𝟎}    = [∨]-introᵣ ([≤]-minimum)
    proof {𝟎}   {𝐒(b)} = [∨]-introₗ ([≤]-minimum)
    proof {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ (proof ↦ [≤]-with-[𝐒] {a}{b} ⦃ proof ⦄)) ([∨]-introᵣ ∘ (proof ↦ [≤]-with-[𝐒] {b}{a} ⦃ proof ⦄)) (proof {a}{b})

instance
  [≤]-weakPartialOrder : Weak.PartialOrder(_≤_)
  [≤]-weakPartialOrder = record{}

instance
  [≤]-weakTotalOrder : Weak.TotalOrder(_≤_)
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
  [≥]-weakPartialOrder : Weak.PartialOrder(_≥_)
  [≥]-weakPartialOrder = record{}

instance
  [≥]-weakTotalOrder : Weak.TotalOrder(_≥_)
  [≥]-weakTotalOrder = record{}

[≥]-to-[≮] : ∀{a b : ℕ} → (a ≮ b) ← (a ≥ b)
[≥]-to-[≮] {a}{b} (b≤a) (𝐒a≤b) = [≤][𝐒]ₗ (transitivity(_≤_) {𝐒(a)}{b}{a} (𝐒a≤b) (b≤a))

[≤]-to-[≯] : ∀{a b : ℕ} → (a ≯ b) ← (a ≤ b)
[≤]-to-[≯] {a}{b} (a≤b) (𝐒b≤a) = [≥]-to-[≮] {b}{a} (a≤b) (𝐒b≤a)

[>]-to-[≰] : ∀{a b : ℕ} → (a ≰ b) ← (a > b)
[>]-to-[≰] {a}{b} (𝐒b≤a) (a≤b) = [≤]-to-[≯] (a≤b) (𝐒b≤a)

[<]-to-[≱] : ∀{a b : ℕ} → (a ≱ b) ← (a < b)
[<]-to-[≱] {a}{b} (𝐒a≤b) (b≤a) = [≥]-to-[≮] (b≤a) (𝐒a≤b)

[<]-to-[≢] : ∀{a b : ℕ} → (a < b) → (a ≢ b)
[<]-to-[≢] = [≱]-to-[≢] ∘ [<]-to-[≱]

[>]-to-[≢] : ∀{a b : ℕ} → (a > b) → (a ≢ b)
[>]-to-[≢] = [≰]-to-[≢] ∘ [>]-to-[≰]

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
  [<]-converseTrichotomy : ConverseTrichotomy(_<_)(_≡_)
  ConverseTrichotomy.proof [<]-converseTrichotomy = p where
    p : Names.ConverseTrichotomy(_<_)(_≡_)
    p {𝟎}   {𝟎}   = [∨]-introₗ ([∨]-introᵣ [≡]-intro)
    p {𝟎}   {𝐒 y} = [∨]-introₗ ([∨]-introₗ [≤]-with-[𝐒])
    p {𝐒 x} {𝟎}   = [∨]-introᵣ [≤]-with-[𝐒]
    p {𝐒 x} {𝐒 y} with p {x} {y}
    ... | [∨]-introₗ ([∨]-introₗ (succ xy)) = [∨]-introₗ ([∨]-introₗ (succ (succ xy)))
    ... | [∨]-introₗ ([∨]-introᵣ [≡]-intro) = [∨]-introₗ ([∨]-introᵣ [≡]-intro)
    ... | [∨]-introᵣ (succ xy)              = [∨]-introᵣ (succ (succ xy))

instance
  [<]-strictPartialOrder : Strict.PartialOrder (_<_)
  [<]-strictPartialOrder = record{}

instance
  [<]-strictTotalOrder : Strict.TotalOrder(_<_)
  [<]-strictTotalOrder = record{}

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
[<]-of-[𝟎][𝐒] {𝐒 x} = succ([≤]-minimum)

instance
  [≤]-of-[𝐒] : ∀{x : ℕ} → (x ≤ 𝐒(x))
  [≤]-of-[𝐒] = [≤]-successor(reflexivity(_≤_))

[<][≢]-equivalence : ∀{x} → (x > 0) ↔ (x ≢ 0)
[<][≢]-equivalence {x} = [↔]-intro (l{x}) (r{x}) where
  l : ∀{x} → (x > 0) ← (x ≢ 0)
  l{𝟎}    (x≢𝟎)  = [⊥]-elim((x≢𝟎)([≡]-intro))
  l{𝐒(x)} (𝐒x≢𝟎) = succ([≤]-minimum)

  r : ∀{x} → (x > 0) → (x ≢ 0)
  r{𝟎}    ()
  r{𝐒(x)} (𝟏≤𝐒x) (𝐒x≡𝟎) with substitute₁ᵣ(1 ≤_) (𝐒x≡𝟎) (𝟏≤𝐒x)
  ... | ()

[≤]-to-[<][≡] : ∀{a b : ℕ} → (a ≤ b) → (a < b)∨(a ≡ b)
[≤]-to-[<][≡] {𝟎}   {𝟎}    ([≤]-minimum)    = [∨]-introᵣ([≡]-intro)
[≤]-to-[<][≡] {𝟎}   {𝐒(b)} ([≤]-minimum)    = [∨]-introₗ([<]-minimum)
[≤]-to-[<][≡] {𝐒(a)}{𝐒(b)} (succ(a≤b)) with [≤]-to-[<][≡] {a}{b} (a≤b)
... | [∨]-introₗ(a<b) = [∨]-introₗ(succ(a<b))
... | [∨]-introᵣ(a≡b) = [∨]-introᵣ(congruence₁(𝐒) (a≡b))

[≮][≢]-to-[≰] : ∀{a b : ℕ} → (a ≮ b) → (a ≢ b) → (a ≰ b)
[≮][≢]-to-[≰] (a≮b) (a≢b) (a≤b) with [≤]-to-[<][≡] (a≤b)
... | [∨]-introₗ (a<b) = a≮b a<b
... | [∨]-introᵣ (a≡b) = a≢b a≡b

[<][≡]-to-[≤] : ∀{a b : ℕ} → (a < b)∨(a ≡ b) → (a ≤ b)
[<][≡]-to-[≤] {a}   {.a}   ([∨]-introᵣ([≡]-intro)) = [≡]-to-[≤] ([≡]-intro)
[<][≡]-to-[≤] {a}   {b}    ([∨]-introₗ(a<b))       = [≤]-predecessor (a<b)

instance
  [<][≤]-sub : (_<_) ⊆₂ (_≤_)
  [<][≤]-sub = intro [≤]-predecessor

instance
  [>][≥]-sub : (_>_) ⊆₂ (_≥_)
  [>][≥]-sub = intro(sub₂(_<_)(_≤_))

[≰]-to-[≮] : ∀{x y : ℕ} → (x ≰ y) → (x ≮ y)
[≰]-to-[≮] = contrapositiveᵣ (sub₂(_<_)(_≤_))

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
[≤][>]-dichotomy {x} {y} | [∨]-introₗ ([∨]-introₗ x<y) = [∨]-introₗ(sub₂(_<_)(_≤_) x<y)
[≤][>]-dichotomy {x} {y} | [∨]-introₗ ([∨]-introᵣ x≡y) = [∨]-introₗ(sub₂(_≡_)(_≤_) x≡y)
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
[<]-non-zero-existence (succ _) = [<]-of-[𝟎][𝐒]

[≢]-to-[<]-of-0ᵣ : ∀{n} → (n ≢ 0) → (0 < n)
[≢]-to-[<]-of-0ᵣ {𝟎}   p with () ← p [≡]-intro
[≢]-to-[<]-of-0ᵣ {𝐒 n} p = succ min

[≤][≢]-to-[<] : ∀{a b : ℕ} → (a ≤ b) → (a ≢ b) → (a < b)
[≤][≢]-to-[<] {.𝟎}     {b}      min       ne = [≢]-to-[<]-of-0ᵣ (ne ∘ symmetry(_≡_))
[≤][≢]-to-[<] {.(𝐒 _)} {.(𝐒 _)} (succ lt) ne = succ([≤][≢]-to-[<] lt (ne ∘ congruence₁(𝐒)))

instance
  [≤][≡]-subtransitivityₗ : Subtransitivityₗ(_≤_)(_≡_)
  [≤][≡]-subtransitivityₗ = subrelation-transitivity-to-subtransitivityₗ

instance
  [≤][≡]-subtransitivityᵣ : Subtransitivityᵣ(_≤_)(_≡_)
  [≤][≡]-subtransitivityᵣ = subrelation-transitivity-to-subtransitivityᵣ

instance
  [≥][≡]-subtransitivityₗ : Subtransitivityₗ(_≥_)(_≡_)
  [≥][≡]-subtransitivityₗ = subrelation-transitivity-to-subtransitivityₗ

instance
  [≥][≡]-subtransitivityᵣ : Subtransitivityᵣ(_≥_)(_≡_)
  [≥][≡]-subtransitivityᵣ = subrelation-transitivity-to-subtransitivityᵣ

instance
  [≤][<]-subtransitivityₗ : Subtransitivityₗ(_≤_)(_<_)
  [≤][<]-subtransitivityₗ = subrelation-transitivity-to-subtransitivityₗ

instance
  [≤][<]-subtransitivityᵣ : Subtransitivityᵣ(_≤_)(_<_)
  [≤][<]-subtransitivityᵣ = subrelation-transitivity-to-subtransitivityᵣ

instance
  [≥][>]-subtransitivityₗ : Subtransitivityₗ(_≥_)(_>_)
  [≥][>]-subtransitivityₗ = subrelation-transitivity-to-subtransitivityₗ

instance
  [≥][>]-subtransitivityᵣ : Subtransitivityᵣ(_≥_)(_>_)
  [≥][>]-subtransitivityᵣ = subrelation-transitivity-to-subtransitivityᵣ

instance
  [>][≡]-subtransitivityₗ : Subtransitivityₗ(_>_)(_≡_)
  [>][≡]-subtransitivityₗ = intro(substitute₂-₁ₗ(_>_)(_))

instance
  [>][≡]-subtransitivityᵣ : Subtransitivityᵣ(_>_)(_≡_)
  [>][≡]-subtransitivityᵣ = intro(swap(substitute₂-₂ᵣ(_>_)(_)))

instance
  [<][≡]-subtransitivityₗ : Subtransitivityₗ(_<_)(_≡_)
  [<][≡]-subtransitivityₗ = intro(substitute₂-₁ₗ(_<_)(_))

instance
  [<][≡]-subtransitivityᵣ : Subtransitivityᵣ(_<_)(_≡_)
  [<][≡]-subtransitivityᵣ = intro(swap(substitute₂-₂ᵣ(_<_)(_)))

instance
  [<][≤]-subtransitivityₗ : Subtransitivityₗ(_<_)(_≤_)
  [<][≤]-subtransitivityₗ = intro((_🝖_) ∘ succ)

instance
  [<][≤]-subtransitivityᵣ : Subtransitivityᵣ(_<_)(_≤_)
  [<][≤]-subtransitivityᵣ = intro(_🝖_)

[≤]-to-positive : ∀{a b} → (a ≤ b) → (Positive(a) → Positive(b))
[≤]-to-positive {𝐒 a} {𝐒 b} _ <> = <>
