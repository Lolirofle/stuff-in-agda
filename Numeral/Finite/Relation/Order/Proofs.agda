module Numeral.Finite.Relation.Order.Proofs where

open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Equiv
import      Lvl
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Finite.Relation.Order
open import Numeral.Finite
import      Numeral.Natural.Relation.Order as ℕ
open import Numeral.Natural
import      Relator.Equals.Proofs.Equiv as Id
open import Type.Identity
open import Type

private variable an bn cn n : ℕ
private variable a : 𝕟(an)
private variable b : 𝕟(bn)
private variable c : 𝕟(cn)

module _ where
  open import Data.Boolean.Operators
  open        Data.Boolean.Operators.Programming
  import      Numeral.Charge as Charge
  open import Numeral.Charge.Proofs
  open import Structure.Relator

  private variable b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ bₗ₁ bₗ₂ bₗ₃ bᵣ₁ bᵣ₂ bᵣ₃ bₘ₁ bₘ₂ bₘ₃ : Bool

  elim₃-[⋚?]-refl : Id (Charge.elim₃ b₁ b₂ b₃ (_⋚?_ {n} a a)) b₂
  elim₃-[⋚?]-refl {a = 𝟎}   = intro
  elim₃-[⋚?]-refl {a = 𝐒 a} = elim₃-[⋚?]-refl {a = a}

  elim₃-[⋚?]-sym : (Id{T = Bool} (Charge.elim₃ b₁ b₂ b₃ (_⋚?_ {an}{bn} a b)) (Charge.elim₃ b₃ b₂ b₁ (_⋚?_ {bn}{an} b a)))
  elim₃-[⋚?]-sym{a = 𝟎}  {b = 𝟎}   = intro
  elim₃-[⋚?]-sym{a = 𝟎}  {b = 𝐒 b} = intro
  elim₃-[⋚?]-sym{a = 𝐒 a}{b = 𝟎}   = intro
  elim₃-[⋚?]-sym{a = 𝐒 a}{b = 𝐒 b} = elim₃-[⋚?]-sym{a = a}{b = b}

  open import Data.Boolean.Proofs

  elim₃-[⋚?]-subtrans : let _ = a ; _ = b ; _ = c ; _ = b₁ && b₂ && b₃ && b₄ && b₅ && b₆ && b₇ && b₈ && b₉ in
    IsTrue((b₁ || (b₂ && b₄) || (b₃ && b₄)) →? b₇) →
    IsTrue(((b₁ && b₆) || (b₂ && b₅) || (b₃ && b₄)) →? b₈) →
    IsTrue(((b₃ && b₄) || (b₃ && b₅) || b₆) →? b₉) →
    IsTrue(Charge.elim₃ b₁ b₂ b₃ (_⋚?_ {an}{bn} a b)) →
    IsTrue(Charge.elim₃ b₄ b₅ b₆ (_⋚?_ {bn}{cn} b c)) →
    IsTrue(Charge.elim₃ b₇ b₈ b₉ (_⋚?_ {an}{cn} a c))
  elim₃-[⋚?]-subtrans {a = 𝟎}  {b = 𝟎}  {c = 𝟎}   {b₁}{𝑇} {b₃}{b₄}{𝑇} {b₆}{b₇}{𝑇} {b₉} _  _  _  ab bc = <> -- b₂ b₅ → b₈
  elim₃-[⋚?]-subtrans {a = 𝟎}  {b = 𝟎}  {c = 𝐒 c} {b₁}{𝑇} {b₃}{𝑇} {b₅}{b₆}{𝑇} {b₈}{b₉} _  _  _  ab bc = <> -- b₂ b₄ → b₇
  elim₃-[⋚?]-subtrans {a = 𝟎}  {b = 𝐒 b}{c = 𝟎}   {𝑇} {b₂}{b₃}{b₄}{b₅}{𝑇} {b₇}{𝑇} {b₉} _  _  _  ab bc = <> -- b₁ b₆ → b₈
  elim₃-[⋚?]-subtrans {a = 𝟎}  {b = 𝐒 b}{c = 𝐒 c} {𝑇} {b₂}{b₃}{b₄}{b₅}{b₆}{𝑇} {b₈}{b₉} _  _  _  ab bc = <> -- b₁ → b₇
  elim₃-[⋚?]-subtrans {a = 𝐒 a}{b = 𝟎}  {c = 𝟎}   {b₁}{b₂}{𝑇} {b₄}{𝑇} {b₆}{b₇}{b₈}{𝑇}  _  _  _  ab bc = <> -- b₃ b₅ → b₉
  elim₃-[⋚?]-subtrans {a = 𝐒 a}{b = 𝟎}  {c = 𝐒 c} {b₁}{b₂}{𝑇} {𝑇} {b₅}{b₆}{𝑇} {𝑇} {𝑇}  _  _  _  ab bc = substitute₁ₗ(IsTrue) elim₃-const <> -- b₃ b₄ → b₇ b₈ b₉
  elim₃-[⋚?]-subtrans {a = 𝐒 a}{b = 𝐒 b}{c = 𝟎}   {b₁}{b₂}{b₃}{b₄}{b₅}{𝑇} {b₇}{b₈}{𝑇}  _  _  _  ab bc = <> -- b₆ → b₉
  elim₃-[⋚?]-subtrans {a = 𝐒 a}{b = 𝐒 b}{c = 𝐒 c} {b₁}{b₂}{b₃}{b₄}{b₅}{b₆}{b₇}{b₈}{b₉} p7 p8 p9 ab bc = elim₃-[⋚?]-subtrans {a = a}{b = b}{c = c} p7 p8 p9 ab bc

  elim₃-[⋚?]-trans : IsTrue((b₁ && b₃) →? b₂) → IsTrue(Charge.elim₃ b₁ b₂ b₃ (_⋚?_ {an}{bn} a b)) → IsTrue(Charge.elim₃ b₁ b₂ b₃ (_⋚?_ {bn}{cn} b c)) → IsTrue(Charge.elim₃ b₁ b₂ b₃ (_⋚?_ {an}{cn} a c))
  elim₃-[⋚?]-trans           {a = 𝟎}   {𝟎}   {c = 𝟎}   p ab bc = bc
  elim₃-[⋚?]-trans           {a = 𝟎}   {𝟎}   {c = 𝐒 c} p ab bc = bc
  elim₃-[⋚?]-trans           {a = 𝐒 a} {𝐒 b} {c = 𝟎}   p ab bc = bc
  elim₃-[⋚?]-trans           {a = 𝟎}   {𝐒 b} {c = 𝐒 c} p ab bc = ab
  elim₃-[⋚?]-trans           {a = 𝐒 a} {𝟎}   {c = 𝟎}   p ab bc = ab
  elim₃-[⋚?]-trans {𝑇}{𝑇}{𝑇} {a = 𝟎}   {𝐒 b} {c = 𝟎}   p ab bc = <>
  elim₃-[⋚?]-trans {𝑇}{𝑇}{𝑇} {a = 𝐒 a} {𝟎}   {c = 𝐒 c} p ab bc = substitute₁ₗ(IsTrue) elim₃-const <>
  elim₃-[⋚?]-trans           {a = 𝐒 a} {𝐒 b} {c = 𝐒 c} p ab bc = elim₃-[⋚?]-trans {a = a} {b} {c = c} p ab bc

  elim₃-[⋚?]-cover₂ : IsTrue(bₗ₁ || bᵣ₁) → IsTrue(bₗ₂ || bᵣ₂) → IsTrue(bₗ₃ || bᵣ₃) → IsTrue((Charge.elim₃ bₗ₁ bₗ₂ bₗ₃ (_⋚?_ {an}{bn} a b)) || (Charge.elim₃ bᵣ₁ bᵣ₂ bᵣ₃ (_⋚?_ {an}{bn} a b)))
  elim₃-[⋚?]-cover₂ {a = 𝟎}  {𝟎}   p1 p2 p3 = p2
  elim₃-[⋚?]-cover₂ {a = 𝟎}  {𝐒 b} p1 p2 p3 = p1
  elim₃-[⋚?]-cover₂ {a = 𝐒 a}{𝟎}   p1 p2 p3 = p3
  elim₃-[⋚?]-cover₂ {a = 𝐒 a}{𝐒 b}          = elim₃-[⋚?]-cover₂ {a = a}{b}

  elim₃-[⋚?]-cover₃ : IsTrue(bₗ₁ || bₘ₁ || bᵣ₁) → IsTrue(bₗ₂ || bₘ₂ || bᵣ₂) → IsTrue(bₗ₃ || bₘ₃ || bᵣ₃) → IsTrue((Charge.elim₃ bₗ₁ bₗ₂ bₗ₃ (_⋚?_ {an}{bn} a b)) || (Charge.elim₃ bₘ₁ bₘ₂ bₘ₃ (_⋚?_ {an}{bn} a b)) || (Charge.elim₃ bᵣ₁ bᵣ₂ bᵣ₃ (_⋚?_ {an}{bn} a b)))
  elim₃-[⋚?]-cover₃ {a = 𝟎}  {𝟎}   p1 p2 p3 = p2
  elim₃-[⋚?]-cover₃ {a = 𝟎}  {𝐒 b} p1 p2 p3 = p1
  elim₃-[⋚?]-cover₃ {a = 𝐒 a}{𝟎}   p1 p2 p3 = p3
  elim₃-[⋚?]-cover₃ {a = 𝐒 a}{𝐒 b}          = elim₃-[⋚?]-cover₃ {a = a}{b}

  elim₃-[⋚?]-disjoint₂ : IsTrue(bₗ₁ != bᵣ₁) → IsTrue(bₗ₂ != bᵣ₂) → IsTrue(bₗ₃ != bᵣ₃) → IsTrue(!((Charge.elim₃ bₗ₁ bₗ₂ bₗ₃ (_⋚?_ {an}{bn} a b)) && (Charge.elim₃ bᵣ₁ bᵣ₂ bᵣ₃ (_⋚?_ {an}{bn} a b))))
  elim₃-[⋚?]-disjoint₂ {_} {_} {_} {_} {_} {_} {𝐒 x} {𝐒 x₁} {𝐒 x₂} {𝐒 x₃} p1 p2 p3 = elim₃-[⋚?]-disjoint₂ {_} {_} {_} {_} {_} {_} {x} {x₁} {x₂} {x₃} p1 p2 p3
  elim₃-[⋚?]-disjoint₂ {_} {_} {𝑇} {𝑇} {_} {_} {𝐒 x} {𝐒 x₁} {𝟎} {𝟎} p1 p2 p3 = p2
  elim₃-[⋚?]-disjoint₂ {_} {_} {𝑇} {𝐹} {_} {_} {𝐒 x} {𝐒 x₁} {𝟎} {𝟎} p1 p2 p3 = <>
  elim₃-[⋚?]-disjoint₂ {_} {_} {𝐹} {𝑇} {_} {_} {𝐒 x} {𝐒 x₁} {𝟎} {𝟎} p1 p2 p3 = <>
  elim₃-[⋚?]-disjoint₂ {_} {_} {𝐹} {𝐹} {_} {_} {𝐒 x} {𝐒 x₁} {𝟎} {𝟎} p1 p2 p3 = <>
  {-# CATCHALL #-}
  elim₃-[⋚?]-disjoint₂ {𝑇} {𝑇} {_} {_} {_} {_} {𝐒 x} {𝐒 x₁} {𝟎} {𝐒 x₂} p1 p2 p3 = p1
  {-# CATCHALL #-}
  elim₃-[⋚?]-disjoint₂ {𝑇} {𝐹} {_} {_} {_} {_} {𝐒 x} {𝐒 x₁} {𝟎} {𝐒 x₂} p1 p2 p3 = <>
  {-# CATCHALL #-}
  elim₃-[⋚?]-disjoint₂ {𝐹} {𝑇} {_} {_} {_} {_} {𝐒 x} {𝐒 x₁} {𝟎} {𝐒 x₂} p1 p2 p3 = <>
  {-# CATCHALL #-}
  elim₃-[⋚?]-disjoint₂ {𝐹} {𝐹} {_} {_} {_} {_} {𝐒 x} {𝐒 x₁} {𝟎} {𝐒 x₂} p1 p2 p3 = <>
  elim₃-[⋚?]-disjoint₂ {_} {_} {_} {_} {𝑇} {𝑇} {𝐒 x} {𝐒 x₁} {𝐒 x₂} {𝟎} p1 p2 p3 = p3
  elim₃-[⋚?]-disjoint₂ {_} {_} {_} {_} {𝑇} {𝐹} {𝐒 x} {𝐒 x₁} {𝐒 x₂} {𝟎} p1 p2 p3 = <>
  elim₃-[⋚?]-disjoint₂ {_} {_} {_} {_} {𝐹} {𝑇} {𝐒 x} {𝐒 x₁} {𝐒 x₂} {𝟎} p1 p2 p3 = <>
  elim₃-[⋚?]-disjoint₂ {_} {_} {_} {_} {𝐹} {𝐹} {𝐒 x} {𝐒 x₁} {𝐒 x₂} {𝟎} p1 p2 p3 = <>

open import Data.Boolean.Stmt.Logic
import      Numeral.Natural.Relation as ℕ

[≤]-reflexivity-raw : (a ≤ a)
[≤]-reflexivity-raw{a = a} = [↔]-to-[←] IsTrue.is-𝑇 (elim₃-[⋚?]-refl {a = a})

[≡]-reflexivity-raw : (a ≡ a)
[≡]-reflexivity-raw{a = a} = [↔]-to-[←] IsTrue.is-𝑇 (elim₃-[⋚?]-refl {a = a})

[≥]-reflexivity-raw : (a ≥ a)
[≥]-reflexivity-raw{a = a} = [↔]-to-[←] IsTrue.is-𝑇 (elim₃-[⋚?]-refl {a = a})

[<]-irreflexivity-raw : ¬(a < a)
[<]-irreflexivity-raw{a = a} = [↔]-to-[→] false-true-opposites ([↔]-to-[←] IsFalse.is-𝐹 (elim₃-[⋚?]-refl {a = a}))

[≢]-irreflexivity-raw : ¬(a ≢ a)
[≢]-irreflexivity-raw{a = a} = [↔]-to-[→] false-true-opposites ([↔]-to-[←] IsFalse.is-𝐹 (elim₃-[⋚?]-refl {a = a}))

[>]-irreflexivity-raw : ¬(a > a)
[>]-irreflexivity-raw{a = a} = [↔]-to-[→] false-true-opposites ([↔]-to-[←] IsFalse.is-𝐹 (elim₃-[⋚?]-refl {a = a}))

open import Logic.Propositional.Proofs.Structures
open import Structure.Function
open import Structure.Relator.Properties

[≡]-symmetry-raw : (a ≡ b) → (b ≡ a)
[≡]-symmetry-raw{a = a} = sub₂(Id)(_→ᶠ_) (congruence₁(IsTrue) (elim₃-[⋚?]-sym {a = a}))

[≢]-symmetry-raw : (a ≢ b) → (b ≢ a)
[≢]-symmetry-raw{a = a} = sub₂(Id)(_→ᶠ_) (congruence₁(IsTrue) (elim₃-[⋚?]-sym {a = a}))

[≤]-antisymmetry-raw : (a ≤ b) → (b ≤ a) → (a ≡ b)
[≤]-antisymmetry-raw {a = 𝟎} {b = 𝟎}     _ _ = <>
[≤]-antisymmetry-raw {a = 𝐒 a} {b = 𝐒 b} p q = [≤]-antisymmetry-raw {a = a}{b = b} p q

[≡]-transitivity-raw : (a ≡ b) → (b ≡ c) → (a ≡ c)
[≡]-transitivity-raw {a = a} = elim₃-[⋚?]-trans {a = a} <>

[≤]-transitivity-raw : (a ≤ b) → (b ≤ c) → (a ≤ c)
[≤]-transitivity-raw {a = a} = elim₃-[⋚?]-trans {a = a} <>

[≥]-transitivity-raw : (a ≥ b) → (b ≥ c) → (a ≥ c)
[≥]-transitivity-raw {a = a} = elim₃-[⋚?]-trans {a = a} <>

[<]-transitivity-raw : (a < b) → (b < c) → (a < c)
[<]-transitivity-raw {a = a} = elim₃-[⋚?]-trans {a = a} <>

[>]-transitivity-raw : (a > b) → (b > c) → (a > c)
[>]-transitivity-raw {a = a} = elim₃-[⋚?]-trans {a = a} <>

[<]-asymmetry-raw : (a < b) → ¬(b < a)
[<]-asymmetry-raw {a = a}{b = b} = [<]-irreflexivity-raw {a = a} ∘₂ [<]-transitivity-raw {a = a}{b = b}

[>]-asymmetry-raw : (a > b) → ¬(b > a)
[>]-asymmetry-raw {a = a}{b = b} = [>]-irreflexivity-raw {a = a} ∘₂ [>]-transitivity-raw {a = a}{b = b}

[<][≤]-subtransitivityₗ-raw : (a ≤ b) → (b < c) → (a < c)
[<][≤]-subtransitivityₗ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[<][≤]-subtransitivityᵣ-raw : (a < b) → (b ≤ c) → (a < c)
[<][≤]-subtransitivityᵣ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[<][≡]-subtransitivityₗ-raw : (a ≡ b) → (b < c) → (a < c)
[<][≡]-subtransitivityₗ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[<][≡]-subtransitivityᵣ-raw : (a < b) → (b ≡ c) → (a < c)
[<][≡]-subtransitivityᵣ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[≤][≡]-subtransitivityₗ-raw : (a ≡ b) → (b ≤ c) → (a ≤ c)
[≤][≡]-subtransitivityₗ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[≤][≡]-subtransitivityᵣ-raw : (a ≤ b) → (b ≡ c) → (a ≤ c)
[≤][≡]-subtransitivityᵣ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[>][≥]-subtransitivityₗ-raw : (a ≥ b) → (b > c) → (a > c)
[>][≥]-subtransitivityₗ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[>][≥]-subtransitivityᵣ-raw : (a > b) → (b ≥ c) → (a > c)
[>][≥]-subtransitivityᵣ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[>][≡]-subtransitivityₗ-raw : (a ≡ b) → (b > c) → (a > c)
[>][≡]-subtransitivityₗ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[>][≡]-subtransitivityᵣ-raw : (a > b) → (b ≡ c) → (a > c)
[>][≡]-subtransitivityᵣ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[≥][≡]-subtransitivityₗ-raw : (a ≡ b) → (b ≥ c) → (a ≥ c)
[≥][≡]-subtransitivityₗ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

[≥][≡]-subtransitivityᵣ-raw : (a ≥ b) → (b ≡ c) → (a ≥ c)
[≥][≡]-subtransitivityᵣ-raw {a = a} = elim₃-[⋚?]-subtrans {a = a} <> <> <>

open import Numeral.Charge.Proofs.Bool

instance
  [≡][≤]-sub : (_≡_ {an}{bn}) ⊆₂ (_≤_)
  [≡][≤]-sub = intro(elim₃-sub{_}{𝐹}{𝑇}{𝐹} <> <> <>)

instance
  [<][≤]-sub : (_<_ {an}{bn}) ⊆₂ (_≤_)
  [<][≤]-sub = intro(elim₃-sub{_}{𝑇}{𝐹}{𝐹} <> <> <>)

instance
  [≡][≥]-sub : (_≡_ {an}{bn}) ⊆₂ (_≥_)
  [≡][≥]-sub = intro(elim₃-sub{_}{𝐹}{𝑇}{𝐹} <> <> <>)

instance
  [>][≥]-sub : (_>_ {an}{bn}) ⊆₂ (_≥_)
  [>][≥]-sub = intro(elim₃-sub{_}{𝐹}{𝐹}{𝑇} <> <> <>)

instance
  [<][≢]-sub : (_<_ {an}{bn}) ⊆₂ (_≢_)
  [<][≢]-sub = intro(elim₃-sub{_}{𝑇}{𝐹}{𝐹} <> <> <>)

instance
  [>][≢]-sub : (_>_ {an}{bn}) ⊆₂ (_≢_)
  [>][≢]-sub = intro(elim₃-sub{_}{𝐹}{𝐹}{𝑇} <> <> <>)

instance
  [≤][≥]-swap-sub : (_≤_ {an}{bn}) ⊆₂ (swap(_≥_))
  [≤][≥]-swap-sub = intro(\{a} → sub₂(Id)(_→ᶠ_) (congruence₁(IsTrue) (elim₃-[⋚?]-sym {a = a})))

instance
  [≥][≤]-swap-sub : (_≥_ {an}{bn}) ⊆₂ (swap(_≤_))
  [≥][≤]-swap-sub = intro(\{a} → sub₂(Id)(_→ᶠ_) (congruence₁(IsTrue) (elim₃-[⋚?]-sym {a = a})))

instance
  [<][>]-swap-sub : (_<_ {an}{bn}) ⊆₂ (swap(_>_))
  [<][>]-swap-sub = intro(\{a} → sub₂(Id)(_→ᶠ_) (congruence₁(IsTrue) (elim₃-[⋚?]-sym {a = a})))

instance
  [>][<]-swap-sub : (_>_ {an}{bn}) ⊆₂ (swap(_<_))
  [>][<]-swap-sub = intro(\{a} → sub₂(Id)(_→ᶠ_) (congruence₁(IsTrue) (elim₃-[⋚?]-sym {a = a})))



[≡]-or-[≢] : (a ≡ b) ∨ (a ≢ b)
[≡]-or-[≢] {a = a} = [↔]-to-[→] IsTrue.preserves-[||][∨] (elim₃-[⋚?]-cover₂ {a = a} <> <> <>)

[<]-or-[≥] : (a < b) ∨ (a ≥ b)
[<]-or-[≥] {a = a} = [↔]-to-[→] IsTrue.preserves-[||][∨] (elim₃-[⋚?]-cover₂ {a = a} <> <> <>)

[≤]-or-[>] : (a ≤ b) ∨ (a > b)
[≤]-or-[>] {a = a} = [↔]-to-[→] IsTrue.preserves-[||][∨] (elim₃-[⋚?]-cover₂ {a = a} <> <> <>)

[≤]-or-[≥] : (a ≤ b) ∨ (a ≥ b)
[≤]-or-[≥] {a = a} = [↔]-to-[→] IsTrue.preserves-[||][∨] (elim₃-[⋚?]-cover₂ {a = a} <> <> <>)

[<][≡][>]-trichotomy-raw : (a < b) ∨ (a ≡ b) ∨ (a > b)
[<][≡][>]-trichotomy-raw {a = a} = [∨]-elim
  ([∨]-introₗ ∘ [↔]-to-[→] IsTrue.preserves-[||][∨])
  [∨]-introᵣ
  ([↔]-to-[→] IsTrue.preserves-[||][∨] (elim₃-[⋚?]-cover₃ {a = a} <> <> <>))



[≤]-minimum : ⦃ pos : ℕ.Positive(n) ⦄ → (minimum{n} ≤ a)
[≤]-minimum {n = 𝐒 _}{a = 𝟎}   = <>
[≤]-minimum {n = 𝐒 _}{a = 𝐒 _} = <>

[≥]-minimum : ⦃ pos : ℕ.Positive(n) ⦄ → (a ≥ minimum{n})
[≥]-minimum {n = 𝐒 _}{a = 𝟎}   = <>
[≥]-minimum {n = 𝐒 _}{a = 𝐒 _} = <>

[≤]-maximum : ⦃ pos : ℕ.Positive(n) ⦄ → (bound a ℕ.≤ n) → (a ≤ maximum{n})
[≤]-maximum {n = 𝐒 𝟎}   {a = 𝟎}          (ℕ.succ _) = <>
[≤]-maximum {n = 𝐒(𝐒 _)}{a = 𝟎}          (ℕ.succ _) = <>
[≤]-maximum {n = 𝐒(𝐒 x)}{a = 𝐒 a}        (ℕ.succ p) = [≤]-maximum {a = a} p
[≤]-maximum {n = 𝐒 𝟎}   {a = 𝐒 {𝟎} ()}   (ℕ.succ _)
[≤]-maximum {n = 𝐒 𝟎}   {a = 𝐒 {𝐒 n} a}  (ℕ.succ ())

[≤]-maximum₌ : (a ≤ maximum{bound(a)} ⦃ 𝕟-to-positive-bound a ⦄)
[≤]-maximum₌ {𝐒 𝟎}   {𝟎}   = <>
[≤]-maximum₌ {𝐒(𝐒 n)}{𝟎}   = <>
[≤]-maximum₌ {𝐒(𝐒 n)}{𝐒 a} = [≤]-maximum₌ {(𝐒 n)}{a}

[<]-minimumᵣ : ⦃ pos : ℕ.Positive(n) ⦄ → ¬(a < minimum{n})
[<]-minimumᵣ {n = 𝐒 n}{a = 𝟎}   ()
[<]-minimumᵣ {n = 𝐒 n}{a = 𝐒 a} ()

[>]-minimumₗ : ⦃ pos : ℕ.Positive(n) ⦄ → ¬(minimum{n} > a)
[>]-minimumₗ {n = 𝐒 n}{a = 𝟎}   ()
[>]-minimumₗ {n = 𝐒 n}{a = 𝐒 a} ()

[≤]-minimumᵣ : ⦃ pos : ℕ.Positive(n) ⦄ → (a ≤ minimum{n}) → (a ≡ minimum{n})
[≤]-minimumᵣ {n = 𝐒 n}{a = 𝟎}   _ = <>
[≤]-minimumᵣ {n = 𝐒 n}{a = 𝐒 a} ()

[≥]-minimumₗ : ⦃ pos : ℕ.Positive(n) ⦄ → (minimum{n} ≥ a) → (a ≡ minimum{n})
[≥]-minimumₗ {n = 𝐒 n}{a = 𝟎}   _ = <>
[≥]-minimumₗ {n = 𝐒 n}{a = 𝐒 a} ()

[<]-minimumₗ : ⦃ pos : ℕ.Positive(n) ⦄ → ¬(𝐒(a) < minimum{n})
[<]-minimumₗ {𝐒 n} ()

[>]-minimumᵣ : ⦃ pos : ℕ.Positive(n) ⦄ → ¬(minimum{n} > 𝐒(a))
[>]-minimumᵣ {𝐒 n} ()

[≤]-maximums : ⦃ posₗ : ℕ.Positive(an) ⦄ → ⦃ posᵣ : ℕ.Positive(bn) ⦄ → (an ℕ.≤ bn) → (maximum{an} ≤ maximum{bn})
[≤]-maximums = [≤]-maximum {a = maximum}

[<]-of-successor : a < 𝐒(a)
[<]-of-successor {𝐒 n}{𝟎}   = <>
[<]-of-successor {𝐒 n}{𝐒 a} = [<]-of-successor {n}{a}

[>]-of-successor : 𝐒(a) > a
[>]-of-successor {𝐒 n}{𝟎}   = <>
[>]-of-successor {𝐒 n}{𝐒 a} = [>]-of-successor {n}{a}

[≤]-of-successor : a ≤ 𝐒(a)
[≤]-of-successor {𝐒 n}{𝟎}   = <>
[≤]-of-successor {𝐒 n}{𝐒 a} = [≤]-of-successor {n}{a}

[≥]-of-successor : 𝐒(a) ≥ a
[≥]-of-successor {𝐒 n}{𝟎}   = <>
[≥]-of-successor {𝐒 n}{𝐒 a} = [≥]-of-successor {n}{a}

[≤][<]-convert : (a ≤ b) ↔ (a < 𝐒(b))
[≤][<]-convert {a = 𝟎}  {b = 𝟎}   = [↔]-intro (const <>) (const <>)
[≤][<]-convert {a = 𝟎}  {b = 𝐒 b} = [↔]-intro (const <>) (const <>)
[≤][<]-convert {a = 𝐒 a}{b = 𝟎}   = [↔]-intro (empty ∘ [<]-minimumᵣ{a = a}) \()
[≤][<]-convert {a = 𝐒 a}{b = 𝐒 b} = [≤][<]-convert {a = a}{b = b}

[<][≤]-convert : (a < b) ↔ (𝐒(a) ≤ b)
[<][≤]-convert {a = 𝟎}  {b = 𝟎}   = [↔]-intro (\()) \()
[<][≤]-convert {a = a@𝟎}{b = 𝐒 b} = [↔]-intro (const <>) (const([≤]-minimum {bound a}{a = b}))
[<][≤]-convert {a = 𝐒 a}{b = b@𝟎} = [↔]-intro (empty ∘ [≤]-minimumᵣ{bound b}{a = 𝐒(𝐒 a)}) (empty ∘ [<]-minimumₗ{bound b}{a = a})
[<][≤]-convert {a = 𝐒 a}{b = 𝐒 b} = [<][≤]-convert {a = a}{b = b}

---------------------------------------------------------------------------------------------------
-- Instances

instance
  [≡]-reflexivity : Reflexivity(_≡_ {n})
  [≡]-reflexivity {n} = intro(\{a} → [≡]-reflexivity-raw {a = a})

instance
  [≤]-reflexivity : Reflexivity(_≤_ {n})
  [≤]-reflexivity {n} = intro(\{a} → [≤]-reflexivity-raw {a = a})

instance
  [≥]-reflexivity : Reflexivity(_≥_ {n})
  [≥]-reflexivity {n} = intro(\{a} → [≥]-reflexivity-raw {a = a})

instance
  [≢]-irreflexivity : Irreflexivity(_≢_ {n})
  [≢]-irreflexivity {n} = intro(\{a} → [≢]-irreflexivity-raw {a = a})

instance
  [<]-irreflexivity : Irreflexivity(_<_ {n})
  [<]-irreflexivity {n} = intro(\{a} → [<]-irreflexivity-raw {a = a})

instance
  [>]-irreflexivity : Irreflexivity(_>_ {n})
  [>]-irreflexivity {n} = intro(\{a} → [>]-irreflexivity-raw {a = a})

instance
  [≡]-symmetry : Symmetry(_≡_ {n})
  [≡]-symmetry {n} = intro(\{a}{b} → [≡]-symmetry-raw {a = a}{b = b})

instance
  [≢]-symmetry : Symmetry(_≢_ {n})
  [≢]-symmetry {n} = intro(\{a}{b} → [≢]-symmetry-raw {a = a}{b = b})

instance
  [≡]-transitivity : Transitivity(_≡_ {n})
  [≡]-transitivity {n} = intro(\{a}{b}{c} → [≡]-transitivity-raw {a = a}{b = b}{c = c})

instance
  [≤]-transitivity : Transitivity(_≤_ {n})
  [≤]-transitivity {n} = intro(\{a}{b}{c} → [≤]-transitivity-raw {a = a}{b = b}{c = c})

instance
  [≥]-transitivity : Transitivity(_≥_ {n})
  [≥]-transitivity {n} = intro(\{a}{b}{c} → [≥]-transitivity-raw {a = a}{b = b}{c = c})

instance
  [<]-transitivity : Transitivity(_<_ {n})
  [<]-transitivity {n} = intro(\{a}{b}{c} → [<]-transitivity-raw {a = a}{b = b}{c = c})

instance
  [>]-transitivity : Transitivity(_>_ {n})
  [>]-transitivity {n} = intro(\{a}{b}{c} → [>]-transitivity-raw {a = a}{b = b}{c = c})

instance
  [≡]-Id-sub : (_≡_ {n}{n}) ⊆₂ Id
  [≡]-Id-sub = intro p where
    p : (a ≡ b) → Id a b
    p {a = 𝟎}   {b = 𝟎}   eq = intro
    p {a = 𝐒 a} {b = 𝐒 b} eq = congruence₁(𝐒) (p{a = a}{b = b} eq)

import      Structure.Setoid as Setoid
open import Structure.Relator.Equivalence

instance
  𝕟-equiv : Setoid.Equiv(𝕟(n))
  𝕟-equiv = Setoid.intro(_≡_) ⦃ intro ⦄
