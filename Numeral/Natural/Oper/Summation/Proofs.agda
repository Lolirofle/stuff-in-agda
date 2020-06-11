module Numeral.Natural.Oper.Summation.Proofs where

import      Lvl
open import Data.List
open import Data.List.Functions
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Structure.Function
open import Structure.Operator.Monoid
open import Structure.Operator
open import Structure.Setoid.WithLvl
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable _▫_ : T → T → T

open        Data.List.Functions.LongOper
open import Data.List.Proofs
open import Functional as Fn using (_$_ ; _∘_ ; const)
import      Function.Equals as Fn
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Structure
import      Numeral.Natural.Oper.Summation
open import Numeral.Natural.Oper.Summation.Range
open import Numeral.Natural.Relation.Order
import      Structure.Function.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator.Proofs.Util
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity

module _ where
  open import Relator.Equals hiding (_≡_)
  open import Relator.Equals.Proofs.Equiv

  Range-empty : ∀{a} → (a ‥ a ≡ ∅)
  Range-empty {𝟎} = [≡]-intro
  Range-empty {𝐒 a} rewrite Range-empty {a} = [≡]-intro
  {-# REWRITE Range-empty #-}

  Range-reversed : ∀{a b} → ⦃ _ : (a ≥ b) ⦄ → (a ‥ b ≡ ∅)
  Range-reversed {a}   {𝟎}   ⦃ [≤]-minimum ⦄ = [≡]-intro
  Range-reversed {𝐒 a} {𝐒 b} ⦃ [≤]-with-[𝐒] ⦃ p ⦄ ⦄
    rewrite Range-reversed {a} {b} ⦃ p ⦄
    = [≡]-intro

  Range-succ : ∀{a b} → (map 𝐒(a ‥ b) ≡ 𝐒(a) ‥ 𝐒(b))
  Range-succ = [≡]-intro

  Range-prepend : ∀{a b} → ⦃ _ : (a < b) ⦄ → (a ‥ b ≡ prepend a (𝐒(a) ‥ b))
  Range-prepend {𝟎}   {𝐒 b} = [≡]-intro
  Range-prepend {𝐒 a} {𝐒 b} ⦃ [≤]-with-[𝐒] ⦃ ab ⦄ ⦄ rewrite Range-prepend {a} {b} ⦃ ab ⦄ = [≡]-intro

  Range-postpend : ∀{a b} → ⦃ _ : (a < 𝐒(b)) ⦄ → (a ‥ 𝐒(b) ≡ postpend b (a ‥ b))
  Range-postpend {𝟎}   {𝟎}   ⦃ [≤]-with-[𝐒] ⦄ = [≡]-intro
  Range-postpend {𝟎}   {𝐒 b} ⦃ [≤]-with-[𝐒] ⦄  = congruence₁(prepend 𝟎) $
    map 𝐒(𝟎 ‥ 𝐒(b))                 🝖[ _≡_ ]-[ congruence₁(map 𝐒) (Range-postpend {𝟎}{b}) ]
    map 𝐒(postpend b (𝟎 ‥ b))       🝖[ _≡_ ]-[ map-postpend ]
    postpend (𝐒(b)) (map 𝐒(𝟎 ‥ b))  🝖-end
  Range-postpend {𝐒 a} {𝐒 b} ⦃ [≤]-with-[𝐒] ⦃ 𝐒ab ⦄ ⦄
    rewrite Range-postpend {a} {b} ⦃ 𝐒ab ⦄
    = map-postpend

  Range-length : ∀{a b} → (length(a ‥ b) ≡ b −₀ a)
  Range-length {𝟎} {𝟎} = [≡]-intro
  Range-length {𝟎} {𝐒 b}
    rewrite length-map{f = 𝐒}{x = 𝟎 ‥ b}
    rewrite Range-length {𝟎} {b}
    = congruence₁(𝐒) [≡]-intro
  Range-length {𝐒 a} {𝟎} = [≡]-intro
  Range-length {𝐒 a} {𝐒 b}
    rewrite length-map{f = 𝐒}{x = a ‥ b}
    rewrite Range-length {a} {b}
    = [≡]-intro

  Range-length-zero : ∀{b} → (length(𝟎 ‥ b) ≡ b)
  Range-length-zero {b} = Range-length {𝟎}{b}

  Range-singleton : ∀{a} → (a ‥ 𝐒(a) ≡ singleton(a))
  Range-singleton {𝟎} = [≡]-intro
  Range-singleton {𝐒 a}
    rewrite Range-singleton {a}
    = [≡]-intro
  {-# REWRITE Range-singleton #-}

  Range-concat : ∀{a b c} → ⦃ ab : (a ≤ b) ⦄ ⦃ bc : (b < c) ⦄ → ((a ‥ b) ++ (b ‥ c) ≡ a ‥ c)
  Range-concat {𝟎} {𝟎}   {𝐒 c} ⦃ [≤]-minimum ⦄ ⦃ [≤]-with-[𝐒] ⦄ = [≡]-intro
  Range-concat {𝟎} {𝐒 b} {𝐒 c} ⦃ [≤]-minimum ⦄ ⦃ [≤]-with-[𝐒] ⦄ = congruence₁ (prepend 0) $
    map 𝐒(𝟎 ‥ b) ++ map 𝐒 (b ‥ c) 🝖[ _≡_ ]-[ map-[++] {l₁ = 𝟎 ‥ b}{l₂ = b ‥ c} ]-sym
    map 𝐒((𝟎 ‥ b) ++ (b ‥ c))     🝖[ _≡_ ]-[ congruence₁(map 𝐒) (Range-concat {𝟎} {b} {c}) ]
    map 𝐒(𝟎 ‥ c)                  🝖-end
  Range-concat {𝐒 a} {𝐒 b} {𝐒 c} ⦃ [≤]-with-[𝐒] ⦄ ⦃ [≤]-with-[𝐒] ⦄ =
    map 𝐒(a ‥ b) ++ map 𝐒 (b ‥ c) 🝖[ _≡_ ]-[ map-[++] {l₁ = a ‥ b}{l₂ = b ‥ c} ]-sym
    map 𝐒((a ‥ b) ++ (b ‥ c))     🝖[ _≡_ ]-[ congruence₁(map 𝐒) (Range-concat {a} {b} {c}) ]
    map 𝐒(a ‥ c)                  🝖-end

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ monoid : Monoid{T = T}(_▫_) ⦄ where
  open Numeral.Natural.Oper.Summation ⦃ monoid = monoid ⦄
  open Monoid(monoid) using (id) renaming (binary-operator to [▫]-binary-operator)
  open import Relator.Equals.Proofs.Equiv {T = ℕ}

  private variable f : ℕ → T
  private variable x a b c k n : ℕ
  private variable r r₁ r₂ : List(ℕ)

  ∑-empty : (∑(∅) f ≡ id)
  ∑-empty = reflexivity(Equiv._≡_ equiv)

  ∑-prepend : (∑(prepend x r) f ≡ f(x) ▫ ∑(r) f)
  ∑-prepend = reflexivity(Equiv._≡_ equiv)

  ∑-postpend : (∑(postpend x r) f ≡ ∑(r) f ▫ f(x))
  ∑-postpend {x = x} {r = ∅} {f = f} =
    ∑(postpend x empty) f 🝖[ _≡_ ]-[]
    ∑(prepend x empty) f  🝖[ _≡_ ]-[]
    f(x) ▫ (∑(empty) f)   🝖[ _≡_ ]-[]
    f(x) ▫ id             🝖[ _≡_ ]-[ identityᵣ(_▫_)(id) ]
    f(x)                  🝖[ _≡_ ]-[ identityₗ(_▫_)(id) ]-sym
    id ▫ f(x)             🝖[ _≡_ ]-[]
    (∑(empty) f) ▫ f(x)   🝖-end
  ∑-postpend {x = x} {r = r₀ ⊰ r} {f = f} =
    f(r₀) ▫ ∑(postpend x r) f  🝖[ _≡_ ]-[ congruence₂ᵣ(_▫_)(f(r₀)) (∑-postpend {x = x}{r = r}{f = f}) ]
    f(r₀) ▫ (∑(r) f ▫ f(x))    🝖[ _≡_ ]-[ associativity(_▫_) {f(r₀)}{∑(r) f}{f(x)} ]-sym
    (f(r₀) ▫ ∑(r) f) ▫ f(x)    🝖-end

open import Relator.Equals hiding (_≡_)
open import Relator.Equals.Proofs.Equiv
open Numeral.Natural.Oper.Summation ⦃ monoid = [+]-monoid ⦄ -- TODO: Generalize all the proofs

private variable f g : ℕ → ℕ
private variable x a b c k n : ℕ
private variable r r₁ r₂ : List(ℕ)

∑-compose : ∑(r) (f ∘ g) ≡ ∑(map g r) f
∑-compose {r = r}{f = f}{g = g} =
  ∑(r) (f ∘ g)                   🝖[ _≡_ ]-[]
  foldᵣ(_+_) 𝟎 (map(f ∘ g) r)   🝖[ _≡_ ]-[ congruence₁(foldᵣ(_+_) 𝟎) ⦃ foldᵣ-function ⦄ (map-preserves-[∘] {f = f}{g = g}{x = r}) ]
  foldᵣ(_+_) 𝟎 (map f(map g r)) 🝖[ _≡_ ]-[]
  ∑(map g r) f                   🝖-end

∑-add : (∑(r) f + ∑(r) g ≡ ∑(r) (x ↦ f(x) + g(x)))
∑-add {∅}      {f} {g} = reflexivity(_≡_)
∑-add {r₀ ⊰ r} {f} {g} =
  ∑(prepend r₀ r) f + ∑(prepend r₀ r) g    🝖[ _≡_ ]-[]
  (f(r₀) + ∑(r) f) + (g(r₀) + ∑(r) g)      🝖[ _≡_ ]-[ One.associate-commute4 {a = f(r₀)}{b = ∑(r) f}{c = g(r₀)}{d = ∑(r) g} (commutativity(_+_){x = ∑(r) f}{y = g(r₀)}) ]
  (f(r₀) + g(r₀)) + (∑(r) f + ∑(r) g)      🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(r₀) + g(r₀)) (∑-add {r} {f} {g}) ]
  (f(r₀) + g(r₀)) + ∑(r) (x ↦ f(x) + g(x)) 🝖[ _≡_ ]-[]
  ∑(prepend r₀ r) (x ↦ f(x) + g(x))        🝖-end

∑-scalar-multₗ : (∑(r) (x ↦ c ⋅ f(x)) ≡ c ⋅ (∑(r) f))
∑-scalar-multₗ {empty}        {c} {f} = [≡]-intro
∑-scalar-multₗ {prepend r₀ r} {c} {f} =
  (c ⋅ f(r₀)) + ∑(r) (x ↦ c ⋅ f(x)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(c ⋅ f(r₀)) (∑-scalar-multₗ {r}{c}{f}) ]
  (c ⋅ f(r₀)) + (c ⋅ (∑(r) f))      🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) {c}{f(r₀)}{∑(r) f} ]-sym
  c ⋅ (f(r₀) + (∑(r) f))            🝖-end

∑-scalar-multᵣ : (∑(r) (x ↦ f(x) ⋅ c) ≡ (∑(r) f) ⋅ c)
∑-scalar-multᵣ {empty}        {f} {c} = [≡]-intro
∑-scalar-multᵣ {prepend r₀ r} {f} {c} =
  (f(r₀) ⋅ c) + ∑(r) (x ↦ f(x) ⋅ c) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(r₀) ⋅ c) (∑-scalar-multᵣ {r}{f}{c}) ]
  (f(r₀) ⋅ c) + ((∑(r) f) ⋅ c)      🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) {f(r₀)}{∑(r) f}{c} ]-sym
  (f(r₀) + (∑(r) f)) ⋅ c            🝖-end

∑-const : (∑(r) (const c) ≡ c ⋅ length(r))
∑-const {empty}      {c} = reflexivity(_≡_)
∑-const {prepend x r}{c} = congruence₂ᵣ(_+_)(c) (∑-const {r}{c})

∑-zero : (∑(r) (const 𝟎) ≡ 𝟎)
∑-zero {r} = ∑-const {r}{𝟎}

∑-singleton : (∑(singleton(a)) f ≡ f(a))
∑-singleton = reflexivity(_≡_)

∑-concat : (∑(r₁ ++ r₂) f ≡ ∑(r₁) f + ∑(r₂) f)
∑-concat {empty}        {r₂} {f} = [≡]-intro
∑-concat {prepend x r₁} {r₂} {f} =
  f(x) + ∑(r₁ ++ r₂) f      🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(x)) (∑-concat {r₁}{r₂}{f}) ]
  f(x) + (∑(r₁) f + ∑ r₂ f) 🝖[ _≡_ ]-[ associativity(_+_) {x = f(x)}{y = ∑(r₁) f}{z = ∑(r₂) f} ]-sym
  (f(x) + ∑(r₁) f) + ∑ r₂ f 🝖-end

instance
  ∑-binaryOperator : BinaryOperator ⦃ equiv-A₂ = Fn.[⊜]-equiv ⦄ (∑)
  BinaryOperator.congruence ∑-binaryOperator {r₁}{r₂} rr {f} {g} fg =
    ∑(r₁) f  🝖[ _≡_ ]-[]
    foldᵣ(_+_) 𝟎 (map f(r₁))  🝖[ _≡_ ]-[ congruence₁(foldᵣ(_+_) 𝟎) (congruence₂(map) ⦃ map-binaryOperator ⦄ fg rr) ]
    foldᵣ(_+_) 𝟎 (map g(r₂))  🝖[ _≡_ ]-[]
    ∑(r₂) g  🝖-end

∑-mult : ∀{r₁ r₂}{f g} → ((∑(r₁) f) ⋅ (∑(r₂) g) ≡ ∑(r₁) (x ↦ ∑(r₂) (y ↦ f(x) ⋅ g(y))))
∑-mult {empty}        {_} {f} {g} = [≡]-intro
∑-mult {prepend x₁ r₁} {empty} {f} {g} =
  𝟎                                                 🝖[ _≡_ ]-[ ∑-zero {r = prepend x₁ r₁} ]-sym
  ∑(prepend x₁ r₁) (x ↦ 𝟎)                          🝖[ _≡_ ]-[ congruence₂ᵣ(∑)(prepend x₁ r₁) (Fn.intro(\{x} → ∑-empty {f = y ↦ f(x) ⋅ g(y)})) ]-sym
  ∑(prepend x₁ r₁) (x ↦ ∑(empty) (y ↦ f(x) ⋅ g(y))) 🝖-end
∑-mult {prepend x₁ r₁} {prepend x₂ r₂} {f} {g} =
  (∑(prepend x₁ r₁) f) ⋅ (∑(prepend x₂ r₂) g)                                                               🝖[ _≡_ ]-[]
  (f(x₁) + (∑(r₁) f)) ⋅ (g(x₂) + (∑(r₂) g))                                                                 🝖[ _≡_ ]-[ OneTypeTwoOp.cross-distribute {a = f(x₁)}{b = ∑(r₁) f}{c = g(x₂)}{d = ∑(r₂) g} ]
  ((f(x₁) ⋅ g(x₂)) + ((∑(r₁) f) ⋅ g(x₂))) + ((f(x₁) ⋅ (∑(r₂) g)) + ((∑(r₁) f) ⋅ (∑(r₂) g)))                 🝖[ _≡_ ]-[ One.associate-commute4 {a = f(x₁) ⋅ g(x₂)}{b = (∑(r₁) f) ⋅ g(x₂)}{c = f(x₁) ⋅ (∑(r₂) g)}{d = (∑(r₁) f) ⋅ (∑(r₂) g)} (commutativity(_+_) {x = (∑(r₁) f) ⋅ g(x₂)}{y = f(x₁) ⋅ (∑(r₂) g)}) ]
  ((f(x₁) ⋅ g(x₂)) + (f(x₁) ⋅ (∑(r₂) g))) + (((∑(r₁) f) ⋅ g(x₂)) + ((∑(r₁) f) ⋅ (∑(r₂) g)))                 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_) ((f(x₁) ⋅ g(x₂)) + (f(x₁) ⋅ (∑(r₂) g))) p ]
  ((f(x₁) ⋅ g(x₂)) + (f(x₁) ⋅ (∑(r₂) g))) + (∑(r₁) (x ↦ (f(x) ⋅ g(x₂)) + (∑(r₂) (y ↦ f(x) ⋅ g(y)))))        🝖[ _≡_ ]-[ congruence₂ₗ(_+_) (∑(r₁) (x ↦ (f(x) ⋅ g(x₂)) + (∑(r₂) (y ↦ f(x) ⋅ g(y))))) (congruence₂ᵣ(_+_)(f(x₁) ⋅ g(x₂)) (∑-scalar-multₗ {r = r₂}{c = f(x₁)}{f = g})) ]-sym
  ((f(x₁) ⋅ g(x₂)) + (∑(r₂) (y ↦ f(x₁) ⋅ g(y)))) + (∑(r₁) (x ↦ (f(x) ⋅ g(x₂)) + (∑(r₂) (y ↦ f(x) ⋅ g(y))))) 🝖[ _≡_ ]-[]
  (∑(prepend x₂ r₂) (y ↦ f(x₁) ⋅ g(y))) + (∑(r₁) (x ↦ ∑(prepend x₂ r₂) (y ↦ f(x) ⋅ g(y))))                  🝖[ _≡_ ]-[]
  ∑(prepend x₁ r₁) (x ↦ ∑(prepend x₂ r₂) (y ↦ f(x) ⋅ g(y)))                                                 🝖-end
  where
    p =      
      ((∑(r₁) f) ⋅ g(x₂)) + ((∑(r₁) f) ⋅ (∑(r₂) g))                 🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) {x = ∑(r₁) f}{y = g(x₂)}{z = ∑(r₂) g} ]-sym
      (∑(r₁) f) ⋅ (g(x₂) + (∑(r₂) g))                               🝖[ _≡_ ]-[ ∑-scalar-multᵣ {r = r₁}{f = f}{c = g(x₂) + (∑(r₂) g)} ]-sym
      ∑(r₁) (x ↦ f(x) ⋅ (g(x₂) + (∑(r₂) g)))                        🝖[ _≡_ ]-[ congruence₂ᵣ(∑) r₁ (Fn.intro(\{x} → distributivityₗ(_⋅_)(_+_) {x = f(x)}{y = g(x₂)}{z = ∑(r₂) g})) ]
      ∑(r₁) (x ↦ (f(x) ⋅ g(x₂)) + (f(x) ⋅ (∑(r₂) g)))               🝖[ _≡_ ]-[ congruence₂ᵣ(∑) r₁ (Fn.intro(\{x} → congruence₂ᵣ(_+_) (f(x) ⋅ g(x₂)) (∑-scalar-multₗ {r = r₂}{c = f(x)}{f = g}))) ]-sym
      ∑(r₁) (x ↦ (f(x) ⋅ g(x₂)) + (∑(r₂) (y ↦ f(x) ⋅ g(y))))        🝖-end

∑-swap-nested : ∀{f : ℕ → ℕ → _}{r₁ r₂} → (∑(r₁) (a ↦ ∑(r₂) (b ↦ f(a)(b))) ≡ ∑(r₂) (b ↦ ∑(r₁) (a ↦ f(a)(b))))
∑-swap-nested {f} {empty}         {empty}         = [≡]-intro
∑-swap-nested {f} {empty}         {prepend x  r₂} =
  ∑(∅)(a ↦ ∑(x ⊰ r₂) (b ↦ f(a)(b)))  🝖[ _≡_ ]-[]
  𝟎                                  🝖[ _≡_ ]-[ ∑-zero {x ⊰ r₂} ]-sym
  ∑(x ⊰ r₂) (b ↦ 𝟎)                  🝖[ _≡_ ]-[]
  ∑(x ⊰ r₂) (b ↦ ∑(∅) (a ↦ f(a)(b))) 🝖-end
∑-swap-nested {f} {prepend x  r₁} {empty}         =
  ∑(x ⊰ r₁) (a ↦ ∑(∅) (b ↦ f(a)(b))) 🝖[ _≡_ ]-[]
  ∑(x ⊰ r₁) (b ↦ 𝟎)                  🝖[ _≡_ ]-[ ∑-zero {x ⊰ r₁} ]
  𝟎                                  🝖[ _≡_ ]-[]
  ∑(∅) (b ↦ ∑(x ⊰ r₁) (a ↦ f(a)(b))) 🝖-end
∑-swap-nested {f} {prepend x₁ r₁} {prepend x₂ r₂} =
  ∑(x₁ ⊰ r₁) (a ↦ ∑(x₂ ⊰ r₂) (b ↦ f(a)(b)))                                                       🝖[ _≡_ ]-[]
  ∑(x₁ ⊰ r₁) (a ↦ f(a)(x₂) + ∑(r₂) (b ↦ f(a)(b)))                                                 🝖[ _≡_ ]-[]
  (f(x₁)(x₂) + ∑(r₂) (b ↦ f(x₁)(b))) + ∑(r₁) (a ↦ f(a)(x₂) + ∑(r₂) (b ↦ f(a)(b)))                 🝖[ _≡_ ]-[]
  (f(x₁)(x₂) + ∑(r₂) (b ↦ f(x₁)(b))) + (∑(r₁) (a ↦ f(a)(x₂) + ∑(r₂) (b ↦ f(a)(b))))               🝖[ _≡_ ]-[ associativity(_+_) {x = f(x₁)(x₂)}{y = ∑(r₂) (b ↦ f(x₁)(b))} ]
  f(x₁)(x₂) + (∑(r₂) (b ↦ f(x₁)(b)) + (∑(r₁) (a ↦ f(a)(x₂) + ∑(r₂) (b ↦ f(a)(b)))))               🝖[ _≡_ ]-[]
  f(x₁)(x₂) + (∑(r₂) (b ↦ f(x₁)(b)) + (∑(r₁) (a ↦ ∑(x₂ ⊰ r₂) (b ↦ f(a)(b)))))                     🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(x₁)(x₂)) (congruence₂ᵣ(_+_)(∑(r₂) (b ↦ f(x₁)(b))) (∑-swap-nested {f}{r₁}{x₂ ⊰ r₂})) ]
  f(x₁)(x₂) + (∑(r₂) (b ↦ f(x₁)(b)) + (∑(x₂ ⊰ r₂) (b ↦ ∑(r₁) (a ↦ f(a)(b)))))                     🝖[ _≡_ ]-[]
  f(x₁)(x₂) + (∑(r₂) (b ↦ f(x₁)(b)) + (∑(r₁) (a ↦ f(a)(x₂)) + (∑(r₂) (b ↦ ∑(r₁) (a ↦ f(a)(b)))))) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(x₁)(x₂)) (symmetry(_≡_) (associativity(_+_) {x = ∑(r₂) (b ↦ f(x₁)(b))}{y = ∑(r₁) (a ↦ f(a)(x₂))})) ]
  f(x₁)(x₂) + ((∑(r₂) (b ↦ f(x₁)(b)) + ∑(r₁) (a ↦ f(a)(x₂))) + (∑(r₂) (b ↦ ∑(r₁) (a ↦ f(a)(b))))) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(x₁)(x₂)) (congruence₂(_+_) (commutativity(_+_) {x = ∑(r₂) (b ↦ f(x₁)(b))}{y = ∑(r₁) (a ↦ f(a)(x₂))}) (symmetry(_≡_) (∑-swap-nested {f}{r₁}{r₂}))) ]
  f(x₁)(x₂) + ((∑(r₁) (a ↦ f(a)(x₂)) + ∑(r₂) (b ↦ f(x₁)(b))) + ∑(r₁) (a ↦ ∑(r₂) (b ↦ f(a)(b))))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(x₁)(x₂)) (associativity(_+_) {x = ∑(r₁) (a ↦ f(a)(x₂))}{y = ∑(r₂) (b ↦ f(x₁)(b))}) ]
  f(x₁)(x₂) + (∑(r₁) (a ↦ f(a)(x₂)) + (∑(r₂) (b ↦ f(x₁)(b)) + ∑(r₁) (a ↦ ∑(r₂) (b ↦ f(a)(b)))))   🝖[ _≡_ ]-[]
  f(x₁)(x₂) + (∑(r₁) (a ↦ f(a)(x₂)) + (∑(x₁ ⊰ r₁) (a ↦ ∑(r₂) (b ↦ f(a)(b)))))                     🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(x₁)(x₂)) (congruence₂ᵣ(_+_)(∑(r₁) (a ↦ f(a)(x₂))) (∑-swap-nested {f}{x₁ ⊰ r₁}{r₂})) ]
  f(x₁)(x₂) + (∑(r₁) (a ↦ f(a)(x₂)) + (∑(r₂) (b ↦ ∑(x₁ ⊰ r₁) (a ↦ f(a)(b)))))                     🝖[ _≡_ ]-[]
  f(x₁)(x₂) + (∑(r₁) (a ↦ f(a)(x₂)) + (∑(r₂) (b ↦ f(x₁)(b) + ∑(r₁) (a ↦ f(a)(b)))))               🝖[ _≡_ ]-[ associativity(_+_) {x = f(x₁)(x₂)}{y = ∑(r₁) (a ↦ f(a)(x₂))} ]-sym
  (f(x₁)(x₂) + ∑(r₁) (a ↦ f(a)(x₂))) + (∑(r₂) (b ↦ f(x₁)(b) + ∑(r₁) (a ↦ f(a)(b))))               🝖[ _≡_ ]-[]
  ∑(x₂ ⊰ r₂) (b ↦ f(x₁)(b) + ∑(r₁) (a ↦ f(a)(b)))                                                 🝖[ _≡_ ]-[]
  ∑(x₂ ⊰ r₂) (b ↦ ∑(x₁ ⊰ r₁) (a ↦ f(a)(b)))                                                       🝖-end




∑-zero-range : (∑(a ‥ a) f ≡ 𝟎)
∑-zero-range {a}{f} = congruence₁ (r ↦ ∑(r) f) (Range-empty{a})

∑-single-range : (∑(a ‥ 𝐒(a)) f ≡ f(a))
∑-single-range {𝟎}  {f} = reflexivity(_≡_)
∑-single-range {𝐒 a}{f} =
  ∑ (map 𝐒(a ‥ 𝐒(a))) f       🝖[ _≡_ ]-[ ∑-compose {r = a ‥ 𝐒(a)}{f}{𝐒} ]-sym
  ∑ (a ‥ 𝐒(a)) (x ↦ f(𝐒(x)))  🝖[ _≡_ ]-[ ∑-single-range {a}{f ∘ 𝐒} ]
  f(𝐒(a))                     🝖-end

∑-step-range : (∑(𝐒(a) ‥ 𝐒(b)) f ≡ ∑(a ‥ b) (f ∘ 𝐒))
∑-step-range {a}{b}{f} = symmetry(_≡_) (∑-compose {r = a ‥ b}{f = f}{g = 𝐒})

∑-stepₗ-range : ⦃ _ : (a < b) ⦄ → (∑(a ‥ b) f ≡ f(a) + ∑(𝐒(a) ‥ b) f)
∑-stepₗ-range {𝟎}   {𝐒 b} {f} ⦃ [≤]-with-[𝐒] ⦃ ab ⦄ ⦄ = reflexivity(_≡_)
∑-stepₗ-range {𝐒 a} {𝐒 b} {f} ⦃ [≤]-with-[𝐒] ⦃ ab ⦄ ⦄ =
  ∑(𝐒(a) ‥ 𝐒(b)) f                                🝖[ _≡_ ]-[ ∑-step-range {a}{b}{f} ]
  ∑(a ‥ b) (f ∘ 𝐒)                                🝖[ _≡_ ]-[ ∑-stepₗ-range {a}{b}{f ∘ 𝐒} ]
  (f ∘ 𝐒)(a) + ∑(𝐒(a) ‥ b) (f ∘ 𝐒)                🝖[ _≡_ ]-[ congruence₂(_+_) (reflexivity(_≡_) {x = f(𝐒(a))}) (symmetry(_≡_) (∑-step-range {𝐒 a}{b}{f})) ]
  f(𝐒(a)) + ∑(𝐒(𝐒(a)) ‥ 𝐒(b)) f                   🝖-end

-- ∑-stepᵣ-range : ⦃ _ : (a < 𝐒(b)) ⦄ → (∑(a ‥ 𝐒(b)) f ≡ ∑(a ‥ b) f + f(b))
-- ∑-stepᵣ-range = ?

-- ∑-add-range : (∑(a ‥ a + b) f ≡ ∑(𝟎 ‥ b) (f ∘ (_+ a)))

∑-trans-range : ⦃ ab : (a ≤ b) ⦄ ⦃ bc : (b < c) ⦄ → (∑(a ‥ b) f + ∑(b ‥ c) f ≡ ∑(a ‥ c) f)
∑-trans-range {a}{b}{c} {f} =
  ∑(a ‥ b) f + ∑(b ‥ c) f 🝖[ _≡_ ]-[ ∑-concat{r₁ = a ‥ b}{r₂ = b ‥ c}{f = f} ]-sym
  ∑((a ‥ b) ++ (b ‥ c)) f 🝖[ _≡_ ]-[ congruence₁(r ↦ ∑(r) f) (Range-concat{a}{b}{c}) ]
  ∑(a ‥ c) f              🝖-end

-- TODO: Formulate ∑({(x,y). a ≤ x ≤ y ≤ b}) f ≡ ∑(a ‥ b) (x ↦ ∑(a ‥ x) (y ↦ f(x)(y))) ≡ ∑(a ‥ b) (x ↦ ∑(x ‥ b) (y ↦ f(x)(y))) ≡ ... and first prove a theorem stating that the order of a list does not matter
-- ∑-nested-dependent-range : ∀{f : ℕ → ℕ → _}{a b} → ?



∑-of-succ : (∑(r) (𝐒 ∘ f) ≡ (∑(r) f) + length(r))
∑-of-succ {empty}      {f} = [≡]-intro
∑-of-succ {prepend x r}{f} =
  ∑(x ⊰ r) (𝐒 ∘ f)                 🝖[ _≡_ ]-[]
  𝐒(f(x)) + ∑(r) (𝐒 ∘ f)           🝖[ _≡_ ]-[]
  𝐒(f(x) + ∑(r) (𝐒 ∘ f))           🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₂ᵣ(_+_)(f(x)) (∑-of-succ {r}{f})) ]
  𝐒(f(x) + ((∑(r) f) + length(r))) 🝖[ _≡_ ]-[ congruence₁(𝐒) (symmetry(_≡_) (associativity(_+_) {x = f(x)}{y = ∑(r) f}{z = length(r)})) ]
  𝐒((f(x) + (∑(r) f)) + length(r)) 🝖[ _≡_ ]-[]
  𝐒((∑(x ⊰ r) f) + length(r))      🝖[ _≡_ ]-[]
  (∑(x ⊰ r) f) + 𝐒(length(r))      🝖[ _≡_ ]-[]
  (∑(x ⊰ r) f) + length(x ⊰ r)     🝖-end

∑-even-sum : (∑(𝟎 ‥₌ n) (k ↦ 2 ⋅ k) ≡ n ⋅ 𝐒(n))
∑-even-sum {𝟎}   = [≡]-intro
∑-even-sum {𝐒 n} =
  ∑(𝟎 ‥₌ 𝐒(n)) (k ↦ 2 ⋅ k)                       🝖[ _≡_ ]-[]
  (2 ⋅ 𝟎) + ∑(1 ‥₌ 𝐒(n)) (k ↦ 2 ⋅ k)             🝖[ _≡_ ]-[]
  𝟎 + ∑(1 ‥₌ 𝐒(n)) (k ↦ 2 ⋅ k)                   🝖[ _≡_ ]-[]
  ∑(1 ‥₌ 𝐒(n)) (k ↦ 2 ⋅ k)                       🝖[ _≡_ ]-[]
  ∑(map 𝐒(𝟎 ‥₌ n)) (k ↦ 2 ⋅ k)                   🝖[ _≡_ ]-[ ∑-step-range {a = 𝟎}{b = 𝐒 n}{f = 2 ⋅_} ]
  ∑(𝟎 ‥₌ n) (k ↦ 2 ⋅ 𝐒(k))                       🝖[ _≡_ ]-[]
  ∑(𝟎 ‥₌ n) (k ↦ 2 + (2 ⋅ k))                    🝖[ _≡_ ]-[ ∑-add {r = 0 ‥₌ n}{f = const 2}{g = 2 ⋅_} ]-sym
  ∑(𝟎 ‥₌ n) (const(2)) + ∑(𝟎 ‥₌ n) (k ↦ (2 ⋅ k)) 🝖[ _≡_ ]-[ congruence₂(_+_) (∑-const {r = 0 ‥₌ n}{c = 2}) (∑-even-sum {n}) ]
  (2 ⋅ length(𝟎 ‥₌ n)) + (n ⋅ 𝐒(n))              🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(n ⋅ 𝐒(n)) (congruence₂ᵣ(_⋅_)(2) (Range-length-zero {𝐒(n)})) ]
  (2 ⋅ 𝐒(n)) + (n ⋅ 𝐒(n))                        🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) {x = 2}{y = n}{z = 𝐒(n)} ]-sym
  (2 + n) ⋅ 𝐒(n)                                 🝖[ _≡_ ]-[]
  𝐒(𝐒(n)) ⋅ 𝐒(n)                                 🝖[ _≡_ ]-[ commutativity(_⋅_) {x = 𝐒(𝐒(n))}{y = 𝐒(n)} ]
  𝐒(n) ⋅ 𝐒(𝐒(n))                                 🝖[ _≡_ ]-end

∑-odd-sum : (∑(𝟎 ‥ n) (k ↦ 𝐒(2 ⋅ k)) ≡ n ^ 2)
∑-odd-sum {𝟎}   = [≡]-intro
∑-odd-sum {𝐒 n} =
  ∑(𝟎 ‥ 𝐒(n)) (k ↦ 𝐒(2 ⋅ k))               🝖[ _≡_ ]-[]
  ∑(𝟎 ‥₌ n) (k ↦ 𝐒(2 ⋅ k))                 🝖[ _≡_ ]-[ ∑-of-succ {r = 𝟎 ‥ 𝐒(n)}{f = 2 ⋅_} ]
  ∑(𝟎 ‥₌ n) (k ↦ 2 ⋅ k) + length(𝟎 ‥ 𝐒(n)) 🝖[ _≡_ ]-[ congruence₂(_+_) (∑-even-sum {n}) (Range-length-zero {𝐒(n)}) ]
  (n ⋅ 𝐒(n)) + 𝐒(n)                        🝖[ _≡_ ]-[ [⋅]-with-[𝐒]ₗ {x = n}{y = 𝐒(n)} ]-sym
  𝐒(n) ⋅ 𝐒(n)                              🝖[ _≡_ ]-[]
  𝐒(n) ^ 2                                 🝖-end

open import Numeral.Natural.Combinatorics

module _ where
  open import Data.List.Relation.Membership using (_∈_ ; use ; skip)

  mapDep : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (l : List(A)) → ((elem : A) → ⦃ _ : (elem ∈ l) ⦄ → B) → List(B)
  mapDep ∅ _ = ∅
  mapDep (elem ⊰ l) f = (f elem ⦃ use ⦄) ⊰ (mapDep l (\x → f x ⦃ _∈_.skip ⦄))

  -- ∑dep : (r : List(ℕ)) → ((i : ℕ) → ⦃ _ : (i ∈ r) ⦄ → ℕ) → ℕ

  -- ∑dep-test : ∑dep ∅ id ≡ 0

-- Also called: The binomial theorem
{-
binomial-power : ∀{n}{a b} → ((a + b) ^ n ≡ ∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ^ (n −₀ i)) ⋅ (b ^ i)))
binomial-power {𝟎}   {a} {b} =
  (a + b) ^ 𝟎                                         🝖[ _≡_ ]-[]
  1                                                   🝖[ _≡_ ]-[]
  1 ⋅ 1 ⋅ 1                                           🝖[ _≡_ ]-[]
  𝑐𝐶(𝟎)(𝟎) ⋅ (a ^ 𝟎) ⋅ (b ^ 𝟎)                        🝖[ _≡_ ]-[]
  𝑐𝐶(𝟎)(𝟎) ⋅ (a ^ (𝟎 −₀ 𝟎)) ⋅ (b ^ 𝟎)                 🝖[ _≡_ ]-[]
  ∑(𝟎 ‥₌ 𝟎) (i ↦ 𝑐𝐶(𝟎)(i) ⋅ (a ^ (𝟎 −₀ i)) ⋅ (b ^ 𝟎)) 🝖-end
binomial-power {𝐒 n} {a} {b} = {!!}
{-  (a + b) ^ 𝐒(n)                                                                                                            🝖[ _≡_ ]-[]
  (a + b) ⋅ ((a + b) ^ n)                                                                                                   🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(a + b) (binomial-power{n}{a}{b}) ]
  (a + b) ⋅ (∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ^ i) ⋅ (b ^ (n −₀ i))))                                                           🝖[ _≡_ ]-[ {!!} ]
  (a ⋅ (∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ^ i) ⋅ (b ^ (n −₀ i))))) + (b ⋅ (∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ^ i) ⋅ (b ^ (n −₀ i))))) 🝖[ _≡_ ]-[ {!!} ]

  a ⋅ (b ^ 𝐒(n)) ⋅ ∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(𝐒(n))(𝐒(i)) ⋅ (a ^ i) ⋅ (b ^ (n −₀ i)))                                                🝖[ _≡_ ]-[ {!!} ]
  (b ^ 𝐒(n)) ⋅ ∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(𝐒(n))(𝐒(i)) ⋅ a ⋅ (a ^ i) ⋅ (b ^ (n −₀ i)))                                                🝖[ _≡_ ]-[ {!!} ]
  (b ^ 𝐒(n)) ⋅ ∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(𝐒(n))(𝐒(i)) ⋅ (a ^ 𝐒(i)) ⋅ (b ^ (n −₀ i)))                                                 🝖[ _≡_ ]-[]
  (b ^ 𝐒(n)) ⋅ ∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(𝐒(n))(𝐒(i)) ⋅ (a ^ 𝐒(i)) ⋅ (b ^ (𝐒(n) −₀ 𝐒(i))))                                            🝖[ _≡_ ]-[ {!!} ]
  (b ^ 𝐒(n)) ⋅ ∑(1 ‥₌ 𝐒(n)) (i ↦ 𝑐𝐶(𝐒(n))(i) ⋅ (a ^ i) ⋅ (b ^ (𝐒(n) −₀ i)))                                  🝖[ _≡_ ]-[]
  (1 ⋅ 1 ⋅ (b ^ 𝐒(n))) ⋅ ∑(1 ‥₌ 𝐒(n)) (i ↦ 𝑐𝐶(𝐒(n))(i) ⋅ (a ^ i) ⋅ (b ^ (𝐒(n) −₀ i)))                        🝖[ _≡_ ]-[]
  (𝑐𝐶(𝐒(n))(𝟎) ⋅ (a ^ 𝟎) ⋅ (b ^ (𝐒(n) −₀ 𝟎))) ⋅ ∑(1 ‥₌ 𝐒(n)) (i ↦ 𝑐𝐶(𝐒(n))(i) ⋅ (a ^ i) ⋅ (b ^ (𝐒(n) −₀ i))) 🝖[ _≡_ ]-[ {!!} ]
  ∑(𝟎 ‥₌ 𝐒(n)) (i ↦ 𝑐𝐶(𝐒(n))(i) ⋅ (a ^ i) ⋅ (b ^ (𝐒(n) −₀ i)))                                               🝖-end-}
  where
    left : _ ≡ _
    left =
      a ⋅ (∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ^ (n −₀ i)) ⋅ (b ^ i)))                                               🝖[ _≡_ ]-[ {!!} ]
      ∑(𝟎 ‥₌ n) (i ↦ a ⋅ 𝑐𝐶(n)(i) ⋅ (a ^ (n −₀ i)) ⋅ (b ^ i))                                                 🝖[ _≡_ ]-[ {!!} ]
      ∑(𝟎 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ⋅ (a ^ (n −₀ i))) ⋅ (b ^ i))                                               🝖[ _≡_ ]-[ {!!} ]
      (𝑐𝐶(n)(𝟎) ⋅ (a ⋅ (a ^ (n −₀ 𝟎))) ⋅ (b ^ 𝟎)) + ∑(1 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ⋅ (a ^ (n −₀ i))) ⋅ (b ^ i)) 🝖[ _≡_ ]-[ {!!} ]
      (1 ⋅ (a ^ 𝐒(n)) ⋅ 1) + ∑(1 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ⋅ (a ^ (n −₀ i))) ⋅ (b ^ i))                        🝖[ _≡_ ]-[ {!!} ]
      (1 ⋅ (a ^ 𝐒(n))) + ∑(1 ‥₌ n) (i ↦ 𝑐𝐶(n)(i) ⋅ (a ⋅ (a ^ (n −₀ i))) ⋅ (b ^ i))                            🝖-end
-- TODO: Maybe need another variant of ∑ where the index has a proof of it being in the range? And it is in this case used for a ⋅ (a ^ (n −₀ i)) ≡ a ^ (𝐒(n) −₀ i)
-}
