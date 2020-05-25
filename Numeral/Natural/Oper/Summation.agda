module Numeral.Natural.Oper.Summation where

import      Lvl
open import Data.List
open import Data.List.Functions
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Structure.Function
open import Structure.Operator
open import Type

_‥_ : ℕ → ℕ → List(ℕ)
_   ‥ 𝟎   = ∅
𝟎   ‥ 𝐒 b = 𝟎 ⊰ map 𝐒(𝟎 ‥ b)
𝐒 a ‥ 𝐒 b = map 𝐒(a ‥ b)

‥_ : ℕ → List(ℕ)
‥ b = 𝟎 ‥ b

_‥₌_ : ℕ → ℕ → List(ℕ)
a ‥₌ b = a ‥ 𝐒(b)

‥₌_ : ℕ → List(ℕ)
‥₌ b = 𝟎 ‥₌ b

-- TODO: Change to (∑ : List(ℕ) → (ℕ → A) → A) with (_▫_), Identity(_▫_)(id) or just a monoid, and use setoids
∑ : List(ℕ) → (ℕ → ℕ) → ℕ
∑(r) f = foldᵣ(_+_) 𝟎 (map f(r))

open        Data.List.Functions.LongOper
open import Data.List.Proofs
open import Functional
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Relator.Equals hiding (_≡_)
open import Relator.Equals.Proofs.Equiv
open import Structure.Setoid
open import Structure.Operator.Properties
open import Structure.Operator.Proofs.Util
open import Structure.Relator.Properties
open import Syntax.Transitivity

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



∑-empty : ∀{f} → (∑(∅) f ≡ 𝟎)
∑-empty = reflexivity(_≡_)

∑-prepend : ∀{f}{x}{r} → (∑(prepend x r) f ≡ f(x) + ∑(r) f)
∑-prepend = reflexivity(_≡_)

∑-postpend : ∀{f}{x}{r} → (∑(postpend x r) f ≡ ∑(r) f + f(x))
∑-postpend {f} {x} {∅} = reflexivity(_≡_)
∑-postpend {f} {x} {r₀ ⊰ r} =
  f(r₀) + ∑(postpend x r) f  🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(r₀)) (∑-postpend {f} {x} {r}) ]
  f(r₀) + (∑(r) f + f(x))    🝖[ _≡_ ]-[ associativity(_+_) {f(r₀)}{∑(r) f}{f(x)} ]-sym
  (f(r₀) + ∑(r) f) + f(x)    🝖-end

∑-compose : ∀{f}{g}{r} → ∑(r) (f ∘ g) ≡ ∑(map g r) f
∑-compose {f}{g}{r} = congruence₁(foldᵣ(_+_) 𝟎) (map-preserves-[∘] {f = f}{g = g}{x = r})

∑-add : ∀{r}{f g} → (∑(r) f + ∑(r) g ≡ ∑(r) (x ↦ f(x) + g(x)))
∑-add {∅}      {f} {g} = reflexivity(_≡_)
∑-add {r₀ ⊰ r} {f} {g} =
  ∑(prepend r₀ r) f + ∑(prepend r₀ r) g    🝖[ _≡_ ]-[]
  (f(r₀) + ∑(r) f) + (g(r₀) + ∑(r) g)      🝖[ _≡_ ]-[ One.associate-commute4 {a = f(r₀)}{b = ∑(r) f}{c = g(r₀)}{d = ∑(r) g} (commutativity(_+_){x = ∑(r) f}{y = g(r₀)}) ]
  (f(r₀) + g(r₀)) + (∑(r) f + ∑(r) g)      🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(r₀) + g(r₀)) (∑-add {r} {f} {g}) ]
  (f(r₀) + g(r₀)) + ∑(r) (x ↦ f(x) + g(x)) 🝖[ _≡_ ]-[]
  ∑(prepend r₀ r) (x ↦ f(x) + g(x))        🝖-end

-- ∑-mult : ∀{r₁ r₂}{f g} → (∑(r₁) f ⋅ ∑(r₂) g ≡ ∑(r₁) (x ↦ ∑(r₂) (y ↦ f(x) ⋅ g(y))))

∑-scalar-mult : ∀{r}{c}{f} → (∑(r) (x ↦ c ⋅ f(x)) ≡ c ⋅ (∑(r) f))
∑-scalar-mult {empty}        {c} {f} = [≡]-intro
∑-scalar-mult {prepend r₀ r} {c} {f} =
  (c ⋅ f(r₀)) + ∑(r) (x ↦ c ⋅ f(x)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(c ⋅ f(r₀)) (∑-scalar-mult {r}{c}{f}) ]
  (c ⋅ f(r₀)) + (c ⋅ (∑(r) f))      🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) {c}{f(r₀)}{∑(r) f} ]-sym
  c ⋅ (f(r₀) + (∑(r) f))            🝖-end

∑-const : ∀{r}{c} → (∑(r) (const c) ≡ c ⋅ length(r))
∑-const {empty}      {c} = reflexivity(_≡_)
∑-const {prepend x r}{c} = congruence₂ᵣ(_+_)(c) (∑-const {r}{c})

∑-zero : ∀{r} → (∑(r) (const 𝟎) ≡ 𝟎)
∑-zero {r} = ∑-const {r}{𝟎}

∑-singleton : ∀{a}{f} → (∑(singleton(a)) f ≡ f(a))
∑-singleton = reflexivity(_≡_)

∑-concat : ∀{f}{r₁ r₂} → (∑(r₁ ++ r₂) f ≡ ∑(r₁) f + ∑(r₂) f)
∑-concat {f} {empty}        {r₂} = [≡]-intro
∑-concat {f} {prepend x r₁} {r₂} =
  f(x) + ∑(r₁ ++ r₂) f      🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(f(x)) (∑-concat {f}{r₁}{r₂}) ]
  f(x) + (∑(r₁) f + ∑ r₂ f) 🝖[ _≡_ ]-[ associativity(_+_) {x = f(x)}{y = ∑(r₁) f}{z = ∑(r₂) f} ]-sym
  (f(x) + ∑(r₁) f) + ∑ r₂ f 🝖-end

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



∑-zero-range : ∀{a}{f} → (∑(a ‥ a) f ≡ 𝟎)
∑-zero-range {a}{f} = congruence₁ (r ↦ ∑(r) f) (Range-empty{a})

∑-single-range : ∀{a}{f} → (∑(a ‥ 𝐒(a)) f ≡ f(a))
∑-single-range {𝟎}  {f} = reflexivity(_≡_)
∑-single-range {𝐒 a}{f} =
  ∑ (map 𝐒 (a ‥ 𝐒 a)) f       🝖[ _≡_ ]-[ ∑-compose {f}{𝐒}{a ‥ 𝐒 a} ]-sym
  ∑ (a ‥ 𝐒 a) (λ x → f (𝐒 x)) 🝖[ _≡_ ]-[ ∑-single-range {a}{f ∘ 𝐒} ]
  f (𝐒 a)                     🝖-end

∑-step-range : ∀{a b}{f} → (∑(𝐒(a) ‥ 𝐒(b)) f ≡ ∑(a ‥ b) (f ∘ 𝐒))
∑-step-range {a}{b}{f} = symmetry(_≡_) (∑-compose {f = f}{g = 𝐒}{r = a ‥ b})

∑-stepₗ-range : ∀{a b}{f} → ⦃ _ : (a < b) ⦄ → (∑(a ‥ b) f ≡ f(a) + ∑(𝐒(a) ‥ b) f)
∑-stepₗ-range {𝟎}   {𝐒 b} {f} ⦃ [≤]-with-[𝐒] ⦃ ab ⦄ ⦄ = reflexivity(_≡_)
∑-stepₗ-range {𝐒 a} {𝐒 b} {f} ⦃ [≤]-with-[𝐒] ⦃ ab ⦄ ⦄ =
  ∑(𝐒(a) ‥ 𝐒(b)) f                                🝖[ _≡_ ]-[ ∑-step-range {a}{b}{f} ]
  ∑(a ‥ b) (f ∘ 𝐒)                                🝖[ _≡_ ]-[ ∑-stepₗ-range {a}{b}{f ∘ 𝐒} ]
  (f ∘ 𝐒)(a) + ∑(𝐒(a) ‥ b) (f ∘ 𝐒)                🝖[ _≡_ ]-[ congruence₂(_+_) (reflexivity(_≡_) {x = f(𝐒(a))}) (symmetry(_≡_) (∑-step-range {𝐒 a}{b}{f})) ]
  f(𝐒(a)) + ∑(𝐒(𝐒(a)) ‥ 𝐒(b)) f                   🝖-end

-- ∑-stepᵣ-range : ∀{a b}{f} → ⦃ _ : (a < 𝐒(b)) ⦄ → (∑(a ‥ 𝐒(b)) f ≡ ∑(a ‥ b) f + f(b))
-- ∑-stepᵣ-range = ?

-- ∑-add-range : ∀{a b}{f} → (∑(a ‥ a + b) f ≡ ∑(𝟎 ‥ b) (f ∘ (_+ a)))

∑-trans-range : ∀{a b c} → ⦃ ab : (a ≤ b) ⦄ ⦃ bc : (b < c) ⦄ → ∀{f} → (∑(a ‥ b) f + ∑(b ‥ c) f ≡ ∑(a ‥ c) f)
∑-trans-range {a}{b}{c} {f} =
  ∑(a ‥ b) f + ∑(b ‥ c) f 🝖[ _≡_ ]-[ ∑-concat{f = f}{r₁ = a ‥ b}{r₂ = b ‥ c} ]-sym
  ∑((a ‥ b) ++ (b ‥ c)) f 🝖[ _≡_ ]-[ congruence₁(r ↦ ∑(r) f) (Range-concat{a}{b}{c}) ]
  ∑(a ‥ c) f              🝖-end

-- TODO: Formulate ∑({(x,y). a ≤ x ≤ y ≤ b}) f ≡ ∑(a ‥ b) (x ↦ ∑(a ‥ x) (y ↦ f(x)(y))) ≡ ∑(a ‥ b) (x ↦ ∑(x ‥ b) (y ↦ f(x)(y))) ≡ ... and first prove a theorem stating that the order of a list does not matter
-- ∑-nested-dependent-range : ∀{f : ℕ → ℕ → _}{a b} → ?



∑-of-succ : ∀{r}{f} → (∑(r) (𝐒 ∘ f) ≡ (∑(r) f) + length(r))
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

∑-even-sum : ∀{n} → (∑(𝟎 ‥₌ n) (k ↦ 2 ⋅ k) ≡ n ⋅ 𝐒(n))
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

∑-odd-sum : ∀{n} → (∑(𝟎 ‥ n) (k ↦ 𝐒(2 ⋅ k)) ≡ n ^ 2)
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
