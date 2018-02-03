module Numeral.Natural.Relation.Properties{ℓ} where

import Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Proof{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Theorems{ℓ}{Lvl.𝟎}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

instance
  [≤]-from-[≡] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
  [≤]-from-[≡] x≡y = [∃]-intro 0 ⦃ x≡y ⦄

instance
  [≤][0]-minimum : ∀{x : ℕ} → (0 ≤ x)
  [≤][0]-minimum {x} = [∃]-intro x ⦃ [+]-identityₗ ⦄
  -- [∃]-intro {ℕ} {\n → 0 + n ≡ x} (x) ⦃ [+]-identityₗ ⦄

instance
  [≤][0]ᵣ : ∀{x : ℕ} → (x ≤ 0) ↔ (x ≡ 0)
  [≤][0]ᵣ {𝟎} = [↔]-intro l r where
    l : (𝟎 ≤ 0) ← (𝟎 ≡ 0)
    l refl = [≤]-from-[≡] refl

    r : (𝟎 ≤ 0) → (𝟎 ≡ 0)
    r _ = [≡]-intro
  [≤][0]ᵣ {𝐒(n)} = [↔]-intro l r where
    l : (𝐒(n) ≤ 0) ← (𝐒(n) ≡ 0)
    l ()

    r : (𝐒(n) ≤ 0) → (𝐒(n) ≡ 0)
    r ([∃]-intro _ ⦃ ⦄ )

instance
  [≤][0]ᵣ-negation : ∀{x : ℕ} → ¬(𝐒(x) ≤ 0)
  [≤][0]ᵣ-negation {x} (Sx≤0) = [𝐒]-not-0([↔]-elimᵣ([≤][0]ᵣ {𝐒(x)}) (Sx≤0))

instance
  [≤]-successor : ∀{a b : ℕ} → (a ≤ b) → (a ≤ 𝐒(b))
  [≤]-successor ([∃]-intro(n) ⦃ proof ⦄) = [∃]-intro (𝐒(n)) ⦃ [≡]-with(𝐒) (proof) ⦄
  -- a + n ≡ b //f
  -- a + ? ≡ 𝐒(b) //What value works if f?
  -- a + 𝐒(n) ≡ 𝐒(b)
  -- 𝐒(a + n) ≡ 𝐒(b) //[≡]-with(𝐒) f

instance
  [≤]-predecessor : ∀{a b : ℕ} → (𝐒(a) ≤ b) → (a ≤ b)
  [≤]-predecessor ([∃]-intro(n) ⦃ proof ⦄) = [∃]-intro (𝐒(n)) ⦃ proof ⦄

[ℕ]-unnecessary-induction : ∀{b : ℕ}{φ : ℕ → Stmt} → (∀(i : ℕ) → (i ≤ b) → φ(i)) → (∀(i : ℕ) → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-unnecessary-induction {𝟎}   {φ} (base) (next) = [ℕ]-induction {φ} (base(𝟎) ([∃]-intro(𝟎) ⦃ [≡]-intro ⦄)) (next)
[ℕ]-unnecessary-induction {𝐒(b)}{φ} (base) (next) = [ℕ]-unnecessary-induction {b}{φ} (base-prev) (next) where
  base-prev : ∀(i : ℕ) → (i ≤ b) → φ(i)
  base-prev(𝟎)    (proof) = base(𝟎) ([≤][0]-minimum)
  base-prev(𝐒(i)) (proof) = next(i) (base-prev(i) ([≤]-predecessor {i}{b} proof))

instance
  [≤]-with-[𝐒] : ∀{a b : ℕ} → (a ≤ b) → (𝐒(a) ≤ 𝐒(b))
  [≤]-with-[𝐒] {a} {b} ([∃]-intro n ⦃ f ⦄) =
    [∃]-intro
      (n)
     ⦃
        ([+1]-commutativity {a} {n}) -- 𝐒(a)+n = a+𝐒(n)
        🝖 ([≡]-with(𝐒) f) -- 𝐒(a+n)=a+𝐒(n) = 𝐒(b)
      ⦄

instance
  [≤]-without-[𝐒] : ∀{a b : ℕ} → (a ≤ b) ← (𝐒(a) ≤ 𝐒(b))
  [≤]-without-[𝐒] {𝟎}   {b}    (_)                    = [≤][0]-minimum
  [≤]-without-[𝐒] {𝐒(a)}{𝟎}    ()
  [≤]-without-[𝐒] {𝐒(a)}{𝐒(b)} ([∃]-intro(n) ⦃ proof ⦄) = [≤]-with-[𝐒] {a}{b} ([≤]-without-[𝐒] {a}{b} ([∃]-intro(n) ⦃ [𝐒]-injectivity proof ⦄))

instance
  [≤][𝐒]ₗ : ∀{x : ℕ} → ¬(𝐒(x) ≤ x)
  [≤][𝐒]ₗ {𝟎}    (1≤0)    = [≤][0]ᵣ-negation{0}(1≤0)
  [≤][𝐒]ₗ {𝐒(n)} (SSn≤Sn) = [≤][𝐒]ₗ {n} ([≤]-without-[𝐒] {𝐒(n)}{n} (SSn≤Sn))

instance
  [≤]-transitivity : Transitivity (_≤_)
  transitivity ⦃ [≤]-transitivity ⦄ {a}{b}{c} ([∃]-intro n₁ ⦃ a+n₁≡b ⦄) ([∃]-intro n₂ ⦃ b+n₂≡c ⦄) =
    [∃]-intro
      (n₁ + n₂)
     ⦃
        (symmetry ([+]-associativity {a} {n₁} {n₂})) -- a+(n₁+n₂) = (a+n₁)+n₂
        🝖 ([≡]-with(expr ↦ expr + n₂) (a+n₁≡b)) -- (a+n₁)+n₂ = b+n₂
        🝖 (b+n₂≡c) -- b+n₂ = c
      ⦄ -- a+(n₁+n₂) = c

instance
  [≤]-reflexivity : Reflexivity (_≤_)
  reflexivity ⦃ [≤]-reflexivity ⦄ = [≤]-from-[≡] [≡]-intro

instance
  [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {a} {b} (([∃]-intro(n₁) ⦃ a+n₁≡b ⦄) , ([∃]-intro(n₂) ⦃ b+n₂≡a ⦄)) = [≡]-elimᵣ (n₁≡0) {n ↦ (a + n ≡ b)} (a+n₁≡b) where
    n₁+n₂≡0 : ((n₁ + n₂) ≡ 0)
    n₁+n₂≡0 =
      [+]-injectivityᵣ(
        (symmetry([+]-associativity {a} {n₁} {n₂}))
        🝖 ([≡]-with(expr ↦ expr + n₂) a+n₁≡b)
        🝖 b+n₂≡a
      )
    n₁≡0 : (n₁ ≡ 0)
    n₁≡0 = [+]-sum-is-0ₗ {n₁} {n₂} n₁+n₂≡0
  -- a+n₁ = b
  -- (a+n₁)+n₂ = b+n₂
  -- (a+n₁)+n₂ = a
  -- a+(n₁+n₂) = a
  -- a+(n₁+n₂) = a+0
  -- n₁+n₂ = 0
  -- a = b

instance
  [≤]-weakPartialOrder : Weak.PartialOrder (_≤_) (_≡_)
  [≤]-weakPartialOrder = record{
      antisymmetry = [≤]-antisymmetry;
      transitivity = [≤]-transitivity;
      reflexivity  = [≤]-reflexivity
    }

instance
  [<][0]-minimum : ∀{x : ℕ} → (0 < 𝐒(x))
  [<][0]-minimum {x} = [≤]-with-[𝐒] {0} ([≤][0]-minimum)

-- TODO
instance
  postulate [≮]-is-[≥] : ∀{a b : ℕ} → ¬(a < b) → (a ≥ b)
  -- [≮]-is-[≥] =
    -- ¬(a<b)
    -- (a<b) → ⊥
    -- (a<b) → ⊥

  [≥]-is-[≮] : ∀{a b : ℕ} → ¬(a < b) ← (a ≥ b)
  [≥]-is-[≮] {a}{b} (b≤a) (Sa≤b) = [≤][𝐒]ₗ (transitivity {_}{_}{𝐒(a)}{b}{a} (Sa≤b) (b≤a))

  -- a ≥ b
  -- b ≤ a

  -- a < b
  -- 𝐒(a) ≤ b

instance
  postulate [≯]-is-[≤] : ∀{a b : ℕ} → ¬(a > b) → (a ≤ b)

  [≤]-is-[≯] : ∀{a b : ℕ} → ¬(a > b) ← (a ≤ b)
  [≤]-is-[≯] {a}{b} = [≥]-is-[≮] {b}{a}

instance
  -- TODO: This would probably be easy if [≤][ℕ]-excluded-middle is valid
  postulate [≰]-is-[>] : ∀{a b : ℕ} → ¬(a ≤ b) → (a > b)

  [>]-is-[≰] : ∀{a b : ℕ} → ¬(a ≤ b) ← (a > b)
  [>]-is-[≰] {a}{b} (Sb≤a) (a≤b) = [≤]-is-[≯] {a}{b} (a≤b) (Sb≤a)

  -- a ≤ b

  -- a > b
  -- b < a
  -- 𝐒(b) ≤ a

instance
  postulate [≱]-is-[<] : ∀{a b : ℕ} → ¬(a ≥ b) → (a < b)

  [<]-is-[≱] : ∀{a b : ℕ} → ¬(a ≥ b) ← (a < b)
  [<]-is-[≱] {a}{b} = [>]-is-[≰] {b}{a}

instance
  [≤]-totality : Total(_≤_)
  total ⦃ [≤]-totality ⦄ {𝟎}   {𝟎}    = [∨]-introₗ ([≤]-from-[≡] [≡]-intro)
  total ⦃ [≤]-totality ⦄ {𝐒(a)}{𝟎}    = [∨]-introᵣ ([≤][0]-minimum)
  total ⦃ [≤]-totality ⦄ {𝟎}   {𝐒(b)} = [∨]-introₗ ([≤][0]-minimum)
  total ⦃ [≤]-totality ⦄ {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ ([≤]-with-[𝐒] {a}{b})) ([∨]-introᵣ ∘ ([≤]-with-[𝐒] {b}{a})) (total ⦃ [≤]-totality ⦄ {a}{b})

instance
  [ℕ]-zero-or-nonzero : ∀{n} → (n ≡ 𝟎)∨(n ≢ 𝟎)
  [ℕ]-zero-or-nonzero {𝟎}    = [∨]-introₗ [≡]-intro
  [ℕ]-zero-or-nonzero {𝐒(_)} = [∨]-introᵣ \()

instance
  [≡][ℕ]-excluded-middle : ∀{a b} → (a ≡ b)∨(a ≢ b)
  [≡][ℕ]-excluded-middle {𝟎}   {𝟎}    = [∨]-introₗ [≡]-intro
  [≡][ℕ]-excluded-middle {𝟎}   {𝐒(_)} = [∨]-introᵣ \()
  [≡][ℕ]-excluded-middle {𝐒(_)}{𝟎}    = [∨]-introᵣ \()
  [≡][ℕ]-excluded-middle {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ [≡]-with(𝐒)) ([∨]-introᵣ ∘ (contrapositiveᵣ [𝐒]-injectivity)) ([≡][ℕ]-excluded-middle {a}{b})

-- instance
--  [≤][ℕ]-excluded-middle : ∀{a b} → (a ≤ b)∨(a ≰ b)
--  [≤][ℕ]-excluded-middle = [∨]-elim ([∨]-introₗ ∘ ([∃]-intro(0))) ([∨]-introᵣ ∘ f) ([≡][ℕ]-excluded-middle) where
--    f : (a ≢ b) → (a ≰ b)
--    f = 
    -- (a≢b) → (a≰b)
    -- ((a≡b)→⊥) → ((a≤b)→⊥)
    -- ((a≡b)→⊥) → (a≤b) → ⊥

-- TODO: Can this proof be made more simple?
[ℕ]-strong-induction : ∀{φ : ℕ → Stmt} → φ(𝟎) → (∀{i : ℕ} → (∀{j : ℕ} → (j ≤ i) → φ(j)) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-strong-induction {φ} (base) (next) {n} = ([ℕ]-inductionᵢ {Q} (Q0) (QS) {n}) {n} (reflexivity) where
  Q : ℕ → Stmt
  Q(k) = (∀{n} → (n ≤ k) → φ(n))

  Q0 : Q(𝟎)
  Q0{𝟎}    (_) = base
  Q0{𝐒(j)} (proof) = [⊥]-elim([≤][0]ᵣ-negation {j} (proof))

  QS : ∀{k : ℕ} → Q(k) → Q(𝐒(k))
  QS{k} (qk) {𝟎}    (0≤Sk)  = base
  QS{k} (qk) {𝐒(n)} (Sn≤Sk) = (next{n} (qn)) :of: φ(𝐒(n)) where
    n≤k : n ≤ k
    n≤k = [≤]-without-[𝐒] {n}{k} (Sn≤Sk)

    qn : Q(n)
    qn{a} (a≤n) = qk{a} (transitivity{_}{_}{a} (a≤n) (n≤k))
