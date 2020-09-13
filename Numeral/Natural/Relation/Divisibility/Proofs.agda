module Numeral.Natural.Relation.Divisibility.Proofs where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Order.Existence using ([≤]-equivalence)
open import Numeral.Natural.Relation.Order.Existence.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type
open import Type.Properties.MereProposition

Even-mereProposition : ∀{n} → MereProposition(Even(n))
Even-mereProposition = intro proof where
  proof : ∀{n}{p q : Even n} → (p ≡ q)
  proof {𝟎}       {Even0}   {Even0}   = [≡]-intro
  proof {𝐒(𝐒(n))} {Even𝐒 p} {Even𝐒 q} = [≡]-with(Even𝐒) (proof {n} {p} {q})

Odd-mereProposition : ∀{n} → MereProposition(Odd(n))
Odd-mereProposition = intro proof where
  proof : ∀{n}{p q : Odd n} → (p ≡ q)
  proof {𝐒(𝟎)}    {Odd0}   {Odd0}   = [≡]-intro
  proof {𝐒(𝐒(n))} {Odd𝐒 p} {Odd𝐒 q} = [≡]-with(Odd𝐒) (proof {n} {p} {q})

DivN : ∀{y : ℕ} → (n : ℕ) → y ∣ (y ⋅ n)
DivN {y}(𝟎)    = Div𝟎
DivN {y}(𝐒(n)) = Div𝐒(DivN{y}(n))

divides-intro : ∀{x y} → (∃(n ↦ y ⋅ n ≡ x)) → (y ∣ x)
divides-intro {x}{y} ([∃]-intro (n) ⦃ y⋅n≡x ⦄) = [≡]-substitutionᵣ (y⋅n≡x) {expr ↦ (y ∣ expr)} (DivN{y}(n))

divides-elim : ∀{x y} → (y ∣ x) → (∃(n ↦ y ⋅ n ≡ x))
divides-elim {_}{_} (Div𝟎) = [∃]-intro (0) ⦃ [≡]-intro ⦄
divides-elim {_}{y} (Div𝐒{x} (y-div-x)) with divides-elim(y-div-x)
... | ([∃]-intro (n) ⦃ y⋅n≡x ⦄) = [∃]-intro (𝐒(n)) ⦃ [≡]-with(y +_) (y⋅n≡x) ⦄

divides-intro-alt : ∀{n x y} → ⦃ _ : y ⋅ n ≡ x ⦄ → (y ∣ x)
divides-intro-alt {n}{x}{y} ⦃ proof ⦄ = ([↔]-to-[←] ([∀]-unrelatedₗ-[→] {X = ℕ} {n ↦ y ⋅ n ≡ x} {y ∣ x})) divides-intro {n} (proof)

instance
  divides-transitivity : Transitivity (_∣_)
  Transitivity.proof (divides-transitivity) {a}{b}{c} (a-div-b) (b-div-c) with (divides-elim (a-div-b) , divides-elim (b-div-c))
  ... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ b⋅n₂≡c ⦄)) =
    (divides-intro
      ([∃]-intro
        (n₁ ⋅ n₂)
        ⦃
          (symmetry(_≡_) ([⋅]-associativity-raw {a}{n₁}{n₂}))
          🝖 ([≡]-with(expr ↦ expr ⋅ n₂) (a⋅n₁≡b))
          🝖 (b⋅n₂≡c)
        ⦄
      )
    )

divides-with-[+] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b + c))
divides-with-[+] {a}{b}{c} (a-div-b) (a-div-c) with (divides-elim (a-div-b) , divides-elim (a-div-c))
... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
  (divides-intro
    ([∃]-intro
      (n₁ + n₂)
      ⦃
        ([⋅][+]-distributivityₗ-raw {a}{n₁}{n₂})
        🝖 ([≡]-with-op(_+_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

divides-with-[−₀] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b −₀ c))
divides-with-[−₀] {a}{b}{c} (a-div-b) (a-div-c) with (divides-elim (a-div-b) , divides-elim (a-div-c))
... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
  (divides-intro
    ([∃]-intro
      (n₁ −₀ n₂)
      ⦃
        ([⋅][−₀]-distributivityₗ-raw {a}{n₁}{n₂})
        🝖 ([≡]-with-op(_−₀_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

divides-without-[+]ₗ : ∀{a b c} → (a ∣ (b + c)) → (a ∣ c) → (a ∣ b)
divides-without-[+]ₗ {a}{b}{c} abc ac = [≡]-substitutionᵣ ([−₀]ₗ[+]ᵣ-nullify{b}{c}) {expr ↦ (a ∣ expr)} (divides-with-[−₀] {a}{b + c}{c} abc ac)

divides-without-[+]ᵣ : ∀{a b c} → (a ∣ (b + c)) → (a ∣ b) → (a ∣ c)
divides-without-[+]ᵣ {a}{b}{c} abc ab = divides-without-[+]ₗ {a}{c}{b} ([≡]-substitutionᵣ ([+]-commutativity-raw{b}{c}) {expr ↦ a ∣ expr} abc) ab

-- instance
--   divides-with-fn : ∀{a b} → (a ∣ b) → ∀{f : ℕ → ℕ} → {_ : ∀{x y : ℕ} → ∃{ℕ → ℕ}(\g → f(x ⋅ y) ≡ f(x) ⋅ g(y))} → ((f(a)) ∣ (f(b)))
--   divides-with-fn {a}{b} (a-div-b) {f} ⦃ f-prop ⦄ 

instance
  [1]-divides : ∀{n} → (1 ∣ n)
  [1]-divides {𝟎}    = Div𝟎
  [1]-divides {𝐒(n)} =
    [≡]-substitutionₗ
      ([+]-commutativity-raw {n}{1})
      {expr ↦ (1 ∣ expr)}
      (Div𝐒([1]-divides{n}))

-- TODO: Rename these reflexivity proofs
instance
  divides-reflexivity : ∀{n} → (n ∣ n)
  divides-reflexivity = Div𝐒(Div𝟎)

instance
  divides-reflexivity-instance : Reflexivity(_∣_)
  divides-reflexivity-instance = intro divides-reflexivity

instance
  [0]-divides-[0] : (0 ∣ 0)
  [0]-divides-[0] = Div𝟎

[0]-only-divides-[0] : ∀{n} → (0 ∣ n) → (n ≡ 0)
[0]-only-divides-[0] {𝟎} _ = [≡]-intro
[0]-only-divides-[0] {𝐒(n)} (proof) = [⊥]-elim(([𝐒]-not-0 ∘ symmetry(_≡_)) ([∃]-proof(divides-elim(proof)))) -- ∃(i ↦ 0 ⋅ i ≡ 𝐒(n))

[0]-divides-not : ∀{n} → ¬(0 ∣ 𝐒(n))
[0]-divides-not (0divSn) = [𝐒]-not-0([0]-only-divides-[0] (0divSn))

divides-not-[1] : ∀{n} → ¬((n + 2) ∣ 1)
divides-not-[1] ()

[1]-only-divides-[1] : ∀{n} → (n ∣ 1) → (n ≡ 1)
[1]-only-divides-[1] {𝟎}       (ndiv1) = [⊥]-elim ([0]-divides-not (ndiv1))
[1]-only-divides-[1] {𝐒(𝟎)}    (ndiv1) = [≡]-intro
[1]-only-divides-[1] {𝐒(𝐒(n))} ()

divides-with-[⋅]ₗ : ∀{a b c} → (a ∣ b) → (a ∣ (b ⋅ c))
divides-with-[⋅]ₗ Div𝟎 = Div𝟎
divides-with-[⋅]ₗ {a}{a}{c} (Div𝐒 Div𝟎) = p{a}{c} where
  p : ∀{a c} → (a ∣ (a ⋅ c))
  p{a}{𝟎} = Div𝟎
  p{a}{𝐒 c} = divides-with-[+] (Div𝐒 Div𝟎) (p{a}{c})
divides-with-[⋅]ₗ {a} {.(a + x)} {c} (Div𝐒 {.a} {x} ab@(Div𝐒 _)) = [≡]-substitutionₗ (distributivityᵣ(_⋅_)(_+_) {a}{x}{c}) {a ∣_} (divides-with-[+] (divides-with-[⋅]ₗ {a}{a}{c} (Div𝐒 Div𝟎)) (divides-with-[⋅]ₗ {a}{x}{c} ab))

divides-with-[⋅]ᵣ : ∀{a b c} → (a ∣ c) → (a ∣ (b ⋅ c))
divides-with-[⋅]ᵣ {a}{b}{c} ac = [≡]-substitutionᵣ (commutativity(_⋅_) {c}{b}) {a ∣_} (divides-with-[⋅]ₗ {a}{c}{b} ac)

divides-with-[⋅] : ∀{a b c} → (a ∣ b) ∨ (a ∣ c) → (a ∣ (b ⋅ c))
divides-with-[⋅] {a}{b}{c} ([∨]-introₗ ab) = divides-with-[⋅]ₗ {a}{b}{c} ab
divides-with-[⋅] {a}{b}{c} ([∨]-introᵣ ac) = divides-with-[⋅]ᵣ {a}{b}{c} ac

divides-elim₊ : ∀{x y} → (y ∣ 𝐒(x)) → ∃(n ↦ y ⋅ 𝐒(n) ≡ 𝐒(x))
divides-elim₊ {x}{y} (proof) with divides-elim{𝐒(x)}{y} (proof)
...                             | [∃]-intro (𝟎)    ⦃ y𝟎≡𝐒x ⦄  = [⊥]-elim (([𝐒]-not-0 ∘ symmetry(_≡_)) (symmetry(_≡_) ([⋅]-absorberᵣ-raw {y}) 🝖 y𝟎≡𝐒x))
...                             | [∃]-intro (𝐒(n)) ⦃ y𝐒n≡𝐒x ⦄ = [∃]-intro (n) ⦃ y𝐒n≡𝐒x ⦄

divides-upper-limit : ∀{a b} → (a ∣ 𝐒(b)) → (a ≤ 𝐒(b))
divides-upper-limit {𝟎}   {_} (proof) = [⊥]-elim ([0]-divides-not (proof))
divides-upper-limit {𝐒(a)}{b} (proof) = ([↔]-to-[→] [≤]-equivalence) (existence2) where
  existence1 : ∃(n ↦ 𝐒(a) + (𝐒(a) ⋅ n) ≡ 𝐒(b))
  existence1 = divides-elim₊(proof)

  existence2 : ∃(n ↦ 𝐒(a) + n ≡ 𝐒(b))
  existence2 = [∃]-intro(𝐒(a) ⋅ [∃]-witness(existence1)) ⦃ [∃]-proof(existence1) ⦄

divides-not-lower-limit : ∀{a b} → (a > 𝐒(b)) → (a ∤ 𝐒(b))
divides-not-lower-limit {a}{b} = (contrapositiveᵣ (divides-upper-limit {a}{b})) ∘ [>]-to-[≰]

Div𝐏 : ∀{x y : ℕ} → (y ∣ (y + x)) → (y ∣ x)
Div𝐏 {x}{y} proof = divides-without-[+]ᵣ {y}{y}{x} (proof) (divides-reflexivity)

Div𝐏-monus : ∀{x y : ℕ} → (y ∣ x) → (y ∣ (x −₀ y))
Div𝐏-monus Div𝟎 = Div𝟎
Div𝐏-monus {.(y + x)}{y} (Div𝐒 {_}{x} yx) = [≡]-substitutionₗ ([−₀]ₗ[+]ₗ-nullify {y}{x}) {y ∣_} yx

divides-with-[⋅]ₗ-both : ∀{x y z} → (x ∣ y) → (z ⋅ x ∣ z ⋅ y)
divides-with-[⋅]ₗ-both {x} {.0}       {z} Div𝟎 = Div𝟎
divides-with-[⋅]ₗ-both {x} {.(x + _)} {z} (Div𝐒 {_}{y} xy) rewrite [⋅][+]-distributivityₗ-raw {z}{x}{y} = Div𝐒 (divides-with-[⋅]ₗ-both {x}{y}{z} xy)

divides-with-[⋅]ᵣ-both : ∀{x y z} → (x ∣ y) → (x ⋅ z ∣ y ⋅ z)
divides-with-[⋅]ᵣ-both {x} {.0}       {z} Div𝟎 = Div𝟎
divides-with-[⋅]ᵣ-both {x} {.(x + _)} {z} (Div𝐒 {_}{y} xy) rewrite [⋅][+]-distributivityᵣ-raw {x}{y}{z} = Div𝐒 (divides-with-[⋅]ᵣ-both {x}{y}{z} xy)

-- divides-without-[⋅]ₗ-both : ∀{x y z} → (z ⋅ x ∣ z ⋅ y) → (x ∣ y)

divides-factorial : ∀{n x} → (𝐒(x) ≤ n) → (𝐒(x) ∣ (n !))
divides-factorial {.(𝐒 y)}{.x} ([≤]-with-[𝐒] {x}{y} ⦃ xy ⦄) with [≥]-or-[<] {x}{y}
... | [∨]-introₗ yx with [≡]-intro ← antisymmetry(_≤_)(_≡_) xy yx = divides-with-[⋅]ₗ {𝐒(x)}{𝐒(x)}{x !} (reflexivity(_∣_))
... | [∨]-introᵣ sxy = divides-with-[⋅]ᵣ {𝐒(x)}{𝐒(y)}{y !} (divides-factorial{y}{x} sxy)

instance
  divides-antisymmetry : Antisymmetry(_∣_)(_≡_)
  Antisymmetry.proof divides-antisymmetry {𝟎} {𝟎}     ab ba = [≡]-intro
  Antisymmetry.proof divides-antisymmetry {𝟎} {𝐒 b}   ab ba with () ← [0]-divides-not ab
  Antisymmetry.proof divides-antisymmetry {𝐒 a} {𝟎}   ab ba with () ← [0]-divides-not ba
  Antisymmetry.proof divides-antisymmetry {𝐒 a} {𝐒 b} ab ba = antisymmetry(_≤_)(_≡_) (divides-upper-limit ab) (divides-upper-limit ba)
