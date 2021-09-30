module Numeral.Natural.Relation.Divisibility.Proofs where

import Lvl
open import Data
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
open import Numeral.Natural.Oper.Proofs.Multiplication
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Order.Existence using ([≤]-equivalence)
open import Numeral.Natural.Relation.Order.Existence.Proofs using ()
open import Numeral.Natural.Relation.Divisibility
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type
open import Type.Properties.MereProposition

{-
div-elim-test : ∀{ℓ ℓ₁}{A : Type{ℓ₁}}{f : A → ℕ}{g : ℕ → ℕ}{P : ∀{y x} → (f(y) ∣ x) → Type{ℓ}} → (∀{y} → P(Div𝟎{f y})) → (∀{y x}{p : f y ∣ g x} → P(p) → P(Div𝐒 p)) → (∀{y x}{p : f(y) ∣ g x} → P(p))
div-elim-test {f = f}{g = g}              z s {y}{x}{p = p} with g(x)
... | 𝟎 = {!p!}
... | 𝐒 a = {!p!}
-- div-elim-test               z s {p = Div𝟎}   = z
-- div-elim-test{f = f}{P = P} z s {p = Div𝐒 p} = s(div-elim-test{f = f}{P = P} z s {p = p})
-}

{-
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
-}

{-

div-elim-test : ∀{f : ℕ → ℕ}{ℓ}{P : ∀{y x} → (f y ∣ x) → Type{ℓ}} → (∀{y} → P(Div𝟎{f y})) → (∀{y x}{p : f y ∣ x} → P(p) → P(Div𝐒 p)) → (∀{y x}{p : f y ∣ x} → P(p))
div-elim-test        z s {p = Div𝟎}   = z
div-elim-test{f = f}{P = P} z s {p = Div𝐒 p} = s(div-elim-test{f = f}{P = P} z s {p = p})

divides-mereProposition : ∀{d n} → MereProposition(𝐒(d) ∣ n)
divides-mereProposition = intro proof where
  proof : ∀{d n}{p q : (𝐒(d) ∣ n)} → (p ≡ q)
  proof {d} {.𝟎} {Div𝟎} {Div𝟎} = [≡]-intro
  proof {d} {.(𝐒 d + _)} {Div𝐒 p} {q} = {!div-elim-test{P = Div𝐒 p ≡_} ? ? {?}!}
  --proof{d}{n}{p}{q} = div-elim {P = \q → ∀{p} → (p ≡ q)} (\{y}{p} → {!div-elim {P = _≡ Div𝟎} ? ? {p = p}!}) {!!} {p = q}
  -- div-elim{P = {!!}} (div-elim {!!} {!!} {p = p}) (div-elim {!!} {!!} {p = p}) {p = q}

  {-
  test : ∀{y x} → (y ∣ x) → ∃{Obj = ℕ ⨯ ℕ}(Tuple.uncurry(_∣_))
  test {y}{.𝟎} Div𝟎     = [∃]-intro (y , 𝟎) ⦃ Div𝟎 ⦄
  test         (Div𝐒 p) = [∃]-intro _       ⦃ p ⦄
  -}
-}

DivN : ∀{y : ℕ} → (n : ℕ) → (y ∣ (y ⋅ n))
DivN {y}(𝟎)    = Div𝟎
DivN {y}(𝐒(n)) = Div𝐒(DivN{y}(n))

divides-quotient : ∀{x y} → (y ∣ x) → ℕ
divides-quotient = divides-elim 𝟎 𝐒

divides-quotient-correctness : ∀{x y}{yx : (y ∣ x)} → (y ⋅ (divides-quotient yx) ≡ x)
divides-quotient-correctness        {yx = Div𝟎}    = [≡]-intro
divides-quotient-correctness {_}{y} {yx = Div𝐒 yx} = congruence₂ᵣ(_+_)(y) (divides-quotient-correctness {yx = yx})

divides-[⋅]-existence : ∀{x y} → ∃(n ↦ y ⋅ n ≡ x) ↔ (y ∣ x)
divides-[⋅]-existence = [↔]-intro l r where
  l : ∀{x y} → (y ∣ x) → (∃(n ↦ y ⋅ n ≡ x))
  l yx = [∃]-intro (divides-quotient yx) ⦃ divides-quotient-correctness {yx = yx} ⦄

  r : ∀{x y} → (∃(n ↦ y ⋅ n ≡ x)) → (y ∣ x)
  r {x}{y} ([∃]-intro n ⦃ y⋅n≡x ⦄) = [≡]-substitutionᵣ y⋅n≡x {y ∣_} (DivN{y}(n))

divides-[⋅]-existence₊ : ∀{x y} → (y ∣ 𝐒(x)) → ∃(n ↦ y ⋅ 𝐒(n) ≡ 𝐒(x))
divides-[⋅]-existence₊ {x}{y} p with [↔]-to-[←] (divides-[⋅]-existence{𝐒(x)}{y}) p
... | [∃]-intro (𝐒(n)) = [∃]-intro n

instance
  divides-transitivity : Transitivity(_∣_)
  Transitivity.proof (divides-transitivity) {a}{b}{c} (a-div-b) (b-div-c) with ([↔]-to-[←] divides-[⋅]-existence a-div-b , [↔]-to-[←] divides-[⋅]-existence b-div-c)
  ... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ b⋅n₂≡c ⦄)) =
    ([↔]-to-[→] divides-[⋅]-existence
      ([∃]-intro
        (n₁ ⋅ n₂)
        ⦃
          (symmetry(_≡_) (associativity(_⋅_) {a}{n₁}{n₂}))
          🝖 ([≡]-with(expr ↦ expr ⋅ n₂) (a⋅n₁≡b))
          🝖 (b⋅n₂≡c)
        ⦄
      )
    )

divides-with-[+] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b + c))
divides-with-[+] {a}{b}{c} (a-div-b) (a-div-c) with ([↔]-to-[←] divides-[⋅]-existence a-div-b , [↔]-to-[←] divides-[⋅]-existence a-div-c)
... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
  ([↔]-to-[→] divides-[⋅]-existence
    ([∃]-intro
      (n₁ + n₂)
      ⦃
        (distributivityₗ(_⋅_)(_+_) {a}{n₁}{n₂})
        🝖 ([≡]-with-op(_+_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

divides-with-[−₀] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b −₀ c))
divides-with-[−₀] {a}{b}{c} (a-div-b) (a-div-c) with ([↔]-to-[←] divides-[⋅]-existence a-div-b , [↔]-to-[←] divides-[⋅]-existence a-div-c)
... | (([∃]-intro (n₁) ⦃ a⋅n₁≡b ⦄),([∃]-intro (n₂) ⦃ a⋅n₂≡c ⦄)) =
  ([↔]-to-[→] divides-[⋅]-existence
    ([∃]-intro
      (n₁ −₀ n₂)
      ⦃
        (distributivityₗ(_⋅_)(_−₀_) {a}{n₁}{n₂})
        🝖 ([≡]-with-op(_−₀_)
          (a⋅n₁≡b)
          (a⋅n₂≡c)
        )
      ⦄
    )
  )

divides-without-[+] : ∀{a b c} → (a ∣ (b + c)) → ((a ∣ b) ↔ (a ∣ c))
divides-without-[+] {a}{b}{c} abc = [↔]-intro (l abc) (r abc) where
  l : ∀{a b c} → (a ∣ (b + c)) → (a ∣ b) ← (a ∣ c)
  l{a}{b}{c} abc ac = [≡]-substitutionᵣ ([−₀]ₗ[+]ᵣ-nullify{b}{c}) {expr ↦ (a ∣ expr)} (divides-with-[−₀] {a}{b + c}{c} abc ac)

  r : ∀{a b c} → (a ∣ (b + c)) → (a ∣ b) → (a ∣ c)
  r{a}{b}{c} abc ab = l {a}{c}{b} ([≡]-substitutionᵣ (commutativity(_+_) {b}{c}) {expr ↦ a ∣ expr} abc) ab

divides-without-[−₀] : ∀{a b c} → (b ≥ c) → (a ∣ (b −₀ c)) → ((a ∣ b) ↔ (a ∣ c))
divides-without-[−₀] ord abc = [↔]-intro
  (\ac → substitute₂ᵣ(_∣_) ([↔]-to-[→] [−₀][+]-nullify2ᵣ ord) (divides-with-[+] abc ac))
  (\ab → substitute₂ᵣ(_∣_) ([↔]-to-[→] [−₀]-nested-sameₗ ord) (divides-with-[−₀] ab abc))

divides-with-[𝄩] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b 𝄩 c))
divides-with-[𝄩] {a} ab ac
 with [∃]-intro n₁ ⦃ p ⦄ ← [↔]-to-[←] divides-[⋅]-existence ab
 with [∃]-intro n₂ ⦃ q ⦄ ← [↔]-to-[←] divides-[⋅]-existence ac
 = [↔]-to-[→] divides-[⋅]-existence ([∃]-intro (n₁ 𝄩 n₂) ⦃ distributivityₗ(_⋅_)(_𝄩_) {a}{n₁}{n₂} 🝖 congruence₂(_𝄩_) p q ⦄)

-- instance
--   divides-with-fn : ∀{a b} → (a ∣ b) → ∀{f : ℕ → ℕ} → {_ : ∀{x y : ℕ} → ∃{ℕ → ℕ}(\g → f(x ⋅ y) ≡ f(x) ⋅ g(y))} → ((f(a)) ∣ (f(b)))
--   divides-with-fn {a}{b} (a-div-b) {f} ⦃ f-prop ⦄ 

instance
  [1]-divides : ∀{n} → (1 ∣ n)
  [1]-divides {𝟎}    = Div𝟎
  [1]-divides {𝐒(n)} =
    [≡]-substitutionₗ
      (commutativity(_+_) {n}{1})
      {expr ↦ (1 ∣ expr)}
      (Div𝐒([1]-divides{n}))

[∣][1]-minimal : Weak.Properties.LE.Minimum(_∣_)(𝟏)
[∣][1]-minimal = Weak.Properties.intro [1]-divides

instance
  divides-reflexivity : Reflexivity(_∣_)
  divides-reflexivity = intro(Div𝐒 Div𝟎)

instance
  [0]-divides-[0] : (0 ∣ 0)
  [0]-divides-[0] = Div𝟎

[0]-only-divides-[0] : ∀{n} → (0 ∣ n) → (n ≡ 0)
[0]-only-divides-[0] {𝟎} _ = [≡]-intro
[0]-only-divides-[0] {𝐒(n)} proof with () ← [∃]-proof([↔]-to-[←] divides-[⋅]-existence proof)

[0]-divides-not : ∀{n} → ¬(0 ∣ 𝐒(n))
[0]-divides-not (0divSn) = [𝐒]-not-0([0]-only-divides-[0] 0divSn)

divides-not-[1] : ∀{n} → ¬((n + 2) ∣ 1)
divides-not-[1] ()

[1]-only-divides-[1] : ∀{n} → (n ∣ 1) → (n ≡ 1)
[1]-only-divides-[1] {𝟎}       ndiv1 = [⊥]-elim ([0]-divides-not ndiv1)
[1]-only-divides-[1] {𝐒(𝟎)}    ndiv1 = [≡]-intro
[1]-only-divides-[1] {𝐒(𝐒(n))} ()

divides-with-[⋅] : ∀{a b c} → ((a ∣ b) ∨ (a ∣ c)) → (a ∣ (b ⋅ c))
divides-with-[⋅] {a}{b}{c} = [∨]-elim (l{a}{b}{c}) (r{a}{b}{c}) where
  l : ∀{a b c} → (a ∣ b) → (a ∣ (b ⋅ c))
  l Div𝟎 = Div𝟎
  l {a}{a}{c} (Div𝐒 Div𝟎) = DivN{a} c
  l {a} {.(a + x)} {c} (Div𝐒 {.a} {x} ab@(Div𝐒 _)) = [≡]-substitutionₗ (distributivityᵣ(_⋅_)(_+_) {a}{x}{c}) {a ∣_} (divides-with-[+] (l {a}{a}{c} (Div𝐒 Div𝟎)) (l {a}{x}{c} ab))

  r : ∀{a b c} → (a ∣ c) → (a ∣ (b ⋅ c))
  r {a}{b}{c} ac = [≡]-substitutionᵣ (commutativity(_⋅_) {c}{b}) {a ∣_} (l {a}{c}{b} ac)

divides-upper-limit : ∀{a b} ⦃ pos : Positive(b) ⦄ → (a ∣ b) → (a ≤ b)
divides-upper-limit {𝟎}   {𝐒 _}  proof = [⊥]-elim ([0]-divides-not proof)
divides-upper-limit {𝐒(a)}{𝐒(b)} proof = ([↔]-to-[→] [≤]-equivalence) (existence2) where
  existence1 : ∃(n ↦ 𝐒(a) + (𝐒(a) ⋅ n) ≡ 𝐒(b))
  existence1 = divides-[⋅]-existence₊(proof)

  existence2 : ∃(n ↦ 𝐒(a) + n ≡ 𝐒(b))
  existence2 = [∃]-intro(𝐒(a) ⋅ [∃]-witness(existence1)) ⦃ [∃]-proof(existence1) ⦄

divides-not-lower-limit : ∀{a b} → (a > 𝐒(b)) → (a ∤ 𝐒(b))
divides-not-lower-limit {a}{b} = (contrapositiveᵣ (divides-upper-limit {a}{𝐒 b})) ∘ [>]-to-[≰]

Div𝐏 : ∀{x y : ℕ} → (y ∣ (y + x)) → (y ∣ x)
Div𝐏 {x}{y} proof = [↔]-to-[→] (divides-without-[+] {y}{y}{x} proof) (reflexivity(_∣_))

Div𝐏-monus : ∀{x y : ℕ} → (y ∣ x) → (y ∣ (x −₀ y))
Div𝐏-monus Div𝟎 = Div𝟎
Div𝐏-monus {.(y + x)}{y} (Div𝐒 {_}{x} yx) = [≡]-substitutionₗ ([−₀]ₗ[+]ₗ-nullify {y}{x}) {y ∣_} yx

divides-with-[⋅]ₗ-both : ∀{x y z} → (x ∣ y) → (z ⋅ x ∣ z ⋅ y)
divides-with-[⋅]ₗ-both {x} {.0}       {z} Div𝟎 = Div𝟎
divides-with-[⋅]ₗ-both {x} {.(x + _)} {z} (Div𝐒 {_}{y} xy) rewrite distributivityₗ(_⋅_)(_+_) {z}{x}{y} = Div𝐒 (divides-with-[⋅]ₗ-both {x}{y}{z} xy)

divides-with-[⋅]ᵣ-both : ∀{x y z} → (x ∣ y) → (x ⋅ z ∣ y ⋅ z)
divides-with-[⋅]ᵣ-both {x} {.0}       {z} Div𝟎 = Div𝟎
divides-with-[⋅]ᵣ-both {x} {.(x + _)} {z} (Div𝐒 {_}{y} xy) rewrite distributivityᵣ(_⋅_)(_+_) {x}{y}{z} = Div𝐒 (divides-with-[⋅]ᵣ-both {x}{y}{z} xy)

divides-with-[⋅]-both : ∀{x₁ y₁ x₂ y₂} → (x₁ ∣ y₁) → (x₂ ∣ y₂) → (x₁ ⋅ x₂ ∣ y₁ ⋅ y₂)
divides-with-[⋅]-both {x₁}{y₁}{x₂}{y₂} xy1 xy2
  with [∃]-intro n₁ ⦃ [≡]-intro ⦄ ← [↔]-to-[←] divides-[⋅]-existence xy1
  with [∃]-intro n₂ ⦃ [≡]-intro ⦄ ← [↔]-to-[←] divides-[⋅]-existence xy2
  = [↔]-to-[→] divides-[⋅]-existence ([∃]-intro (n₁ ⋅ n₂) ⦃ One.associate-commute4 {_▫_ = _⋅_} {a = x₁}{x₂}{n₁}{n₂} (commutativity(_⋅_) {x₂}{n₁}) ⦄)

divides-with-[^] : ∀{a b n} → (a ∣ b) → ((a ^ n) ∣ (b ^ n))
divides-with-[^] {n = 𝟎}   _  = Div𝐒 Div𝟎
divides-with-[^] {n = 𝐒 n} ab = divides-with-[⋅]-both ab (divides-with-[^] {n = n} ab)

divides-withᵣ-[^] : ∀{a b n} → ⦃ pos : Positive(n) ⦄ → (a ∣ b) → (a ∣ (b ^ n))
divides-withᵣ-[^] {a}{b}{𝐒 n} ab = divides-with-[⋅] {a}{b}{b ^ n} ([∨]-introₗ ab)

divides-without-[⋅]ᵣ-both : ∀{x y z} → (x ⋅ 𝐒(z) ∣ y ⋅ 𝐒(z)) → (x ∣ y)
divides-without-[⋅]ᵣ-both {x}{y}{z} p
  with [∃]-intro n ⦃ peq ⦄ ← [↔]-to-[←] divides-[⋅]-existence p
  = [↔]-to-[→] divides-[⋅]-existence ([∃]-intro n ⦃ [⋅]-cancellationᵣ{𝐒(z)} (symmetry(_≡_) (One.commuteᵣ-assocₗ{_▫_ = _⋅_}{x}{𝐒(z)}{n}) 🝖 peq) ⦄)

divides-without-[⋅]ₗ-both : ∀{x y z} → (𝐒(z) ⋅ x ∣ 𝐒(z) ⋅ y) → (x ∣ y)
divides-without-[⋅]ₗ-both {x}{y}{z} p = divides-without-[⋅]ᵣ-both {x}{y}{z} (substitute₂(_∣_) (commutativity(_⋅_) {𝐒(z)}{x}) (commutativity(_⋅_) {𝐒(z)}{y}) p)

divides-without-[⋅]ᵣ-both' : ∀{x y z} ⦃ pos : Positive(z) ⦄ → (x ⋅ z ∣ y ⋅ z) → (x ∣ y)
divides-without-[⋅]ᵣ-both' {x}{y}{𝐒(z)} = divides-without-[⋅]ᵣ-both {x}{y}{z}

divides-without-[⋅]ₗ-both' : ∀{x y z} ⦃ pos : Positive(z) ⦄ → (z ⋅ x ∣ z ⋅ y) → (x ∣ y)
divides-without-[⋅]ₗ-both' {x}{y}{𝐒(z)} = divides-without-[⋅]ₗ-both {x}{y}{z}

divides-factorial : ∀{n x} → (𝐒(x) ≤ n) → (𝐒(x) ∣ (n !))
divides-factorial {.(𝐒 y)}{.x} (succ {x}{y} xy) with [≥]-or-[<] {x}{y}
... | [∨]-introₗ yx with [≡]-intro ← antisymmetry(_≤_)(_≡_) xy yx = divides-with-[⋅] {𝐒(x)}{𝐒(x)}{x !} ([∨]-introₗ(reflexivity(_∣_)))
... | [∨]-introᵣ sxy = divides-with-[⋅] {𝐒(x)}{𝐒(y)}{y !} ([∨]-introᵣ(divides-factorial{y}{x} sxy))

instance
  divides-antisymmetry : Antisymmetry(_∣_)(_≡_)
  Antisymmetry.proof divides-antisymmetry {𝟎} {𝟎}     ab ba = [≡]-intro
  Antisymmetry.proof divides-antisymmetry {𝟎} {𝐒 b}   ab ba with () ← [0]-divides-not ab
  Antisymmetry.proof divides-antisymmetry {𝐒 a} {𝟎}   ab ba with () ← [0]-divides-not ba
  Antisymmetry.proof divides-antisymmetry {𝐒 a} {𝐒 b} ab ba = antisymmetry(_≤_)(_≡_) (divides-upper-limit ab) (divides-upper-limit ba)

instance
  divides-weakPartialOrder : Weak.PartialOrder(_∣_)
  divides-weakPartialOrder = record{}

divides-quotient-positive : ∀{d n}{dn : (d ∣ 𝐒(n))} → (divides-quotient dn ≥ 1)
divides-quotient-positive {𝟎}   {n}        {dn = dn}      with () ← [0]-divides-not dn
divides-quotient-positive {𝐒 d} {.(d + _)} {dn = Div𝐒 dn} = succ _≤_.min

divides-quotient-composite : ∀{d n} → (d ≥ 2) → (d < n) → ∀{dn : (d ∣ n)} → (divides-quotient dn ≥ 2)
divides-quotient-composite l g {Div𝐒 {x = 𝟎}   dn} with () ← irreflexivity(_<_) g
divides-quotient-composite l g {Div𝐒 {x = 𝐒 x} dn} = succ (divides-quotient-positive {dn = dn})

divides-of-[⋅]ₗ : ∀{a b c} → (Positive(a) ↔ Positive(b)) → ((a ⋅ b) ∣ c) → ((a ∣ c) ∧ (b ∣ c))
divides-of-[⋅]ₗ {𝟎}   {𝟎}   {c} pos abc = [∧]-intro abc abc
divides-of-[⋅]ₗ {𝟎}   {𝐒 b} {c} pos abc with () ← [↔]-to-[←] pos <>
divides-of-[⋅]ₗ {𝐒 a} {𝟎}   {c} pos abc with () ← [↔]-to-[→] pos <>
divides-of-[⋅]ₗ {𝐒 a} {𝐒 b} {c} pos abc = [∧]-intro
  (divides-without-[⋅]ᵣ-both'{z = 𝐒 b} (divides-with-[⋅] {c = 𝐒(b)} ([∨]-introₗ abc)))
  (divides-without-[⋅]ₗ-both'{z = 𝐒 a} (divides-with-[⋅] {b = 𝐒(a)} ([∨]-introᵣ abc)))

divides-positive : ∀{a b} → (a ∣ b) → (Positive(a) ← Positive(b))
divides-positive {𝟎}   {𝐒 b} (Div𝐒 ab) <> with () ← [0]-divides-not ab
divides-positive {𝐒 a} {𝐒 b} ab        <> = <>
