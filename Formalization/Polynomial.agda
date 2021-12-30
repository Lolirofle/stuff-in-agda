module Formalization.Polynomial where

import      Lvl
open import Data.ListSized
open import Numeral.Natural as ℕ using (ℕ)
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable n n₁ n₂ : ℕ

-- TODO: Some of the operations should work with arbitrary Rg structures, not just ℕ, and some other stuff should work with more assumptions. Currently, one of the function that needs to be modified is 𝐷 and normalize for this to work because their implementations depend on ℕ.
-- TODO: Composition of polynomials, power operation

module _ where
  -- A polynomial of a finite degree represented as a list of its coefficients.
  -- Examples:
  --   (a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x² + a₃⋅x³ + a₄⋅x⁴) of degree 4 is [a₀,a₁,a₂,a₃,a₄]
  --   (5 + 7⋅x + x³) of maximal degree 3 is [5,7,0,1]
  Polynomial : ℕ → Type
  Polynomial(n) = List(ℕ)(ℕ.𝐒(n))

  open import Data.ListSized.Functions
  import      Functional as Fn
  open import Logic.Propositional
  open import Logic.Propositional.Equiv
  open import Logic.Predicate
  import      Numeral.Natural.Function as ℕ
  open import Numeral.Natural.Function.Proofs
  import      Numeral.Natural.Oper as ℕ
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv{T = ℕ}
  open import Structure.Relator

  -- Constant polynomial.
  -- Semantically, this corresponds to a constant.
  const : ℕ → Polynomial(n)
  const {n} a = a ⊰ repeat ℕ.𝟎 n

  -- Zero polynomial.
  -- Semantically, this corresponds to zero.
  𝟎 : Polynomial(n)
  𝟎 {n} = const{n} ℕ.𝟎

  -- Unit polynomial.
  -- Semantically, this corresponds to one.
  𝟏 : Polynomial(n)
  𝟏 {n} = const{n}(ℕ.𝐒(ℕ.𝟎))

  -- Increases the degree of the polynomial by adding a zero term at the beginning.
  -- Semantically, this corresponds to multiplying the whole polynomial by the variable.
  -- Example: (var⋅ [a₀,a₁,a₂] = [0,a₀,a₁,a₂])
  --   x ⋅ (a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x²)
  --   = a₀⋅x¹ + a₁⋅x² + a₂⋅x³
  var⋅_ : Polynomial(n) → Polynomial(ℕ.𝐒(n))
  var⋅_ = ℕ.𝟎 ⊰_

  -- Single variable polynomial.
  var : Polynomial(ℕ.𝐒(n))
  var = var⋅ 𝟏

  -- Polynomial addition.
  -- Adds the powers component-wise.
  -- Examples: ([a₀,a₁,a₂] + [b₀,b₁,b₂] = [a₀b₀ , a₁+b₁ , a₂+b₂])
  --   (a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x²) + (b₀⋅x⁰ + b₁⋅x¹ + b₂⋅x²)
  --   = (a₀+b₀)⋅x⁰ + (a₁+b₁)⋅x¹ + (a₂+b₂)⋅x²
  --   of maximal degree 2 is [a₀+b₀ , a₁+b₁ , a₂+b₂]
  _+_ : Polynomial(n₁) → Polynomial(n₂) → Polynomial(ℕ.max n₁ n₂)
  _+_ = map₂(ℕ._+_) Fn.id Fn.id

  -- Polymonial scalar multiplication.
  -- Multiplies every component by a factor.
  -- Example: (n ⋅ [a₀,a₁,a₂] = [n⋅a₀ , n⋅a₁ , n⋅a₂])
  --   n ⋅ (a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x²)
  --   = (n⋅a₀)⋅x⁰ + (n⋅a₁)⋅x¹ + (n⋅a₂)⋅x²
  _⋅_ : ℕ → Polynomial(n) → Polynomial(n)
  n ⋅ as = map (n ℕ.⋅_) as

  -- Increases the degree of the polynomial by adding zero terms at the end.
  -- Semantically, this corresponds to adding terms multiplied by zero.
  -- Example: (pad [a₀,a₁,a₂] = [a₀,a₁,a₂,0,0])
  --   a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x²
  --   = a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x² + 0⋅x³ + 0⋅x⁴
  pad : ⦃ _ : (n₁ ≤ n₂)⦄ → Polynomial(n₁) → Polynomial(n₂)
  pad {n₁ = ℕ.𝟎}     {n₂ = ℕ.𝟎}     ⦃ min ⦄  (a ⊰ ∅)  = singleton a
  pad {n₁ = ℕ.𝟎}     {n₂ = ℕ.𝐒(n₂)} ⦃ min ⦄  (a ⊰ ∅)  = a ⊰ 𝟎
  pad {n₁ = ℕ.𝐒(n₁)} {n₂ = ℕ.𝐒(n₂)} ⦃ succ p ⦄ (a ⊰ as) = a ⊰ pad ⦃ p ⦄ as

  -- Polynomial multiplication.
  -- Proof of step:
  --   ∑(0‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ ∑(0‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ)
  --   = (a + ∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ)) ⋅ (b + ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ))
  --   = (a ⋅ b) + (a ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ)) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ b) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ))
  --   = (a⋅b) + (a ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ)) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ b⋅x) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ))
  --   = (a⋅b) + (a ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ)⋅x) + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ)⋅x ⋅ b) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ))
  --   = (a⋅b) + (a ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ))⋅x + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ) ⋅ b)⋅x + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ) ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ))⋅x²
  --   = (a⋅b) + ((a ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ)) + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ) ⋅ b) + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ) ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ))⋅x)⋅x
  --   Also see `eval-preserves-multiplication`.
  _⨯_ : Polynomial(n₁) → Polynomial(n₂) → Polynomial(n₁ ℕ.+ n₂)
  _⨯_                  as@(_ ⊰ _)       (b ⊰ ∅)          = b ⋅ as
  _⨯_                  (a ⊰ ∅)          bs@(_ ⊰ _ ⊰ _)   = a ⋅ bs
  _⨯_ {ℕ.𝐒 n₁}{ℕ.𝐒 n₂} (a ⊰ as@(_ ⊰ _)) (b ⊰ bs@(_ ⊰ _)) = (a ℕ.⋅ b) ⊰ lr where
    l : Polynomial(n₁ ℕ.+ n₂)
    l = pad ⦃ max-order-[+] ⦄ ((b ⋅ as) + (a ⋅ bs))

    r : Polynomial(ℕ.𝐒(n₁ ℕ.+ n₂))
    r = var⋅ (as ⨯ bs)

    lr : Polynomial(ℕ.𝐒(n₁ ℕ.+ n₂))
    lr = substitute₁ᵣ(Polynomial) ([↔]-to-[→] max-defᵣ [≤]-of-[𝐒]) (l + r)

  normalize : Polynomial(n) → ∃(Polynomial)
  normalize {ℕ.𝟎}   (x ⊰ ∅)      = [∃]-intro ℕ.𝟎 ⦃ x ⊰ ∅ ⦄
  normalize {ℕ.𝐒 n} (ℕ.𝟎 ⊰ p) with normalize{n} p
  ... | [∃]-intro ℕ.𝟎 ⦃ singleton ℕ.𝟎 ⦄ = [∃]-intro ℕ.𝟎      ⦃ singleton ℕ.𝟎 ⦄
  {-# CATCHALL #-}
  ... | [∃]-intro m   ⦃ a ⦄             = [∃]-intro (ℕ.𝐒(m)) ⦃ ℕ.𝟎 ⊰ a ⦄
  normalize {ℕ.𝐒 n} (ℕ.𝐒(x) ⊰ p) = [∃]-map ℕ.𝐒 (ℕ.𝐒(x) ⊰_) (normalize{n} p)

  degree : Polynomial(n) → ℕ
  degree = [∃]-witness Fn.∘ normalize

  𝐷 : Polynomial(n) → Polynomial(ℕ.𝐏(n))
  𝐷 {ℕ.𝟎}   = Fn.id
  𝐷 {ℕ.𝐒 n} = map₂₌(ℕ._⋅_) (accumulateIterate n ℕ.𝐒(ℕ.𝐒(ℕ.𝟎))) Fn.∘ tail

  import Numeral.Natural.Oper.FlooredDivision as ℕ
  ∫ : Polynomial(n) → Polynomial(ℕ.𝐒(n))
  ∫ {n} p = var⋅(map₂₌(ℕ._⌊/⌋₀_) p (accumulateIterate n ℕ.𝐒(ℕ.𝐒(ℕ.𝟎))))

module Semantics where
  open import Data.ListSized.Functions
  open import Logic.Propositional
  open import Logic.Propositional.Equiv
  open import Numeral.Finite as 𝕟 using (𝕟)
  import      Numeral.Natural.Oper as ℕ
  open import Numeral.Natural.Oper.Proofs
  open import Numeral.Natural.Relation.Order
  open import Relator.Equals.Proofs.Equiv{T = ℕ}
  open import Structure.Function.Multi
  open import Structure.Operator
  open import Structure.Operator.Proofs.Util
  open import Structure.Operator.Properties
  open import Structure.Relator.Properties
  open import Structure.Relator
  open import Structure.Setoid
  open import Syntax.Function
  open import Syntax.Transitivity

  eval : Polynomial(n) → (ℕ → ℕ)
  eval (singleton a)    _ = a
  eval (a ⊰ al@(_ ⊰ _)) x = a ℕ.+ (x ℕ.⋅ (eval al x))

  module Proofs where
    eval-of-[⊰] : ∀{x}{a}{al : Polynomial(n)} → (eval (a ⊰ al) x ≡ a ℕ.+ (x ℕ.⋅ (eval al x)))
    eval-of-[⊰] {ℕ.𝟎}   {x} {a} {b ⊰ ∅}      = reflexivity(_≡_)
    eval-of-[⊰] {ℕ.𝐒 n} {x} {a} {b ⊰ c ⊰ al} = reflexivity(_≡_)

    eval-preserves-var⋅ : ∀{x}{a : Polynomial(n)} → (eval (var⋅ a) x ≡ x ℕ.⋅ (eval a x))
    eval-preserves-var⋅ {n}{x}{a} = eval-of-[⊰] {n}{x}{ℕ.𝟎}{a}

    eval-preserves-zero : ∀{x} → (eval{n} 𝟎 x ≡ ℕ.𝟎)
    eval-preserves-zero {ℕ.𝟎}   {x} = reflexivity(_≡_)
    eval-preserves-zero {ℕ.𝐒 n} {x} =
      eval(𝟎 {ℕ.𝐒 n}) x              🝖[ _≡_ ]-[]
      eval(ℕ.𝟎 ⊰ 𝟎 {n}) x            🝖[ _≡_ ]-[]
      ℕ.𝟎 ℕ.+ (x ℕ.⋅ eval (𝟎 {n}) x) 🝖[ _≡_ ]-[]
      x ℕ.⋅ eval (𝟎 {n}) x           🝖[ _≡_ ]-[ congruence₂-₂(ℕ._⋅_)(x) (eval-preserves-zero{n}{x}) ]
      x ℕ.⋅ ℕ.𝟎                      🝖[ _≡_ ]-[ absorberᵣ(ℕ._⋅_)(ℕ.𝟎) {x} ]
      ℕ.𝟎                            🝖-end

    eval-preserves-const : ∀{x}{a} → (eval{n} (const a) x ≡ a)
    eval-preserves-const {ℕ.𝟎}   {x}{a} = reflexivity(_≡_)
    eval-preserves-const {ℕ.𝐒 n} {x}{a} =
      eval{ℕ.𝐒 n} (const a) x                  🝖[ _≡_ ]-[]
      eval(a ⊰ repeat ℕ.𝟎 (ℕ.𝐒 n)) x           🝖[ _≡_ ]-[ eval-of-[⊰] {x = x}{a}{repeat ℕ.𝟎 (ℕ.𝐒 n)} ]
      a ℕ.+ (x ℕ.⋅ eval(repeat ℕ.𝟎 (ℕ.𝐒 n)) x) 🝖[ _≡_ ]-[]
      a ℕ.+ (x ℕ.⋅ eval{n} 𝟎 x)                🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a) (eval-preserves-zero{ℕ.𝐒 n}{x = x}) ]
      a ℕ.+ (x ℕ.⋅ ℕ.𝟎)                        🝖[ _≡_ ]-[]
      a ℕ.+ ℕ.𝟎                                🝖[ _≡_ ]-[ identityᵣ(ℕ._+_)(ℕ.𝟎) ]
      a                                        🝖-end

    eval-preserves-one : ∀{x} → (eval{n} 𝟏 x ≡ ℕ.𝐒(ℕ.𝟎))
    eval-preserves-one {n}{x} = eval-preserves-const {n}{x}{ℕ.𝐒(ℕ.𝟎)}

    eval-preserves-var : ∀{x}{a : Polynomial(n)} → (eval (var{n}) x ≡ x)
    eval-preserves-var {n}{x}{a} =
      eval (var{n}) x      🝖[ _≡_ ]-[ eval-preserves-var⋅{n}{x}{𝟏} ]
      x ℕ.⋅ eval (𝟏 {n}) x 🝖[ _≡_ ]-[ congruence₂-₂(ℕ._⋅_)(x) (eval-preserves-one {n}{x}) ]
      x ℕ.⋅ ℕ.𝐒(ℕ.𝟎)       🝖[ _≡_ ]-[ identityᵣ(ℕ._⋅_)(ℕ.𝐒(ℕ.𝟎)) {x} ]
      x                    🝖-end

    eval-preserves-addition : ∀{x}{a : Polynomial(n₁)}{b : Polynomial(n₂)} → (eval (a + b) x ≡ (eval a x) ℕ.+ (eval b x))
    eval-preserves-addition {x = x} {singleton a}    {singleton b}    = reflexivity(_≡_)
    eval-preserves-addition {x = x} {singleton a}    {b ⊰ bs@(_ ⊰ _)} = associativity(ℕ._+_) {a}{b}
    eval-preserves-addition {x = x} {a ⊰ as@(_ ⊰ _)} {singleton b}    =
      eval ((a ⊰ as) + (singleton b)) x            🝖[ _≡_ ]-[]
      (a ℕ.+ b) ℕ.+ (x ℕ.⋅ (eval as x))            🝖[ _≡_ ]-[ associativity(ℕ._+_) {a}{b} ]
      a ℕ.+ (b ℕ.+ (x ℕ.⋅ (eval as x)))            🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a) (commutativity(ℕ._+_) {x = b}) ]
      a ℕ.+ ((x ℕ.⋅ (eval as x)) ℕ.+ b)            🝖[ _≡_ ]-[ associativity(ℕ._+_) {a}{x ℕ.⋅ eval as x} ]-sym
      (a ℕ.+ (x ℕ.⋅ (eval as x))) ℕ.+ b            🝖[ _≡_ ]-[]
      (eval (a ⊰ as) x) ℕ.+ (eval (singleton b) x) 🝖-end
    eval-preserves-addition {x = x} {a ⊰ as@(_ ⊰ _)} {b ⊰ bs@(_ ⊰ _)} =
      eval ((a ⊰ as) + (b ⊰ bs)) x                                  🝖[ _≡_ ]-[]
      eval ((a ℕ.+ b) ⊰ (as + bs)) x                                🝖[ _≡_ ]-[]
      (a ℕ.+ b) ℕ.+ (x ℕ.⋅ (eval (as + bs) x))                      🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a ℕ.+ b) (congruence₂-₂(ℕ._⋅_)(x) (eval-preserves-addition {x = x}{as}{bs})) ]
      (a ℕ.+ b) ℕ.+ (x ℕ.⋅ ((eval as x) ℕ.+ (eval bs x)))           🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a ℕ.+ b) (distributivityₗ(ℕ._⋅_)(ℕ._+_) {x}{eval as x}{eval bs x}) ]
      (a ℕ.+ b) ℕ.+ ((x ℕ.⋅ (eval as x)) ℕ.+ (x ℕ.⋅ (eval bs x)))   🝖[ _≡_ ]-[ One.associate-commute4 {a = a}{b = b}{c = x ℕ.⋅ (eval as x)}{d = x ℕ.⋅ (eval bs x)} (commutativity(ℕ._+_) {b}) ]
      (a ℕ.+ (x ℕ.⋅ (eval as x))) ℕ.+ (b ℕ.+ (x ℕ.⋅ (eval bs x)))   🝖[ _≡_ ]-[]
      (eval (a ⊰ as) x) ℕ.+ (eval (b ⊰ bs) x)                       🝖-end

    eval-preserves-scalar-multiplication : ∀{x}{a}{b : Polynomial(n)} → (eval (a ⋅ b) x ≡ a ℕ.⋅ (eval b x))
    eval-preserves-scalar-multiplication {ℕ.𝟎}   {x} {a} {b ⊰ ∅} = reflexivity(_≡_)
    eval-preserves-scalar-multiplication {ℕ.𝐒 n} {x} {a} {b ⊰ bs@(_ ⊰ _)} =
      eval (a ⋅ (b ⊰ bs)) x                     🝖[ _≡_ ]-[]
      eval ((a ℕ.⋅ b) ⊰ (a ⋅ bs)) x             🝖[ _≡_ ]-[]
      (a ℕ.⋅ b) ℕ.+ (x ℕ.⋅ (eval (a ⋅ bs) x))   🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a ℕ.⋅ b) (congruence₂-₂(ℕ._⋅_)(x) (eval-preserves-scalar-multiplication {n} {x}{a}{bs})) ]
      (a ℕ.⋅ b) ℕ.+ (x ℕ.⋅ (a ℕ.⋅ (eval bs x))) 🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a ℕ.⋅ b) (One.commuteₗ-assocᵣ {a = x}{b = a}{c = eval bs x}) ]
      (a ℕ.⋅ b) ℕ.+ (a ℕ.⋅ (x ℕ.⋅ (eval bs x))) 🝖[ _≡_ ]-[ distributivityₗ(ℕ._⋅_)(ℕ._+_) {x = a}{y = b}{z = x ℕ.⋅ (eval bs x)} ]-sym
      a ℕ.⋅ (b ℕ.+ (x ℕ.⋅ (eval bs x)))         🝖[ _≡_ ]-[]
      a ℕ.⋅ eval (b ⊰ bs) x                     🝖-end

    eval-preserves-pad : ∀{x}{a : Polynomial(n₁)} ⦃ ord : (n₁ ≤ n₂) ⦄ → (eval (pad ⦃ ord ⦄ a) x ≡ eval a x)
    eval-preserves-pad {ℕ.𝟎}    {ℕ.𝟎}    {x} {a ⊰ ∅}          ⦃ ord@min ⦄  = reflexivity(_≡_)
    eval-preserves-pad {ℕ.𝟎}    {ℕ.𝐒 n₂} {x} {a ⊰ ∅}          ⦃ ord@min ⦄  =
      eval (pad ⦃ ord ⦄ (a ⊰ ∅)) x  🝖[ _≡_ ]-[]
      a ℕ.+ (x ℕ.⋅ eval (𝟎 {n₂}) x) 🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a) (congruence₂-₂(ℕ._⋅_)(x) (eval-preserves-zero{n₂}{x})) ]
      a ℕ.+ (x ℕ.⋅ ℕ.𝟎)             🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a) (absorberᵣ(ℕ._⋅_)(ℕ.𝟎) {x}) ]
      a ℕ.+ ℕ.𝟎                     🝖[ _≡_ ]-[ identityᵣ(ℕ._+_)(ℕ.𝟎) ]
      a                             🝖[ _≡_ ]-[]
      eval (a ⊰ ∅) x                🝖-end
    eval-preserves-pad {ℕ.𝐒 n₁} {ℕ.𝐒 n₂} {x} {a ⊰ as@(_ ⊰ _)} ⦃ ord@(succ p) ⦄ =
      eval (pad ⦃ ord ⦄ (a ⊰ as)) x       🝖[ _≡_ ]-[]
      eval (a ⊰ pad ⦃ _ ⦄ as) x           🝖[ _≡_ ]-[ eval-of-[⊰] {n₂}{x}{a}{pad ⦃ p ⦄ as} ]
      a ℕ.+ (x ℕ.⋅ eval (pad ⦃ _ ⦄ as) x) 🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a) (congruence₂-₂(ℕ._⋅_)(x) (eval-preserves-pad {n₁}{n₂}{x}{as} ⦃ p ⦄)) ]
      a ℕ.+ (x ℕ.⋅ eval as x)       🝖[ _≡_ ]-[ eval-of-[⊰] {n₁}{x}{a}{as} ]-sym
      eval (a ⊰ as) x               🝖-end

    eval-preserves-multiplication : ∀{x}{a : Polynomial(n₁)}{b : Polynomial(n₂)} → (eval (a ⨯ b) x ≡ (eval a x) ℕ.⋅ (eval b x))
    eval-preserves-multiplication {n₁}    {ℕ.𝟎}   {x} {a ⊰ as}         {b ⊰ ∅}          =
      eval ((a ⊰ as) ⨯ (b ⊰ ∅)) x          🝖[ _≡_ ]-[]
      eval (b ⋅ (a ⊰ as)) x                🝖[ _≡_ ]-[ eval-preserves-scalar-multiplication {x = x}{b}{a ⊰ as} ]
      b ℕ.⋅ eval (a ⊰ as) x                🝖[ _≡_ ]-[ commutativity(ℕ._⋅_) {b}{eval(a ⊰ as) x} ]
      eval (a ⊰ as) x ℕ.⋅ b                🝖[ _≡_ ]-[]
      (eval (a ⊰ as) x ℕ.⋅ eval (b ⊰ ∅) x) 🝖-end
    eval-preserves-multiplication {ℕ.𝟎}   {ℕ.𝐒 n₂}{x} {a ⊰ ∅}          {b ⊰ bs@(_ ⊰ _)} =
      eval ((a ⊰ ∅) ⨯ (b ⊰ bs)) x        🝖[ _≡_ ]-[]
      eval (a ⋅ (b ⊰ bs)) x              🝖[ _≡_ ]-[ eval-preserves-scalar-multiplication {x = x}{a}{b ⊰ bs} ]
      a ℕ.⋅ (b ℕ.+ (x ℕ.⋅ eval bs x))    🝖[ _≡_ ]-[]
      eval (a ⊰ ∅) x ℕ.⋅ eval (b ⊰ bs) x 🝖-end
    eval-preserves-multiplication {ℕ.𝐒 n₁}{ℕ.𝐒 n₂}{x} {a ⊰ as@(_ ⊰ _)} {b ⊰ bs@(_ ⊰ _)} =
      eval((a ℕ.⋅ b) ⊰ lr) x                                                                                                    🝖[ _≡_ ]-[ eval-of-[⊰] {x = x}{a = a ℕ.⋅ b}{al = lr} ]
      (a ℕ.⋅ b) ℕ.+ (x ℕ.⋅ eval lr x)                                                                                           🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a ℕ.⋅ b) (congruence₂-₂(ℕ._⋅_)(x) eval-lr) ]
      (a ℕ.⋅ b) ℕ.+ (x ℕ.⋅ (((b ℕ.⋅ eval as x) ℕ.+ (a ℕ.⋅ eval bs x)) ℕ.+ (x ℕ.⋅ (eval as x ℕ.⋅ eval bs x))))                   🝖[ _≡_ ]-[ alg{a}{b}{x}{eval as x}{eval bs x} ]
      (a ℕ.+ (x ℕ.⋅ eval as x)) ℕ.⋅ (b ℕ.+ (x ℕ.⋅ eval bs x))                                                                   🝖[ _≡_ ]-[ congruence₂(ℕ._⋅_) (eval-of-[⊰] {x = x}{a = a}{al = as}) (eval-of-[⊰] {x = x}{a = b}{al = bs}) ]
      (eval(a ⊰ as) x ℕ.⋅ eval(b ⊰ bs) x)                                                                                       🝖-end
      where
        open import Numeral.Natural.Function
        open import Numeral.Natural.Function.Proofs
        open import Numeral.Natural.Relation.Order.Proofs
        open import Relator.Equals using ([≡]-intro)

        l : Polynomial(n₁ ℕ.+ n₂)
        l = pad ⦃ max-order-[+] ⦄ ((b ⋅ as) + (a ⋅ bs))

        r : Polynomial(ℕ.𝐒(n₁ ℕ.+ n₂))
        r = var⋅ (as ⨯ bs)

        lr : Polynomial(ℕ.𝐒(n₁ ℕ.+ n₂))
        lr = substitute₁ᵣ(Polynomial) ([↔]-to-[→] max-defᵣ [≤]-of-[𝐒]) (l + r)

        eval-l : (eval l x ≡ (b ℕ.⋅ eval as x) ℕ.+ (a ℕ.⋅ eval bs x))
        eval-l =
          eval l x                                             🝖[ _≡_ ]-[]
          eval (pad ⦃ max-order-[+] ⦄ ((b ⋅ as) + (a ⋅ bs))) x 🝖[ _≡_ ]-[ eval-preserves-pad {x = x}{(b ⋅ as) + (a ⋅ bs)} ⦃ max-order-[+] ⦄ ]
          eval ((b ⋅ as) + (a ⋅ bs)) x                         🝖[ _≡_ ]-[ eval-preserves-addition {x = x}{b ⋅ as}{a ⋅ bs} ]
          eval (b ⋅ as) x ℕ.+ eval (a ⋅ bs) x                  🝖[ _≡_ ]-[ congruence₂(ℕ._+_) (eval-preserves-scalar-multiplication {x = x}{b}{as}) (eval-preserves-scalar-multiplication {x = x}{a}{bs}) ]
          (b ℕ.⋅ eval as x) ℕ.+ (a ℕ.⋅ eval bs x)              🝖-end

        eval-r : (eval r x ≡ x ℕ.⋅ (eval as x ℕ.⋅ eval bs x))
        eval-r =
          eval r x                        🝖[ _≡_ ]-[]
          eval (var⋅ (as ⨯ bs)) x         🝖[ _≡_ ]-[ eval-preserves-var⋅ {x = x}{as ⨯ bs} ]
          x ℕ.⋅ eval (as ⨯ bs) x          🝖[ _≡_ ]-[ congruence₂-₂(ℕ._⋅_)(x) (eval-preserves-multiplication {x = x}{as}{bs}) ]
          x ℕ.⋅ (eval as x ℕ.⋅ eval bs x) 🝖-end

        eval-substitution : ∀{m n}{a : Polynomial(m)}{eq : (m ≡ n)}{x} → (eval(substitute₁ᵣ(Polynomial) eq a) x ≡ eval a x)
        eval-substitution {eq = [≡]-intro} = [≡]-intro

        eval-lr : (eval lr x ≡ ((b ℕ.⋅ eval as x) ℕ.+ (a ℕ.⋅ eval bs x)) ℕ.+ (x ℕ.⋅ (eval as x ℕ.⋅ eval bs x)))
        eval-lr =
          eval lr x                                                                       🝖[ _≡_ ]-[ eval-substitution{a = l + r}{[↔]-to-[→] max-defᵣ [≤]-of-[𝐒]}{x = x} ]
          eval (l + r) x                                                                  🝖[ _≡_ ]-[ eval-preserves-addition{x = x}{l}{r} ]
          eval l x ℕ.+ eval r x                                                           🝖[ _≡_ ]-[ congruence₂(ℕ._+_) eval-l eval-r ]
          ((b ℕ.⋅ eval as x) ℕ.+ (a ℕ.⋅ eval bs x)) ℕ.+ (x ℕ.⋅ (eval as x ℕ.⋅ eval bs x)) 🝖-end

        alg : ∀{a b x q r} → ((a ℕ.⋅ b) ℕ.+ (x ℕ.⋅ (((b ℕ.⋅ q) ℕ.+ (a ℕ.⋅ r)) ℕ.+ (x ℕ.⋅ (q ℕ.⋅ r)))) ≡ (a ℕ.+ (x ℕ.⋅ q)) ℕ.⋅ (b ℕ.+ (x ℕ.⋅ r)))
        alg {a}{b}{x}{q}{r} =
          (a ℕ.⋅ b) ℕ.+ (x ℕ.⋅ (((b ℕ.⋅ q) ℕ.+ (a ℕ.⋅ r)) ℕ.+ (x ℕ.⋅ (q ℕ.⋅ r))))                   🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a ℕ.⋅ b) (distributivityₗ(ℕ._⋅_)(ℕ._+_) {x}{(b ℕ.⋅ q) ℕ.+ (a ℕ.⋅ r)}{x ℕ.⋅ (q ℕ.⋅ r)}) ]
          (a ℕ.⋅ b) ℕ.+ ((x ℕ.⋅ ((b ℕ.⋅ q) ℕ.+ (a ℕ.⋅ r))) ℕ.+ (x ℕ.⋅ (x ℕ.⋅ (q ℕ.⋅ r))))           🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a ℕ.⋅ b) (congruence₂(ℕ._+_) (distributivityₗ(ℕ._⋅_)(ℕ._+_) {x}{b ℕ.⋅ q}{a ℕ.⋅ r}) (symmetry(_≡_) (associativity(ℕ._⋅_) {x}{x}{q ℕ.⋅ r}))) ]
          (a ℕ.⋅ b) ℕ.+ (((x ℕ.⋅ (b ℕ.⋅ q)) ℕ.+ (x ℕ.⋅ (a ℕ.⋅ r))) ℕ.+ ((x ℕ.⋅ x) ℕ.⋅ (q ℕ.⋅ r)))   🝖[ _≡_ ]-[ congruence₂-₂(ℕ._+_)(a ℕ.⋅ b) (congruence₂(ℕ._+_) (congruence₂(ℕ._+_) (One.commuteᵣ-assocᵣ {_▫_ = ℕ._⋅_}{a = x}{b}{q}) (One.commuteₗ-assocᵣ {_▫_ = ℕ._⋅_}{a = x}{a}{r})) (One.associate-commute4-c {_▫_ = ℕ._⋅_}{a = x}{x}{q}{r})) ]
          (a ℕ.⋅ b) ℕ.+ ((((x ℕ.⋅ q) ℕ.⋅ b) ℕ.+ (a ℕ.⋅ (x ℕ.⋅ r))) ℕ.+ ((x ℕ.⋅ q) ℕ.⋅ (x ℕ.⋅ r)))   🝖[ _≡_ ]-[ One.associate4-231-222 {_▫_ = ℕ._+_} {a = a ℕ.⋅ b}{(x ℕ.⋅ q) ℕ.⋅ b}{a ℕ.⋅ (x ℕ.⋅ r)}{(x ℕ.⋅ q) ℕ.⋅ (x ℕ.⋅ r)} ]
          ((a ℕ.⋅ b) ℕ.+ ((x ℕ.⋅ q) ℕ.⋅ b)) ℕ.+ ((a ℕ.⋅ (x ℕ.⋅ r)) ℕ.+ ((x ℕ.⋅ q) ℕ.⋅ (x ℕ.⋅ r)))   🝖[ _≡_ ]-[ OneTypeTwoOp.cross-distribute{a = a}{x ℕ.⋅ q}{b}{x ℕ.⋅ r} ]-sym
          (a ℕ.+ (x ℕ.⋅ q)) ℕ.⋅ (b ℕ.+ (x ℕ.⋅ r))                                                   🝖-end
