module Formalization.Polynomial where

import      Lvl
open import Data.ListSized
open import Numeral.Natural as ℕ using (ℕ)
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable n n₁ n₂ : ℕ

module _ where
  -- A polynomial of a finite degree represented as a list of its
  -- Examples:
  --   (a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x² + a₃⋅x³ + a₄⋅x⁴) of degree 4 is [a₀,a₁,a₂,a₃,a₄]
  --   (5 + 7⋅x + x³) of maximal degree 3 is [5,7,0,1]
  Polynomial : ℕ → Type
  Polynomial(n) = List(ℕ)(ℕ.𝐒(n))

  import      Functional as Fn
  open import Logic.Propositional
  import      Numeral.Natural.Function as ℕ
  open import Numeral.Natural.Function.Proofs
  import      Numeral.Natural.Oper as ℕ
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv(ℕ)

  -- Zero polynomial.
  -- Semantically, this corresponds to zero.
  𝟎 : Polynomial(n)
  𝟎 {n} = repeat ℕ.𝟎 (ℕ.𝐒(n))

  -- Polynomial addition.
  -- Adds the powers component-wise.
  -- Examples: ([a₀,a₁,a₂] + [b₀,b₁,b₂] = [a₀b₀ , a₁+b₁ , a₂+b₂])
  --   (a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x²) + (b₀⋅x⁰ + b₁⋅x¹ + b₂⋅x²)
  --   = (a₀+b₀)⋅x⁰ + (a₁+b₁)⋅x¹ + (a₂+b₂)⋅x²
  --   of maximal degree 2 is [a₀+b₀ , a₁+b₁ , a₂+b₂]
  _+_ : Polynomial(n₁) → Polynomial(n₂) → Polynomial(ℕ.max n₁ n₂)
  _+_ = map₂(ℕ._+_) Fn.id Fn.id
  {-(a ⊰ ∅)          + (b ⊰ ∅)          = (a ℕ.+ b) ⊰ ∅
  (a ⊰ ∅)          + (b ⊰ bs@(_ ⊰ _)) = (a ℕ.+ b) ⊰ bs
  (a ⊰ as@(_ ⊰ _)) + (b ⊰ ∅)          = (a ℕ.+ b) ⊰ as
  (a ⊰ as@(_ ⊰ _)) + (b ⊰ bs@(_ ⊰ _)) = (a ℕ.+ b) ⊰ (as + bs)-}

  -- Polymonial scalar multiplication.
  -- Multiplies every component by a factor.
  -- Example: (n ⋅ [a₀,a₁,a₂] = [n⋅a₀ , n⋅a₁ , n⋅a₂])
  --   n ⋅ (a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x²)
  --   = (n⋅a₀)⋅x⁰ + (n⋅a₁)⋅x¹ + (n⋅a₂)⋅x²
  _⋅_ : ℕ → Polynomial(n) → Polynomial(n)
  n ⋅ as = map (n ℕ.⋅_) as

  -- Increases the degree of the polynomial by adding a zero term at the beginning.
  -- Semantically, this corresponds to multiplying the whole polynomial by the variable.
  -- Example: (var⋅ [a₀,a₁,a₂] = [0,a₀,a₁,a₂])
  --   x ⋅ (a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x²)
  --   = a₀⋅x¹ + a₁⋅x² + a₂⋅x³
  var⋅_ : Polynomial(n) → Polynomial(ℕ.𝐒(n))
  var⋅_ = ℕ.𝟎 ⊰_

  -- Increases the degree of the polynomial by adding zero terms at the end.
  -- Semantically, this corresponds to adding terms multiplied by zero.
  -- Example: (pad [a₀,a₁,a₂] = [a₀,a₁,a₂,0,0])
  --   a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x²
  --   = a₀⋅x⁰ + a₁⋅x¹ + a₂⋅x² + 0⋅x³ + 0⋅x⁴
  pad : ⦃ _ : (n₁ ≤ n₂)⦄ → Polynomial(n₁) → Polynomial(n₂)
  pad {n₁ = ℕ.𝟎}     {n₂ = ℕ.𝟎}     ⦃ [≤]-minimum ⦄  (a ⊰ ∅)  = singleton a
  pad {n₁ = ℕ.𝟎}     {n₂ = ℕ.𝐒(n₂)} ⦃ [≤]-minimum ⦄  (a ⊰ ∅)  = a ⊰ 𝟎
  pad {n₁ = ℕ.𝐒(n₁)} {n₂ = ℕ.𝐒(n₂)} ⦃ [≤]-with-[𝐒] ⦄ (a ⊰ as) = a ⊰ pad as

  -- Polynomial multiplication.
  -- Proof of step:
  --   ∑(0‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ ∑(0‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ)
  --   = (a + ∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ)) ⋅ (b + ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ))
  --   = (a ⋅ b) + (a ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ)) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ b) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ))
  --   = (a⋅b) + (a ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ)) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ b⋅x) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ))
  --   = (a⋅b) + (a ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ)⋅x) + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ)⋅x ⋅ b) + (∑(1‥𝐒(n₁))(i ↦ aᵢ⋅xⁱ) ⋅ ∑(1‥𝐒(n₂))(i ↦ bᵢ⋅xⁱ))
  --   = (a⋅b) + (a ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ))⋅x + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ) ⋅ b)⋅x + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ) ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ))⋅x²
  --   = (a⋅b) + ((a ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ)) + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ) ⋅ b) + (∑(0‥n₁)(i ↦ aᵢ⋅xⁱ) ⋅ ∑(0‥n₂)(i ↦ bᵢ⋅xⁱ))⋅x)⋅x
  _⨯_ : Polynomial(n₁) → Polynomial(n₂) → Polynomial(n₁ ℕ.+ n₂)
  _⨯_                  as@(_ ⊰ _)       (b ⊰ ∅)          = b ⋅ as
  _⨯_                  (a ⊰ ∅)          bs@(_ ⊰ _ ⊰ _)   = a ⋅ bs
  _⨯_ {ℕ.𝐒 n₁}{ℕ.𝐒 n₂} (a ⊰ as@(_ ⊰ _)) (b ⊰ bs@(_ ⊰ _)) = (a ℕ.⋅ b) ⊰ lr where
    l : Polynomial(n₁ ℕ.+ n₂)
    l = pad ⦃ max-order-[+] ⦄ ((b ⋅ as) + (a ⋅ bs))

    r : Polynomial(ℕ.𝐒(n₁ ℕ.+ n₂))
    r = var⋅ (as ⨯ bs)

    lr : Polynomial(ℕ.𝐒(n₁ ℕ.+ n₂))
    lr = [≡]-substitutionᵣ ([↔]-to-[→] max-defᵣ [≤]-of-[𝐒]) {Polynomial} (l + r)

  𝐷 : Polynomial(n) → Polynomial(ℕ.𝐏(n))
  𝐷 {ℕ.𝟎}    (singleton _) = singleton ℕ.𝟎
  𝐷 {ℕ.𝐒(n)} (a ⊰ b ⊰ p)   = {!!}

module Semantics  where
  open import Numeral.Finite as 𝕟 using (𝕟)
  import      Numeral.Natural.Oper as ℕ
  open import Numeral.Natural.Oper.Proofs
  open import Relator.Equals.Proofs.Equiv(ℕ)
  open import Structure.Function.Multi
  open import Structure.Operator
  open import Structure.Operator.Proofs
  open import Structure.Operator.Properties
  open import Structure.Relator.Properties
  open import Structure.Setoid.WithLvl
  open import Syntax.Function
  open import Syntax.Transitivity

  eval : Polynomial(n) → (ℕ → ℕ)
  eval (singleton a)    _ = a
  eval (a ⊰ al@(_ ⊰ _)) x = a ℕ.+ (x ℕ.⋅ (eval al x))

  module Proofs where
    eval-preserves-addition : ∀{x}{a : Polynomial(n₁)}{b : Polynomial(n₂)} → (eval (a + b) x ≡ (eval a x) ℕ.+ (eval b x))
    eval-preserves-addition {x = x} {singleton a}    {singleton b}    = reflexivity(_≡_)
    eval-preserves-addition {x = x} {singleton a}    {b ⊰ bs@(_ ⊰ _)} = associativity(ℕ._+_) {a}{b}
    eval-preserves-addition {x = x} {a ⊰ as@(_ ⊰ _)} {singleton b}    =
      eval ((a ⊰ as) + (singleton b)) x            🝖[ _≡_ ]-[]
      (a ℕ.+ b) ℕ.+ (x ℕ.⋅ (eval as x))            🝖[ _≡_ ]-[ associativity(ℕ._+_) {a}{b} ]
      a ℕ.+ (b ℕ.+ (x ℕ.⋅ (eval as x)))            🝖[ _≡_ ]-[ congruence₂ᵣ(ℕ._+_)(a) (commutativity(ℕ._+_) {x = b}) ]
      a ℕ.+ ((x ℕ.⋅ (eval as x)) ℕ.+ b)            🝖[ _≡_ ]-[ associativity(ℕ._+_) {a}{x ℕ.⋅ eval as x} ]-sym
      (a ℕ.+ (x ℕ.⋅ (eval as x))) ℕ.+ b            🝖[ _≡_ ]-[]
      (eval (a ⊰ as) x) ℕ.+ (eval (singleton b) x) 🝖-end
    eval-preserves-addition {x = x} {a ⊰ as@(_ ⊰ _)} {b ⊰ bs@(_ ⊰ _)} =
      eval ((a ⊰ as) + (b ⊰ bs)) x                                  🝖[ _≡_ ]-[]
      eval ((a ℕ.+ b) ⊰ (as + bs)) x                                🝖[ _≡_ ]-[]
      (a ℕ.+ b) ℕ.+ (x ℕ.⋅ (eval (as + bs) x))                      🝖[ _≡_ ]-[ congruence₂ᵣ(ℕ._+_)(a ℕ.+ b) (congruence₂ᵣ(ℕ._⋅_)(x) (eval-preserves-addition {x = x}{as}{bs})) ]
      (a ℕ.+ b) ℕ.+ (x ℕ.⋅ ((eval as x) ℕ.+ (eval bs x)))           🝖[ _≡_ ]-[ congruence₂ᵣ(ℕ._+_)(a ℕ.+ b) (distributivityₗ(ℕ._⋅_)(ℕ._+_) {x}{eval as x}{eval bs x}) ]
      (a ℕ.+ b) ℕ.+ ((x ℕ.⋅ (eval as x)) ℕ.+ (x ℕ.⋅ (eval bs x)))   🝖[ _≡_ ]-[ One.associate-commute4 {a = a}{b = b}{c = x ℕ.⋅ (eval as x)}{d = x ℕ.⋅ (eval bs x)} (commutativity(ℕ._+_) {b}) ]
      (a ℕ.+ (x ℕ.⋅ (eval as x))) ℕ.+ (b ℕ.+ (x ℕ.⋅ (eval bs x)))   🝖[ _≡_ ]-[]
      (eval (a ⊰ as) x) ℕ.+ (eval (b ⊰ bs) x)                       🝖-end
