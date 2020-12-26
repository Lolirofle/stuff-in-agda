module Structure.Numeral.Integer.Proofs where

open import Data.Either as Either using (Left ; Right)
import      Data.Tuple as Tuple
open import Functional
open import Function.Proofs
open import Logic.IntroInstances
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Numeral.Integer
open import Structure.Relator
open import Structure.Relator.Proofs
open import Structure.Relator.Properties
open import Structure.Setoid
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Operator.Ring.Proofs
open import Structure.Operator.Ring
open import Structure.OrderedField
open import Syntax.Implication
open import Syntax.Transitivity
open import Type

private variable ℓₒ ℓₗ ℓₑ ℓₗ₁ ℓₗ₂ : Lvl.Level
private variable Z : Type{ℓₒ}
private variable _+_ _⋅_ : Z → Z → Z
private variable _≤_ : Z → Z → Type{ℓₗ}

module _ ⦃ equiv : Equiv{ℓₑ}(Z) ⦄ ⦃ int : Integer ⦃ equiv ⦄ (_+_)(_⋅_)(_≤_) ⦄ where
  open Integer(int)

  negative-induction : ∀{ℓ}{P : Z → Type{ℓ}} ⦃ rel-p : UnaryRelator(P) ⦄ → P(𝟎) → (∀{n} → (n ≤ 𝟎) → P(n) → P(𝐏(n))) → (∀{n} → (n ≤ 𝟎) → P(n))
  negative-induction {P = P} pz ps {n} neg =
    substitute₁(P) (involution(−_)) (positive-induction
      {P = P ∘ (−_)}
      ⦃ [∘]-unaryRelator ⦄
      (substitute₁ₗ(P) [−]-of-𝟎 pz)
      (\{n} pos pnn → substitute₁ₗ(P) [+]-negation-distribution (ps{− n} ([↔]-to-[→] [≤]-flip-positive pos) pnn))
      {− n}
      ([↔]-to-[→] [≤]-flip-negative neg)
    )

  induction : ∀{ℓ}{P : Z → Type{ℓ}} ⦃ rel-p : UnaryRelator(P) ⦄ → P(𝟎) → (∀{n} → (n ≤ 𝟎) → P(n) → P(𝐏(n))) → (∀{n} → (𝟎 ≤ n) → P(n) → P(𝐒(n))) → (∀{n} → P(n))
  induction pz pp ps {n} with converseTotal(_≤_) {n}{𝟎}
  ... | Left  neg = negative-induction pz pp neg
  ... | Right pos = positive-induction pz ps pos

  [⋅]-commutativity : Commutativity(_⋅_)
  [⋅]-commutativity = intro(induction{P = x ↦ ∀{y} → (x ⋅ y ≡ y ⋅ x)} ⦃ {!!} ⦄ base (const pred) (const succ)) where
    base : ∀{y} → (𝟎 ⋅ y ≡ y ⋅ 𝟎)
    base{y} =
      𝟎 ⋅ y 🝖[ _≡_ ]-[ absorberₗ(_⋅_)(𝟎) ]
      𝟎     🝖[ _≡_ ]-[ absorberᵣ(_⋅_)(𝟎) ]-sym
      y ⋅ 𝟎 🝖-end

    pred : ∀{x} → (∀{y} → (x ⋅ y ≡ y ⋅ x)) → (∀{y} → (𝐏(x) ⋅ y ≡ y ⋅ 𝐏(x)))
    pred {x} p {y} =
      𝐏(x) ⋅ y          🝖[ _≡_ ]-[]
      (x − 𝟏) ⋅ y       🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_−_) ⦃ [⋅][−]-distributivityᵣ ⦄ ]
      (x ⋅ y) − (𝟏 ⋅ y) 🝖[ _≡_ ]-[ congruence₂ᵣ(_−_) ⦃ [−]-binaryOperator ⦄ (_) (identityₗ(_⋅_)(𝟏)) ]
      (x ⋅ y) − y       🝖[ _≡_ ]-[ congruence₂ₗ(_−_) ⦃ [−]-binaryOperator ⦄ (_) p ]
      (y ⋅ x) − y       🝖[ _≡_ ]-[ congruence₂ᵣ(_−_) ⦃ [−]-binaryOperator ⦄ (_) (identityᵣ(_⋅_)(𝟏)) ]-sym
      (y ⋅ x) − (y ⋅ 𝟏) 🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_−_) ⦃ [⋅][−]-distributivityₗ ⦄ ]-sym
      y ⋅ (x − 𝟏)       🝖[ _≡_ ]-[]
      y ⋅ 𝐏(x)          🝖-end

    succ : ∀{x} → (∀{y} → (x ⋅ y ≡ y ⋅ x)) → (∀{y} → (𝐒(x) ⋅ y ≡ y ⋅ 𝐒(x)))
    succ {x} p {y} =
      𝐒(x) ⋅ y          🝖[ _≡_ ]-[]
      (x + 𝟏) ⋅ y       🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) ]
      (x ⋅ y) + (𝟏 ⋅ y) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(_) (identityₗ(_⋅_)(𝟏)) ]
      (x ⋅ y) + y       🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(_) p ]
      (y ⋅ x) + y       🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(_) (identityᵣ(_⋅_)(𝟏)) ]-sym
      (y ⋅ x) + (y ⋅ 𝟏) 🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) ]-sym
      y ⋅ (x + 𝟏)       🝖[ _≡_ ]-[]
      y ⋅ 𝐒(x)          🝖-end

  [≤]-identities : (𝟎 ≤ 𝟏)
  [≤]-identities with converseTotal(_≤_) {𝟎}{− 𝟏}
  ... | Left omi =
    omi ⇒
    (𝟎 ≤ (− 𝟏))           ⇒-[ swap apply₂ [≤][⋅]-zero ]
    (𝟎 ≤ ((− 𝟏) ⋅ (− 𝟏))) ⇒-[ _🝖 sub₂(_≡_)(_≤_) [⋅]-of-[−]  ]
    (𝟎 ≤ (𝟏 ⋅ 𝟏))         ⇒-[ _🝖 sub₂(_≡_)(_≤_) (identityₗ(_⋅_)(𝟏))  ]
    (𝟎 ≤ 𝟏)               ⇒-end
  ... | Right mio = [↔]-to-[←] [≤]-flip-positive mio

  [<]-identities : (𝟎 < 𝟏)
  [<]-identities = [≤][≢]-to-[<] [≤]-identities (NonZero.proof distinct-identities ∘ symmetry(_≡_))

  𝐒-of-𝟎 : 𝐒(𝟎) ≡ 𝟏
  𝐒-of-𝟎 =
    𝐒(𝟎)  🝖[ _≡_ ]-[]
    𝟎 + 𝟏 🝖[ _≡_ ]-[ identityₗ(_+_)(𝟎) ]
    𝟏     🝖-end

  instance
    postulate 𝐒-function : Function(𝐒)
    -- 𝐒-function = {!!}

  instance
    postulate [<]-relator : BinaryRelator(_<_)
    -- [<]-relator = {![¬]-binaryRelator!}

  [≤]-with-𝐒 : ∀{x y} → (x ≤ y) → (𝐒(x) ≤ 𝐒(y))
  [≤]-with-𝐒 = [≤][+]ₗ-preserve

  [<]-with-𝐒 : ∀{x y} → (x < y) → (𝐒(x) < 𝐒(y))
  [<]-with-𝐒 = [<][+]-preserveₗ

  [≤]-with-𝐏 : ∀{x y} → (x ≤ y) → (𝐏(x) ≤ 𝐏(y))
  [≤]-with-𝐏 = [≤][−]ₗ-preserve

  [<]-with-𝐏 : ∀{x y} → (x < y) → (𝐏(x) < 𝐏(y))
  [<]-with-𝐏 = [<][+]-preserveₗ

  𝐒-𝐏-inverse : ∀{x} → (𝐒(𝐏(x)) ≡ x)
  𝐒-𝐏-inverse = associativity(_+_) 🝖 congruence₂ᵣ(_+_)(_) (inverseFunctionₗ(_+_)(−_)) 🝖 identityᵣ(_+_)(𝟎)

  𝐏-𝐒-inverse : ∀{x} → (𝐏(𝐒(x)) ≡ x)
  𝐏-𝐒-inverse = associativity(_+_) 🝖 congruence₂ᵣ(_+_)(_) (inverseFunctionᵣ(_+_)(−_)) 🝖 identityᵣ(_+_)(𝟎)

  𝐒-order : ∀{x} → (x < 𝐒(x))
  𝐒-order {x} = induction
    {P = x ↦ x < 𝐒(x)}
    ⦃ binary-unaryRelator ⦃ rel-P = [∘]-binaryRelator ⦄ ⦄
    (subtransitivityᵣ(_<_)(_≡_) [<]-identities (symmetry(_≡_) 𝐒-of-𝟎))
    (const (p ↦ subtransitivityᵣ(_<_)(_≡_) ([<]-with-𝐏 p) (𝐏-𝐒-inverse 🝖 symmetry(_≡_) 𝐒-𝐏-inverse)))
    (const [<]-with-𝐒)

  𝐒-least-upper-bound : ∀{x m} → (x < m) → (𝐒(x) ≤ m)
  𝐒-least-upper-bound {x}{m} xm with converseTotal(_≤_) {x}{m} |  converseTotal(_≤_) {𝐒(x)}{m}
  ... | Left x₁ | Left x₂ = x₂
  ... | Left x₁ | Right x₂ = {!!} -- x<m x≤m m≤𝐒x
  ... | Right x₁ | Left x₂ = x₂
  ... | Right x₁ | Right x₂ with () ← xm x₁
  {-... | Left  𝐒xm  = {!!}
  ... | Right ¬m𝐒x = {!!}
  -}
  {-=
    𝐒(x) 🝖[ _≤_ ]-[ {!!} ]
    m    🝖-end-}

  least-upper-bound-existence : ∃{Obj = Z → Z}(S ↦ (∀{x} → (x < S(x))) ∧ (∀{x m} → (x < m) → (S(x) ≤ m)))
  ∃.witness            least-upper-bound-existence  = 𝐒
  Tuple.left  (∃.proof least-upper-bound-existence) = 𝐒-order
  Tuple.right (∃.proof least-upper-bound-existence) = 𝐒-least-upper-bound

  {- TODO: Not here. Needs invertible mult
  record Exponentiation(_^_ : Z → Z → Z) : Type{ℓₑ Lvl.⊔ Lvl.of(Z) Lvl.⊔ Lvl.of(𝟎 ≤ 𝟎)} where
    field
      base : ∀{a} → (a ^ 𝟎 ≡ 𝟏)
      step : ∀{a b} → (𝟎 ≤ b) → (a ^ (b + 𝟏) ≡ a ⋅ (a ^ b))
      neg  : ∀{a b} → (𝟎 ≤ 𝟎) → (a ^ (− b) ≡ ⅟(a ^ b))
  -}
