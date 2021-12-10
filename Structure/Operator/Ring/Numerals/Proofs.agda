open import Structure.Operator.Ring
open import Structure.Setoid
open import Type

module Structure.Operator.Ring.Numerals.Proofs
  {ℓF ℓₑF ℓₙ₀}
  {F : Type{ℓF}}
  ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  ⦃ ring : Ring(_+_)(_⋅_) {ℓₙ₀} ⦄
  where

open import Functional
open import Numeral.Integer as ℤ using (ℤ)
open import Numeral.Natural as ℕ using (ℕ)
open import Structure.Operator.Ring.Numerals
open import Syntax.Number
open import Syntax.Transitivity

open Ring(ring)

module _ where
  open import Function.Iteration
  open import Logic
  open import Logic.Classical
  open import Numeral.Natural.Induction
  open import Relator.Equals renaming (_≡_ to _≡ᵢ_ ; [≡]-intro to intro) using()
  open import Structure.Function
  open import Structure.Operator
  open import Structure.Operator.Properties
  open import Structure.Relator.Properties
  open import Structure.Operator.Ring.Proofs

  instance
    𝐒-function : Function(𝐒)
    𝐒-function = BinaryOperator.unary₁ [+]-binaryOperator

  instance
    𝐏-function : Function(𝐏)
    𝐏-function = BinaryOperator.unary₁ [+]-binaryOperator

  from-ℕ-is-𝐒-iteration : ∀{n} → (from-ℕ n ≡ (𝐒 ^ n)(𝟎))
  from-ℕ-is-𝐒-iteration {ℕ.𝟎}        = reflexivity(_≡_)
  from-ℕ-is-𝐒-iteration {ℕ.𝟏}        = symmetry(_≡_) (identityₗ(_+_)(𝟎))
  from-ℕ-is-𝐒-iteration {ℕ.𝐒(ℕ.𝐒 n)} = congruence₁(𝐒) (from-ℕ-is-𝐒-iteration {ℕ.𝐒(n)})

  [⋅]-distributeᵣ-over-𝐒-iteration : ∀{n}{x} → ((𝐒 ^ n)(𝟎) ⋅ x ≡ ((_+ x) ^ n)(𝟎))
  [⋅]-distributeᵣ-over-𝐒-iteration {ℕ.𝟎}{x} =
    ((𝐒 ^ ℕ.𝟎)(𝟎) ⋅ x) 🝖[ _≡_ ]-[]
    (id(𝟎) ⋅ x)        🝖[ _≡_ ]-[]
    (𝟎 ⋅ x)            🝖[ _≡_ ]-[ absorberₗ(_⋅_)(𝟎) ]
    𝟎                  🝖[ _≡_ ]-[]
    id(𝟎)              🝖[ _≡_ ]-[]
    ((_+ x) ^ ℕ.𝟎)(𝟎)  🝖-end
  [⋅]-distributeᵣ-over-𝐒-iteration {ℕ.𝐒(n)}{x} =
    ((𝐒 ^ ℕ.𝐒(n))(𝟎) ⋅ x)        🝖[ _≡_ ]-[]
    (𝐒((𝐒 ^ n)(𝟎)) ⋅ x)          🝖[ _≡_ ]-[]
    (((𝐒 ^ n)(𝟎) + 𝟏) ⋅ x)       🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) ]
    (((𝐒 ^ n)(𝟎) ⋅ x) + (𝟏 ⋅ x)) 🝖[ _≡_ ]-[ congruence₂(_+_) ([⋅]-distributeᵣ-over-𝐒-iteration {n}{x}) (identityₗ(_⋅_)(𝟏)) ]
    ((_+ x) ^ n)(𝟎) + x          🝖[ _≡_ ]-[]
    ((_+ x) ^ ℕ.𝐒(n))(𝟎)         🝖-end

  [⋅]-distributeₗ-over-𝐒-iteration : ∀{n}{x} → (x ⋅ (𝐒 ^ n)(𝟎) ≡ ((_+ x) ^ n)(𝟎))
  [⋅]-distributeₗ-over-𝐒-iteration {ℕ.𝟎}{x} =
    (x ⋅ (𝐒 ^ ℕ.𝟎)(𝟎)) 🝖[ _≡_ ]-[]
    (x ⋅ id(𝟎))        🝖[ _≡_ ]-[]
    (x ⋅ 𝟎)            🝖[ _≡_ ]-[ absorberᵣ(_⋅_)(𝟎) ]
    𝟎                  🝖[ _≡_ ]-[]
    id(𝟎)              🝖[ _≡_ ]-[]
    ((_+ x) ^ ℕ.𝟎)(𝟎)  🝖-end
  [⋅]-distributeₗ-over-𝐒-iteration {ℕ.𝐒(n)}{x} =
    (x ⋅ (𝐒 ^ ℕ.𝐒(n))(𝟎))        🝖[ _≡_ ]-[]
    (x ⋅ 𝐒((𝐒 ^ n)(𝟎)))          🝖[ _≡_ ]-[]
    (x ⋅ ((𝐒 ^ n)(𝟎) + 𝟏))       🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) ]
    ((x ⋅ (𝐒 ^ n)(𝟎)) + (x ⋅ 𝟏)) 🝖[ _≡_ ]-[ congruence₂(_+_) ([⋅]-distributeₗ-over-𝐒-iteration {n}{x}) (identityᵣ(_⋅_)(𝟏)) ]
    ((_+ x) ^ n)(𝟎) + x          🝖[ _≡_ ]-[]
    ((_+ x) ^ ℕ.𝐒(n))(𝟎)         🝖-end

  open import Data
  open import Functional.Instance
  import      Numeral.Natural.Relation as ℕ
  open import Numeral.Natural.Equiv.Id
  open import Structure.Function
  open import Structure.Function.Domain
  import      Structure.Function.Names as Names
  open import Type.Identity

  instance
    𝐒-injective : Injective(𝐒)
    𝐒-injective = intro(cancellationᵣ(_+_))

  from-ℕ-preserve-𝐒 : ∀{n} → (from-ℕ (ℕ.𝐒(n)) ≡ 𝐒(from-ℕ n))
  from-ℕ-preserve-𝐒 {ℕ.𝟎}   = symmetry(_≡_) (identityₗ(_+_)(𝟎))
  from-ℕ-preserve-𝐒 {ℕ.𝐒 n} = reflexivity(_≡_)

  from-ℕ-natural : ∀{n} → Natural(from-ℕ n)
  from-ℕ-natural {ℕ.𝟎}    = zero
  from-ℕ-natural {ℕ.𝐒(n)} = subst (symmetry(_≡_) (from-ℕ-preserve-𝐒 {n})) (succ (from-ℕ-natural {n}))

  open import Logic.Predicate
  open import Logic.Predicate.Equiv  
  open import Structure.Relator
  Natural-induction-raw : ∀{ℓ} → (P : (x : F) → Natural(x) → Type{ℓ})
                        → P(𝟎) zero
                        → (∀{x} → (nat : Natural(x)) → P(x) nat → P(𝐒(x)) (succ nat))
                        → (∀{x y}{nat : Natural(x)} → (eq : x ≡ y) → P(x) nat → P(y) (subst eq nat))
                        → (∀{x} → (nat : Natural(x)) → P(x) nat)
  Natural-induction-raw P base step rel zero           = base
  Natural-induction-raw P base step rel (succ nat)     = step nat (Natural-induction-raw P base step rel nat)
  Natural-induction-raw P base step rel (subst eq nat) = rel eq   (Natural-induction-raw P base step rel nat)

  {-
  Natural-induction-image : ∀{ℓ} → (P : (x : F) → Natural(x) → Type{ℓ})
                        → P(𝟎) zero
                        → (∀{x} → (nat : Natural(x)) → P(x) nat → P(𝐒(x)) (succ nat))
                        → (∀{x y}{nat : Natural(x)} → (eq : x ≡ y) → P(x) nat → P(y) (subst eq nat))
                        → (∀{x} → (nat : Natural(x)) → P(x) nat)
  -}

  Natural-induction : ∀{ℓ} → (P : (∃ Natural) → Type{ℓ}) ⦃ rel : UnaryRelator(P) ⦄
                    → P([∃]-intro 𝟎 ⦃ zero ⦄)
                    → (∀{x} → P(x) → P([∃]-map 𝐒 succ x))
                    → (∀{x} → P(x))
  Natural-induction P pz ps {x} = Natural-induction-raw(\x nat → P([∃]-intro x ⦃ nat ⦄)) pz (\_ → ps) (\eq → substitute₁(P) eq) ([∃]-proof x)

  {-
  TODO: Characteristic(_+_)(_⋅_)(ℕ.𝟎) → DistinctIdentities ?

  open import Structure.Operator.Ring.Characteristic
  module _ ⦃ char : Characteristic(_+_)(_⋅_)(ℕ.𝟎) ⦄ ⦃ dist-ident : DistinctIdentities ⦄ where
    instance
      positive-nonzero : ∀{n} → ⦃ ℕ.Positive(n) ⦄ → NonZero(from-ℕ n)
      positive-nonzero {n = ℕ.𝐒 ℕ.𝟎} = {!!}
      NonZero.proof(positive-nonzero {n = ℕ.𝐒 (ℕ.𝐒 n)}) eq = NonZero.proof (positive-nonzero{ℕ.𝐒 n}) {!eq!}
  -}

  {-
  instance
    positive-nonzero : ⦃ division : Division(_+_)(_⋅_) ⦄ ⦃ dist-ident : DistinctIdentities ⦄ → ∀{n} → ⦃ ℕ.Positive(n) ⦄ → NonZero(from-ℕ n)
    NonZero.proof(positive-nonzero ⦃ dist-ident = dist-ident@(intro dist-ident-raw) ⦄ {ℕ.𝐒(ℕ.𝐒 n)}) ssn0 = dist-ident-raw (symmetry(_≡_) (identityₗ(_+_)(𝟎)) 🝖 congruence₁(𝐒) (symmetry(_≡_) (absorberᵣ(_⋅_)(𝟎) {from-ℕ (ℕ.𝐒(n))}) 🝖 congruence₂-₂(_⋅_)(from-ℕ (ℕ.𝐒 n)) {!!} 🝖 identityᵣ(_⋅_)(𝟏)) 🝖 symmetry(_≡_) (from-ℕ-preserve-𝐒 {ℕ.𝐒 n}) 🝖 ssn0)
    -- [⋅]-cancellationᵣ ⦃ nonzero = positive-nonzero ⦃ dist-ident = dist-ident ⦄ {ℕ.𝐒 n} ⦃ <> ⦄ ⦄
    -- symmetry(_≡_) (from-ℕ-preserve-𝐒 {n}) 🝖 sn0
    --  🝖 sn0 🝖 symmetry(_≡_) (absorberᵣ(_⋅_)(𝟎) {𝐒(from-ℕ n)})
    -- positive-nonzero ⦃ dist-ident ⦄ {ℕ.𝐒 ℕ.𝟎}    = dist-ident
    -- NonZero.proof (positive-nonzero ⦃ intro dist-ident ⦄ {ℕ.𝐒 (ℕ.𝐒 n)}) ssn0 = dist-ident ({!identity!} 🝖 ssn0)

  instance
    from-ℕ-injective : ⦃ division : Division(_+_)(_⋅_) ⦄ ⦃ dist-ident : DistinctIdentities ⦄ → Injective(from-ℕ)
    Injective.proof (from-ℕ-injective ⦃ dist-ident = dist-ident@(intro dist-ident-raw) ⦄) = p where
      p : Names.Injective(from-ℕ)
      p {ℕ.𝟎}  {ℕ.𝟎}   xy = intro
      p {ℕ.𝟎}  {ℕ.𝐒 y} xy with () ← dist-ident-raw {!!}
      -- ([⋅]-cancellationₗ ⦃ nonzero = positive-nonzero ⦃ dist-ident ⦄ {ℕ.𝐒 y} ⦄ (identityᵣ(_⋅_)(𝟏) 🝖 xy 🝖 symmetry(_≡_) (absorberᵣ(_⋅_)(𝟎) {from-ℕ (ℕ.𝐒 y)})))
      p {ℕ.𝐒 x}{ℕ.𝟎}   xy with () ← dist-ident-raw ([⋅]-cancellationₗ ⦃ nonzero = positive-nonzero ⦃ dist-ident = dist-ident ⦄ {ℕ.𝐒 x} ⦄ (identityᵣ(_⋅_)(𝟏) 🝖 xy 🝖 symmetry(_≡_) (absorberᵣ(_⋅_)(𝟎) {from-ℕ (ℕ.𝐒 x)})))
      p {ℕ.𝐒 x}{ℕ.𝐒 y} xy = congruence₁(ℕ.𝐒) (p{x}{y} {!!})

{-
  test : ∀{x} → ((x / 2) ⦃ {!!} ⦄ + (x / 2) ⦃ {!!} ⦄ ≡ x)
  test = {!!}
-}
  -}
