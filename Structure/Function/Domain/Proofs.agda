module Structure.Function.Domain.Proofs where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
import      Lvl
open import Functional
open import Function.Domains
open import Function.Equals
import      Function.Names as Names
open import Functional.Instance
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Setoid.Uniqueness
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Transitivity
open import Type
open import Type.Dependent

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₒ₁ ℓₒ₂ : Lvl.Level
private variable T A B C : Type{ℓ}

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ (f : A → B) where
  injective-to-unique : Injective(f) → ∀{y} → Unique(x ↦ f(x) ≡ y)
  injective-to-unique (intro(inj)) {y} {x₁}{x₂} fx₁y fx₂y =
    inj{x₁}{x₂} (fx₁y 🝖 symmetry(_≡_) fx₂y)

  instance
    bijective-to-injective : ⦃ bij : Bijective(f) ⦄ → Injective(f)
    Injective.proof(bijective-to-injective ⦃ intro(bij) ⦄) {x₁}{x₂} (fx₁fx₂) =
      ([∃!]-existence-eq (bij {f(x₂)}) {x₁} (fx₁fx₂))
      🝖 symmetry(_≡_) ([∃!]-existence-eq (bij {f(x₂)}) {x₂} (reflexivity(_≡_)))
    -- ∀{y : B} → ∃!(x ↦ f(x) ≡ y)
    -- ∃!(x ↦ f(x) ≡ f(x₂))
    -- ∀{x} → (f(x) ≡ f(x₂)) → (x ≡ [∃!]-witness e)
    -- (f(x₁) ≡ f(x₂)) → (x₁ ≡ [∃!]-witness e)
    --
    -- ∀{y : B} → ∃!(x ↦ f(x) ≡ y)
    -- ∃!(x ↦ f(x) ≡ f(x₂))
    -- ∀{x} → (f(x) ≡ f(x₂)) → (x ≡ [∃!]-witness e)
    -- (f(x₂) ≡ f(x₂)) → (x₂ ≡ [∃!]-witness e)

  instance
    bijective-to-surjective : ⦃ bij : Bijective(f) ⦄ → Surjective(f)
    Surjective.proof(bijective-to-surjective ⦃ intro(bij) ⦄) {y} =
      [∃!]-existence (bij {y})

  instance
    injective-surjective-to-bijective : ⦃ inj : Injective(f) ⦄ → ⦃ surj : Surjective(f) ⦄ → Bijective(f)
    Bijective.proof(injective-surjective-to-bijective ⦃ inj ⦄ ⦃ intro(surj) ⦄) {y} =
      [∃!]-intro surj (injective-to-unique inj)

  injective-surjective-bijective-equivalence : (Injective(f) ∧ Surjective(f)) ↔ Bijective(f)
  injective-surjective-bijective-equivalence =
    [↔]-intro
      (\bij → [∧]-intro (bijective-to-injective ⦃ bij = bij ⦄) (bijective-to-surjective ⦃ bij = bij ⦄))
      (\{([∧]-intro inj surj) → injective-surjective-to-bijective ⦃ inj = inj ⦄ ⦃ surj = surj ⦄})

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  instance
    injective-relator : UnaryRelator(Injective{A = A}{B = B})
    Injective.proof (UnaryRelator.substitution injective-relator {f₁}{f₂} (intro f₁f₂) (intro inj-f₁)) f₂xf₂y = inj-f₁ (f₁f₂ 🝖 f₂xf₂y 🝖 symmetry(_≡_) f₁f₂)

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  instance
    surjective-relator : UnaryRelator(Surjective{A = A}{B = B})
    Surjective.proof (UnaryRelator.substitution surjective-relator {f₁}{f₂} (intro f₁f₂) (intro surj-f₁)) {y} = [∃]-map-proof (\{x} f₁xf₁y → symmetry(_≡_) (f₁f₂{x}) 🝖 f₁xf₁y) (surj-f₁{y})

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  instance
    bijective-relator : UnaryRelator(Bijective{A = A}{B = B})
    UnaryRelator.substitution bijective-relator {f₁}{f₂} f₁f₂ bij-f₁ = injective-surjective-to-bijective(f₂) ⦃ substitute₁(Injective) f₁f₂ (bijective-to-injective(f₁)) ⦄ ⦃ substitute₁(Surjective) f₁f₂ (bijective-to-surjective(f₁)) ⦄ where
      instance _ = bij-f₁

module _
  {A : Type{ℓₒ₁}}
  {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  where

  invᵣ-surjective : (f : A → B) ⦃ surj : Surjective(f) ⦄ → (B → A)
  invᵣ-surjective _ ⦃ surj ⦄ (y) = [∃]-witness(Surjective.proof surj{y})

module _
  {A : Type{ℓₒ₁}}
  {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B}
  where

  surjective-to-inverseᵣ : ⦃ surj : Surjective(f) ⦄ → Inverseᵣ(f)(invᵣ-surjective f)
  surjective-to-inverseᵣ ⦃ intro surj ⦄ = intro([∃]-proof surj)

module _
  {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} {f⁻¹ : B → A}
  where

  inverseᵣ-to-surjective : ⦃ inverᵣ : Inverseᵣ(f)(f⁻¹) ⦄ → Surjective(f)
  Surjective.proof inverseᵣ-to-surjective {y} = [∃]-intro (f⁻¹(y)) ⦃ inverseᵣ(f)(f⁻¹) ⦄

  Inverse-symmetry : Inverse(f)(f⁻¹) → Inverse(f⁻¹)(f)
  Inverse-symmetry ([∧]-intro (intro inverₗ) (intro inverᵣ)) = [∧]-intro (intro inverᵣ) (intro inverₗ)

module _
  {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B}
  where

  invertibleᵣ-to-surjective : ⦃ inverᵣ : Invertibleᵣ(f) ⦄ → Surjective(f)
  ∃.witness (Surjective.proof(invertibleᵣ-to-surjective ⦃ inverᵣ ⦄) {y}) = [∃]-witness inverᵣ(y)
  ∃.proof   (Surjective.proof(invertibleᵣ-to-surjective ⦃ inverᵣ ⦄) {y}) = inverseᵣ _ _ ⦃ [∧]-elimᵣ([∃]-proof inverᵣ) ⦄

  -- Every surjective function has a right inverse with respect to function composition.
  -- One of the right inverse functions of a surjective function f.
  -- Specifically the one that is used in the constructive proof of surjectivity for f.
  -- Without assuming that the value used in the proof of surjectivity constructs a function, this would be unprovable because it is not guaranteed in arbitrary setoids.
  -- Note: The usual formulation of this proposition (without assuming `inv-func`) is equivalent to the axiom of choice from set theory in classical logic.
  surjective-to-invertibleᵣ : ⦃ surj : Surjective(f) ⦄ ⦃ inv-func : Function(invᵣ-surjective f) ⦄ → Invertibleᵣ(f)
  ∃.witness (surjective-to-invertibleᵣ)                                                 = invᵣ-surjective f
  ∃.proof   (surjective-to-invertibleᵣ ⦃ surj = intro surj ⦄ ⦃ inv-func = inv-func ⦄)   = [∧]-intro inv-func (intro([∃]-proof surj))

  invertibleᵣ-when-surjective : Invertibleᵣ(f) ↔ Σ(Surjective(f)) (surj ↦ Function(invᵣ-surjective f ⦃ surj ⦄))
  invertibleᵣ-when-surjective =
    [↔]-intro
      (surj   ↦ surjective-to-invertibleᵣ ⦃ Σ.left surj ⦄ ⦃ Σ.right surj ⦄)
      (inverᵣ ↦ intro (invertibleᵣ-to-surjective ⦃ inverᵣ ⦄) ([∧]-elimₗ([∃]-proof inverᵣ)))

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} {f⁻¹ : B → A} ⦃ inverᵣ : Inverseᵣ(f)(f⁻¹) ⦄
  where

  -- Note: This states that a function which is injective and surjective (bijective) is a function, but another way of satisfying this proposition is from a variant of axiom of choice which directly state that the right inverse of a surjective function always exist.
  inverseᵣ-function : ⦃ inj : Injective(f) ⦄ → Function(f⁻¹)
  Function.congruence (inverseᵣ-function) {y₁}{y₂} y₁y₂ =
    injective(f) (
      f(f⁻¹(y₁)) 🝖-[ inverseᵣ(f)(f⁻¹) ]
      y₁         🝖-[ y₁y₂ ]
      y₂         🝖-[ inverseᵣ(f)(f⁻¹) ]-sym
      f(f⁻¹(y₂)) 🝖-end
    )

  -- The right inverse is injective when f is a surjective function.
  inverseᵣ-injective : ⦃ func : Function(f) ⦄ → Injective(f⁻¹)
  Injective.proof(inverseᵣ-injective) {x₁}{x₂} (invᵣfx₁≡invᵣfx₂) =
    x₁         🝖-[ inverseᵣ(f)(f⁻¹) ]-sym
    f(f⁻¹(x₁)) 🝖-[ congruence₁(f) {f⁻¹(x₁)} {f⁻¹(x₂)} (invᵣfx₁≡invᵣfx₂) ]
    f(f⁻¹(x₂)) 🝖-[ inverseᵣ(f)(f⁻¹) ]
    x₂         🝖-end

  -- The right inverse is surjective when the surjective f is injective.
  inverseᵣ-surjective : ⦃ inj : Injective(f) ⦄ → Surjective(f⁻¹)
  ∃.witness (Surjective.proof inverseᵣ-surjective {x}) = f(x)
  ∃.proof   (Surjective.proof inverseᵣ-surjective {x}) =
    injective(f) (
      f(f⁻¹(f(x))) 🝖-[ inverseᵣ(f)(f⁻¹) ]
      f(x)         🝖-end
    )

  -- The right inverse is a left inverse when the surjective f is injective.
  inverseᵣ-inverseₗ : ⦃ inj : Injective(f) ⦄ → Inverseₗ(f)(f⁻¹)
  inverseᵣ-inverseₗ = intro([∃]-proof(surjective(f⁻¹) ⦃ inverseᵣ-surjective ⦄))

  -- The right inverse is bijective when the surjective f is injective.
  inverseᵣ-bijective : ⦃ func : Function(f) ⦄ ⦃ inj : Injective(f) ⦄ → Bijective(f⁻¹)
  inverseᵣ-bijective = injective-surjective-to-bijective(f⁻¹) ⦃ inverseᵣ-injective ⦄ ⦃ inverseᵣ-surjective ⦄

  inverseᵣ-inverse : ⦃ inj : Injective(f) ⦄ → Inverse(f)(f⁻¹)
  inverseᵣ-inverse = [∧]-intro inverseᵣ-inverseₗ inverᵣ

  -- The right inverse is an unique right inverse when f is injective.
  inverseᵣ-unique-inverseᵣ : ⦃ inj : Injective(f) ⦄ → ∀{g} → (f ∘ g ⊜ id) → (g ⊜ f⁻¹)
  inverseᵣ-unique-inverseᵣ {g = g} (intro p) = intro $ \{x} →
    g(x)         🝖-[ inverseₗ(f)(f⁻¹) ⦃ inverseᵣ-inverseₗ ⦄ ]-sym
    f⁻¹(f(g(x))) 🝖-[ congruence₁(f⁻¹) ⦃ inverseᵣ-function ⦄ p ]
    f⁻¹(x)       🝖-end

  -- The right inverse is an unique left inverse function.
  inverseᵣ-unique-inverseₗ : ∀{g} ⦃ _ : Function(g) ⦄ → (g ∘ f ⊜ id) → (g ⊜ f⁻¹)
  inverseᵣ-unique-inverseₗ {g = g} (intro p) = intro $ \{x} →
    g(x)         🝖-[ congruence₁(g) (inverseᵣ(f)(f⁻¹)) ]-sym
    g(f(f⁻¹(x))) 🝖-[ p{f⁻¹(x)} ]
    f⁻¹(x)       🝖-end

  -- The right inverse is invertible.
  inverseᵣ-invertibleᵣ : ⦃ func : Function(f) ⦄ ⦃ inj : Injective(f) ⦄ → Invertibleᵣ(f⁻¹)
  ∃.witness inverseᵣ-invertibleᵣ                   = f
  ∃.proof   (inverseᵣ-invertibleᵣ ⦃ func = func ⦄) = [∧]-intro func inverseᵣ-inverseₗ

  -- TODO: invᵣ-unique-function : ∀{g} → (invᵣ(f) ∘ g ⊜ id) → (g ⊜ f)

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} {f⁻¹ : B → A} ⦃ inverₗ : Inverseₗ(f)(f⁻¹) ⦄
  where

  inverseₗ-surjective : Surjective(f⁻¹)
  inverseₗ-surjective = inverseᵣ-to-surjective

  inverseₗ-to-injective : ⦃ invₗ-func : Function(f⁻¹) ⦄ → Injective(f)
  inverseₗ-to-injective = inverseᵣ-injective

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f   : A → B} ⦃ func     : Function(f)   ⦄
  {f⁻¹ : B → A} ⦃ inv-func : Function(f⁻¹) ⦄
  where

  inverseₗ-to-inverseᵣ : ⦃ surj : Surjective(f) ⦄ ⦃ inverₗ : Inverseₗ(f)(f⁻¹) ⦄ → Inverseᵣ(f)(f⁻¹)
  Inverseᵣ.proof inverseₗ-to-inverseᵣ {x} with [∃]-intro y ⦃ p ⦄ ← surjective f{x} =
    f(f⁻¹(x))    🝖-[ congruence₁(f) (congruence₁(f⁻¹) p) ]-sym
    f(f⁻¹(f(y))) 🝖-[ congruence₁(f) (inverseₗ(f)(f⁻¹)) ]
    f(y)         🝖-[ p ]
    x            🝖-end

  module _ ⦃ surj : Surjective(f) ⦄ ⦃ inverₗ : Inverseₗ(f)(f⁻¹) ⦄ where
    inverseₗ-injective : Injective(f⁻¹)
    Injective.proof inverseₗ-injective {x}{y} p =
      x         🝖-[ inverseᵣ(f)(f⁻¹) ⦃ inverseₗ-to-inverseᵣ ⦄ ]-sym
      f(f⁻¹(x)) 🝖-[ congruence₁(f) p ]
      f(f⁻¹(y)) 🝖-[ inverseᵣ(f)(f⁻¹) ⦃ inverseₗ-to-inverseᵣ ⦄ ]
      y         🝖-end

    inverseₗ-bijective : Bijective(f⁻¹)
    inverseₗ-bijective = injective-surjective-to-bijective(f⁻¹) ⦃ inverseₗ-injective ⦄ ⦃ inverseₗ-surjective ⦄

    inverseₗ-to-surjective : Surjective(f)
    inverseₗ-to-surjective = inverseᵣ-surjective ⦃ inj = inverseₗ-injective ⦄

    inverseₗ-to-bijective : Bijective(f)
    inverseₗ-to-bijective = injective-surjective-to-bijective(f) ⦃ inverseₗ-to-injective ⦄ ⦃ inverseₗ-to-surjective ⦄

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} {f⁻¹ : B → A} ⦃ inver : Inverse(f)(f⁻¹) ⦄
  where

  inverse-to-surjective : Surjective(f)
  inverse-to-surjective = inverseᵣ-to-surjective ⦃ inverᵣ = [∧]-elimᵣ inver ⦄

  module _ ⦃ inv-func : Function(f⁻¹) ⦄ where
    inverse-to-injective : Injective(f)
    inverse-to-injective = inverseₗ-to-injective ⦃ inverₗ = [∧]-elimₗ inver ⦄

    inverse-to-bijective : Bijective(f)
    inverse-to-bijective = injective-surjective-to-bijective(f) ⦃ inj = inverse-to-injective ⦄ ⦃ surj = inverse-to-surjective ⦄

  inverse-surjective : Surjective(f⁻¹)
  inverse-surjective = inverseₗ-surjective ⦃ inverₗ = [∧]-elimₗ inver ⦄

  module _ ⦃ func : Function(f) ⦄ where
    inverse-injective : Injective(f⁻¹)
    inverse-injective = inverseᵣ-injective ⦃ inverᵣ = [∧]-elimᵣ inver ⦄ ⦃ func = func ⦄

    inverse-bijective : Bijective(f⁻¹)
    inverse-bijective = injective-surjective-to-bijective(f⁻¹) ⦃ inj = inverse-injective ⦄ ⦃ surj = inverse-surjective ⦄

  inverse-function-when-injective : Function(f⁻¹) ↔ Injective(f)
  inverse-function-when-injective =
    [↔]-intro
      (inj ↦ inverseᵣ-function ⦃ inverᵣ = [∧]-elimᵣ inver ⦄ ⦃ inj = inj ⦄)
      (inv-func ↦ inverse-to-injective ⦃ inv-func = inv-func ⦄)

  function-when-inverse-injective : Function(f) ↔ Injective(f⁻¹)
  function-when-inverse-injective =
    [↔]-intro
      (inv-inj ↦ intro(\{x y} → xy ↦ injective(f⁻¹) ⦃ inv-inj ⦄ (
        f⁻¹(f(x)) 🝖-[ inverseₗ(f)(f⁻¹) ⦃ [∧]-elimₗ inver ⦄ ]
        x         🝖-[ xy ]
        y         🝖-[ inverseₗ(f)(f⁻¹) ⦃ [∧]-elimₗ inver ⦄ ]-sym
        f⁻¹(f(y)) 🝖-end
      )))
      (func ↦ inverse-injective ⦃ func = func ⦄)

  -- TODO: inverse-function-when-bijective : Function(f⁻¹) ↔ Bijective(f)
  -- Surjective(f) ↔ Injective(f⁻¹)
  -- Injective(f) ↔ Surjective(f⁻¹)

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} ⦃ inver : Invertible(f) ⦄
  where

  invertible-elimₗ : Invertibleₗ(f)
  invertible-elimₗ = [∃]-map-proof (Tuple.mapRight [∧]-elimₗ) inver

  invertible-elimᵣ : Invertibleᵣ(f)
  invertible-elimᵣ = [∃]-map-proof (Tuple.mapRight [∧]-elimᵣ) inver

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  where

  private variable f : A → B

  -- invertible-intro : ⦃ inverₗ : Invertibleₗ(f) ⦄ ⦃ inverᵣ : Invertibleᵣ(f) ⦄ → Invertible(f)
  -- invertible-intro = {!!}

  bijective-to-invertible : ⦃ bij : Bijective(f) ⦄ → Invertible(f)
  bijective-to-invertible {f = f} ⦃ bij = bij ⦄ = [∃]-intro f⁻¹ ⦃ [∧]-intro f⁻¹-function ([∧]-intro f⁻¹-inverseₗ f⁻¹-inverseᵣ) ⦄ where
    f⁻¹ : B → A
    f⁻¹ = invᵣ-surjective f ⦃ bijective-to-surjective(f) ⦄

    f⁻¹-inverseᵣ : Inverseᵣ(f)(f⁻¹)
    f⁻¹-inverseᵣ = surjective-to-inverseᵣ ⦃ surj = bijective-to-surjective(f) ⦄

    f⁻¹-inverseₗ : Inverseₗ(f)(f⁻¹)
    f⁻¹-inverseₗ = inverseᵣ-inverseₗ ⦃ inverᵣ = f⁻¹-inverseᵣ ⦄  ⦃ inj = bijective-to-injective(f) ⦄

    f⁻¹-function : Function(f⁻¹)
    f⁻¹-function = inverseᵣ-function ⦃ inverᵣ = f⁻¹-inverseᵣ ⦄ ⦃ inj = bijective-to-injective(f) ⦄

  invertible-to-bijective : ⦃ inver : Invertible(f) ⦄ → Bijective(f)
  invertible-to-bijective {f} ⦃ ([∃]-intro f⁻¹ ⦃ [∧]-intro func inver ⦄) ⦄ =
    injective-surjective-to-bijective(f)
      ⦃ inj  = inverse-to-injective  ⦃ inver = inver ⦄ ⦃ inv-func = func ⦄ ⦄
      ⦃ surj = inverse-to-surjective ⦃ inver = inver ⦄ ⦄

  invertible-when-bijective : Invertible(f) ↔ Bijective(f)
  invertible-when-bijective = [↔]-intro (bij ↦ bijective-to-invertible ⦃ bij ⦄) (inver ↦ invertible-to-bijective ⦃ inver ⦄)
