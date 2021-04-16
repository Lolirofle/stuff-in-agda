module Type.Properties.Homotopy.Proofs where

import      Data.Tuple as Tuple
open import Functional
open import Function.Axioms
open import Logic
open import Logic.Classical
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Numeral.Natural
open import Type
open import Type.Dependent
open import Type.Properties.Homotopy
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Type.Properties.Singleton.Proofs
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Structure.Type.Identity
open import Syntax.Function
open import Syntax.Transitivity

private variable ℓ ℓₑ ℓₑₑ ℓₚ ℓ₁ ℓ₂ : Lvl.Level
private variable n : ℕ

module _ {ℓ} ⦃ equiv : ∀{T : Type{ℓ}} → Equiv{ℓ}(T) ⦄ where
  private variable T : Type{ℓ}
  {-
  private open module EquivEquiv{T} = Equiv(equiv{T}) using () renaming (_≡_ to _≡ₑ_)
  module _ ⦃ identElim : ∀{ℓ}{T : Type{ℓ}} → IdentityEliminator(_≡ₑ_ {T = T}) ⦄ where
    constant-endofunction-existence-on-equivalence-is-hset : ∀{x y : T} → ∃{Obj = (x ≡ y) → (x ≡ y)}(Constant) → HomotopyLevel(2)(T)
    HomotopyLevel.proof (constant-endofunction-existence-on-equivalence-is-hset ([∃]-intro const)) {x = x} {y} {xy₁} {xy₂} = {!!} where
      equivalence-endofunction-invertibleₗ : ∀{f : ∀{x y : T} → (x ≡ y) → (x ≡ y)} → (∀{x y : T} → Invertibleₗ(f{x}{y}))
      ∃.witness (equivalence-endofunction-invertibleₗ {T = T}{f = f} {x}{y}) xy =
        xy 🝖 symmetry(_≡ₑ_) (f(reflexivity _))
      Tuple.left (∃.proof equivalence-endofunction-invertibleₗ) = {!!}
      Inverseₗ.proof (Tuple.right (∃.proof (equivalence-endofunction-invertibleₗ {T = T}{f = f} {x}{y}))) {xy} = idElim(_≡ₑ_) ⦃ inst = identElim{T = T} ⦄ (xy ↦ (f(xy) 🝖 symmetry(_≡ₑ_) (f(reflexivity(_≡ₑ_))) ≡ₑ xy)) {!!} xy
  -}

  HomotopyLevel-zero-step-is-one : (∀{x y : T} → HomotopyLevel(0)(x ≡ y)) → HomotopyLevel(1)(T)
  HomotopyLevel.proof (HomotopyLevel-zero-step-is-one p) {x}{y} = Σ.left(HomotopyLevel.proof(p{x}{y}))

  HomotopyLevel-step-is-successor : (∀{x y : T} → HomotopyLevel(n)(x ≡ y)) → HomotopyLevel(𝐒(n))(T)
  HomotopyLevel-step-is-successor {n = 𝟎}      = HomotopyLevel-zero-step-is-one
  HomotopyLevel-step-is-successor {n = 𝐒(n)} p = intro(\{x}{y} → HomotopyLevel.proof(p{x}{y}))

module _
  ⦃ equiv : ∀{ℓ}{T : Type{ℓ}} → Equiv{ℓ}(T) ⦄
  ⦃ funcExt : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}}{P : T → Stmt{ℓ₂}} → DependentImplicitFunctionExtensionality(T)(P) ⦄
  ⦃ prop-eq : ∀{ℓ}{T : Type{ℓ}}{x y : T} → MereProposition(x ≡ y) ⦄
  where

  private variable T : Type{ℓ}

  HomotopyLevel-prop₊ : MereProposition(Names.HomotopyLevel(𝐒(n))(T))
  HomotopyLevel-prop₊ {𝟎}    = prop-universal ⦃ prop-p = prop-universal ⦃ prop-p = prop-eq ⦄ ⦄
  HomotopyLevel-prop₊ {𝐒(n)} = prop-universal ⦃ prop-p = prop-universal ⦃ prop-p = HomotopyLevel-prop₊ {n} ⦄ ⦄

  module _
    (base₁ : ∀{ℓ}{A : Type{ℓ}} → HomotopyLevel(1)(A) → HomotopyLevel(2)(A))
    where

    HomotopyLevel-one-is-zero-step : HomotopyLevel(1)(T) → (∀{x y : T} → HomotopyLevel(0)(x ≡ y))
    HomotopyLevel.proof(HomotopyLevel-one-is-zero-step h1 {x} {y}) = intro (HomotopyLevel.proof h1) (HomotopyLevel.proof(base₁ h1))

    HomotopyLevel-successor-step : HomotopyLevel(𝐒(n))(T) → (∀{x y : T} → HomotopyLevel(n)(x ≡ y))
    HomotopyLevel-successor-step {n = 𝟎}      = HomotopyLevel-one-is-zero-step
    HomotopyLevel-successor-step {n = 𝐒(n)} p = intro(HomotopyLevel.proof p)

    HomotopyLevel-successor : HomotopyLevel(n)(T) → HomotopyLevel(𝐒(n))(T)
    HomotopyLevel-successor {n = 0}       h0   = MereProposition.uniqueness(unit-is-prop ⦃ proof = intro (Σ.left h0) (Σ.right h0) ⦄)
    HomotopyLevel-successor {n = 1}            = base₁
    HomotopyLevel-successor {n = 𝐒(𝐒(n))} hssn = HomotopyLevel-successor {n = 𝐒(n)} hssn

{-
    {- TODO: The zero case needs assumptions about the sigma type because it is not a mere proposition unless both A and equality are mere propositions. So first, prove if equality on the sigma type depends only on its components, and its types are mere propositions, then the sigma type is a mere proposition. Secondly, one can use that proof here
    HomotopyLevel-prop : MereProposition(HomotopyLevel(n)(A))
    HomotopyLevel-prop {𝟎} = intro {!!}
    HomotopyLevel-prop {𝐒 n} = {!!}
    -}

{-
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-equiv : Equiv{ℓₑ}(Equiv._≡_ equiv) ⦄ where
    -- TODO: ComputablyDecidable → UIP (https://homotopytypetheory.org/2012/03/30/a-direct-proof-of-hedbergs-theorem/)
    -- TODO: http://www.cse.chalmers.se/~nad/listings/equality/Equality.Decidable-UIP.html
  classical-to-uip : (∀{x y : T} → ((x ≡ y) ∨ (x ≢ y))) → UniqueIdentityProofs(T)
  MereProposition.uniqueness (classical-to-uip {T = T} dec {x} {y}) {xy₁} {xy₂} = {!p xy₁!} where
    {-
    p : ∀{x y : T} → (x ≡ y) → Stmt
    p {x}{y} eq with dec{x}{x} | dec{x}{y}
    ... | [∨]-introₗ xx  | [∨]-introₗ xy  = eq ≡ transitivity(_≡_) xx xy
    ... | [∨]-introₗ xx  | [∨]-introᵣ nxy with () ← nxy eq
    ... | [∨]-introᵣ nxx | [∨]-introₗ _   with () ← nxx [≡]-intro
    -}

    dec-eq : ∀{x y} → (x ≡ y) → (x ≡ y)
    dec-eq {x}{y} eq with dec{x}{y}
    ... | [∨]-introₗ xy  = xy
    ... | [∨]-introᵣ nxy with () ← nxy eq

    dec-eq-unique : ∀{x y}{xy₁ xy₂ : x ≡ y} → (dec-eq xy₁ ≡ dec-eq xy₂)
    dec-eq-unique {x}{y} {xy₁} with dec{x}{y}
    ... | [∨]-introₗ _   = ?
    ... | [∨]-introᵣ nxy with () ← nxy xy₁

    dec-eq-unit : ∀{x y}{eq : x ≡ y} → (eq ≡ dec-eq eq)
    dec-eq-unit  {x}{y}{eq} with dec{y}{y} | dec{x}{y}
    ... | [∨]-introₗ yy | [∨]-introₗ xy = {!!}
    ... | [∨]-introₗ yy | [∨]-introᵣ x₂ = {!!}
    ... | [∨]-introᵣ x₁ | [∨]-introₗ x₂ = {!!}
    ... | [∨]-introᵣ x₁ | [∨]-introᵣ x₂ = {!!}

{-    p : ∀{x y : T} → (xy : x ≡ y) → (xy ≡ dec-eq(xy))
    p {x}{y} [≡]-intro with dec{x}{x} | dec{x}{y}
    ... | [∨]-introₗ a | [∨]-introₗ x₁ = {![≡]-intro!}
    ... | [∨]-introₗ a | [∨]-introᵣ x₁ = {!!}
    ... | [∨]-introᵣ a | [∨]-introₗ x₁ = {!!}
    ... | [∨]-introᵣ a | [∨]-introᵣ x₁ = {!!}
-}
-}
-}
