module Type.Properties.Homotopy.Proofs where

open import BidirectionalFunction as ↔
import      Data.Tuple as Tuple
open import Functional
open import Logic
open import Logic.Classical
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Numeral.Natural
open import Type
open import Type.Dependent.Sigma
open import Type.Properties.Homotopy
open import Type.Properties.MereProposition
open import Type.Properties.MereProposition.Proofs
open import Type.Properties.Proofs
open import Type.Properties.Singleton
open import Type.Properties.Singleton.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Structure.Type.Identity
open import Syntax.Function
open import Syntax.Transitivity

private variable ℓ ℓₑ ℓₑₑ ℓₚ ℓ₁ ℓ₂ : Lvl.Level
private variable n : ℕ

module _ ⦃ equiv : ∀{T : Type{ℓ}} → Equiv{ℓ}(T) ⦄ where
  private variable T : Type{ℓ}

  HomotopyLevel₀-IsUnit : HomotopyLevel(𝟎)(T) ↔ IsUnit(T)
  HomotopyLevel₀-IsUnit = intro (\(intro x p) → intro(intro x p)) (\(intro(intro x p)) → intro x p)

  HomotopyLevel₁-MereProposition : HomotopyLevel(𝟏)(T) ↔ MereProposition(T)
  HomotopyLevel₁-MereProposition = intro (\(intro p) → intro p) (\(intro p) → intro p)

  HomotopyLevel-stepᵣ : (∀{x y : T} → HomotopyLevel(n)(x ≡ y)) → HomotopyLevel(𝐒(n))(T)
  HomotopyLevel-stepᵣ {n = 𝟎}    p = intro \{x}{y} → Σ.left(HomotopyLevel.proof(p{x}{y}))
  HomotopyLevel-stepᵣ {n = 𝐒(n)} p = intro(\{x}{y} → HomotopyLevel.proof(p{x}{y}))

  module _ (base₁ : HomotopyLevel(1)(T) → HomotopyLevel(2)(T)) where
    HomotopyLevel-stepₗ : (∀{x y : T} → HomotopyLevel(n)(x ≡ y)) ← HomotopyLevel(𝐒(n))(T)
    HomotopyLevel-stepₗ {n = 𝟎}    p = intro(intro(HomotopyLevel.proof p) (HomotopyLevel.proof(base₁ p)))
    HomotopyLevel-stepₗ {n = 𝐒(n)} p = intro(HomotopyLevel.proof p)

    HomotopyLevel-step = \{n} → ↔.intro (HomotopyLevel-stepₗ{n = n}) (HomotopyLevel-stepᵣ{T = T}{n = n})

  module _ (base₁ : ∀{T : Type{ℓ}} → Names.HomotopyLevel(1)(T) → Names.HomotopyLevel(2)(T)) where
    HomotopyLevelRaw-successor : Names.HomotopyLevel(n)(T) → Names.HomotopyLevel(𝐒(n))(T)
    HomotopyLevelRaw-successor {𝟎}      h0   = MereProposition.uniqueness(unit-is-prop ⦃ proof = intro (Σ.left h0) (Σ.right h0) ⦄)
    HomotopyLevelRaw-successor {𝟏}           = base₁
    HomotopyLevelRaw-successor {𝐒(𝐒 n)} hssn = HomotopyLevelRaw-successor {𝐒 n} hssn

  module _ (base₁ : ∀{T : Type{ℓ}} → HomotopyLevel(1)(T) → HomotopyLevel(2)(T)) where
    HomotopyLevel-successor : HomotopyLevel(n)(T) → HomotopyLevel(𝐒(n))(T)
    HomotopyLevel-successor (intro h) = intro(HomotopyLevelRaw-successor(\p → HomotopyLevel.proof(base₁(intro p))) h)

module _
  ⦃ equiv : ∀{ℓ}{T : Type{ℓ}} → Equiv{ℓ}(T) ⦄
  ⦃ funcExt : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}}{P : T → Stmt{ℓ₂}} → DependentImplicitFunctionExtensionality(T)(P) ⦄
  where

  private variable T : Type{ℓ}

  module _ ⦃ prop : ∀{x y : T} → MereProposition(x ≡ y) ⦄ where
    HomotopyLevel₁Raw-prop : MereProposition(Names.HomotopyLevel(𝟏)(T))
    HomotopyLevel₁Raw-prop = prop-universal ⦃ prop-p = prop-universal ⦄

    module _ ⦃ func : Function{B = HomotopyLevel(𝟏)(T)}(intro) ⦄ where
      HomotopyLevel₁-prop : MereProposition(HomotopyLevel(𝟏)(T))
      HomotopyLevel₁-prop = prop-by-inverseᵣ intro HomotopyLevel.proof ⦃ inv = intro(reflexivity _ ⦃ Equiv.reflexivity equiv ⦄) ⦄ HomotopyLevel₁Raw-prop

  module _ ⦃ prop : ∀{T : Type{ℓ}} → MereProposition(Names.HomotopyLevel(𝟏)(T)) ⦄ where
    HomotopyLevelRaw-prop-step : ∀{T : Type{ℓ}} → MereProposition(Names.HomotopyLevel(𝐒(n))(T))
    HomotopyLevelRaw-prop-step{𝟎}    = prop
    HomotopyLevelRaw-prop-step{𝐒(n)} = prop-universal ⦃ prop-p = prop-universal ⦃ prop-p = HomotopyLevelRaw-prop-step{n} ⦄ ⦄

  module _
    ⦃ prop : ∀{T : Type{ℓ}} → MereProposition(HomotopyLevel(𝟏)(T)) ⦄
    ⦃ func-intro : ∀{n}{T : Type{ℓ}} → Function{B = HomotopyLevel(n)(T)}(intro) ⦄
    ⦃ func-proof : ∀{n}{T : Type{ℓ}} → Function{A = HomotopyLevel(n)(T)}(HomotopyLevel.proof) ⦄
    where

    HomotopyLevel-prop-step : ∀{T : Type{ℓ}} → MereProposition(HomotopyLevel(𝐒(n))(T))
    HomotopyLevel-prop-step =
      prop-by-inverseᵣ intro HomotopyLevel.proof ⦃ inv = intro(reflexivity _ ⦃ Equiv.reflexivity equiv ⦄) ⦄
      (HomotopyLevelRaw-prop-step ⦃ prop-by-inverseₗ intro HomotopyLevel.proof ⦃ inv = intro(reflexivity _ ⦃ Equiv.reflexivity equiv ⦄) ⦄ prop ⦄)

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
