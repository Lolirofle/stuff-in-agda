module Structure.Relator.Ordering.Lattice where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional hiding (⊤ ; ⊥)
open import Logic.Predicate
open import Logic.Propositional.Theorems
open import Structure.Relator.Ordering
open import Structure.Relator.Properties hiding (antisymmetry ; asymmetry ; transitivity ; reflexivity ; irreflexivity)
open import Type

private variable ℓ₁ ℓ₂ ℓ₃ : Lvl.Level

module _ {T : Type{ℓ₁}} where
  record Top (_≤_ : T → T → Stmt{ℓ₂}) (P : T → Stmt{ℓ₃}) (m : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field
      ⦃ membership ⦄ : P(m)
      proof : ∀{x : T} → ⦃ _ : P(x) ⦄ → (x ≤ m)

  module _ (_≤_ : T → T → Stmt{ℓ₂}) where
    Bottom : (P : T → Stmt{ℓ₃}) (m : T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
    Bottom = Top(swap(_≤_))
    module Bottom{ℓ₂}{ℓ₃}{_≤_} = Top{ℓ₂}{ℓ₃}{swap(_≤_)}

  record RightBound (_≤_ : T → T → Stmt{ℓ₂}) (P : T → Stmt{ℓ₃}) (b : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field proof : ∀{x : T} → ⦃ _ : P(x) ⦄ → (x ≤ b)

  module _ (_≤_ : T → T → Stmt{ℓ₂}) where
    LeftBound : (P : T → Stmt{ℓ₃}) → (b : T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
    LeftBound = RightBound(swap(_≤_))
    module LeftBound{ℓ₂}{ℓ₃}{_≤_} = RightBound{ℓ₂}{ℓ₃}{swap(_≤_)}

  record Meet (_≤_ : T → T → Stmt{ℓ₂}) (P : T → Stmt{ℓ₃}) (inf : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field
      bound : LeftBound(_≤_)(P) (inf)
      extreme : RightBound(_≤_)(LeftBound(_≤_)(P)) (inf)

  module _ (_≤_ : T → T → Stmt{ℓ₂}) where
    Join : (P : T → Stmt{ℓ₃}) → (sup : T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
    Join = Meet(swap(_≤_))
    module Join{ℓ₂}{ℓ₃}{_≤_} = Meet{ℓ₂}{ℓ₃}{swap(_≤_)}

  module Complete {ℓ₃} where
    record MeetSemilattice (_≤_ : T → T → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ Lvl.𝐒(ℓ₃)} where
      constructor intro
      field proof : ∀{P : T → Stmt{ℓ₃}} → ∃(Meet(_≤_)(P))

    module _ (_≤_ : T → T → Stmt{ℓ₂}) where
      JoinSemilattice : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ Lvl.𝐒(ℓ₃)}
      JoinSemilattice = MeetSemilattice(swap(_≤_))
      module JoinSemilattice{ℓ₂}{_≤_} = MeetSemilattice{ℓ₂}{swap(_≤_)}

    record Lattice (_≤_ : T → T → Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ Lvl.𝐒(ℓ₃)} where
      constructor intro
      field
        ⦃ meet-semilattice ⦄ : MeetSemilattice(_≤_)
        ⦃ join-semilattice ⦄ : JoinSemilattice(_≤_)

      record Bounded (_≤_ : T → T → Stmt{ℓ₂}) (⊤ : T) (⊥ : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ Lvl.𝐒(ℓ₃)} where
        constructor intro
        field
          ⦃ bottom ⦄ : Weak.Properties.Extremumₗ(_≤_)(⊥)
          ⦃ top ⦄    : Weak.Properties.Extremumᵣ(_≤_)(⊤)

  top : (_≤_ : T → T → Stmt{ℓ₂}) → (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Top(_≤_)(P)) ⦄ → T
  top _ (P) ⦃ e ⦄ = [∃]-witness e

  bottom : (_≤_ : T → T → Stmt{ℓ₂}) → (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Bottom(_≤_)(P)) ⦄ → T
  bottom(_≤_) = top(swap(_≤_))

  meet : (_≤_ : T → T → Stmt{ℓ₂}) → (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Meet(_≤_)(P)) ⦄ → T
  meet _ _ ⦃ e ⦄ = [∃]-witness e

  join :  (_≤_ : T → T → Stmt{ℓ₂}) → (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Join(_≤_)(P)) ⦄ → T
  join(_≤_) = meet(swap(_≤_))

  module Oper where
    ⊥ = bottom
    ⊤ = top
    ⋁ = join
    ⋀ = meet

  -- LE is a module with synonyms when the order is interpreted as a (_≤_) (lesser than or equals) relation.
  module LE where
    Minimum    = Bottom
    Maximum    = Top
    LowerBound = LeftBound
    UpperBound = RightBound
    Supremum   = Join
    Infimum    = Meet

    module Minimum    = Bottom
    module Maximum    = Top
    module LowerBound = LeftBound
    module UpperBound = RightBound
    module Supremum   = Join
    module Infimum    = Meet

    min = bottom
    max = top
    sup = join
    inf = meet

-- TODO: https://en.wikipedia.org/wiki/Map_of_lattices
