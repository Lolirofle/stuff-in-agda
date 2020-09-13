module Structure.Categorical.Proofs where

open import Data
open import Functional
open import Logic.Propositional
import      Lvl
open import Structure.Setoid.WithLvl
open import Structure.Categorical.Properties
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓₘ ℓₑ : Lvl.Level
private variable Obj A B : Type{ℓ}
private variable _▫_ : Obj → Obj → Type{ℓ}
private variable f : A → B

empty-morphism : ∀{ℓₘ ℓ} → Empty{ℓ} → Empty{ℓ} → Type{ℓₘ}
empty-morphism{ℓₘ}{ℓ} = empty{T = Empty{ℓ} → Type{ℓₘ}}

empty-id : Names.Reflexivity(empty-morphism{ℓₘ}{ℓ})
empty-id {x = ()}

empty-comp : Names.SwappedTransitivity(empty-morphism{ℓₘ}{ℓ})
empty-comp {x = ()}

empty-inv : Names.Symmetry(empty-morphism{ℓₘ}{ℓ})
empty-inv {x = ()}

module _ ⦃ empty-equiv : ∀{x y} → Equiv{ℓₑ}(empty-morphism{ℓₘ}{ℓ} x y) ⦄ where
  instance
    empty-associativity : Morphism.Associativity{Morphism = empty-morphism} ⦃ empty-equiv ⦄ empty-comp
    empty-associativity = Morphism.intro \{}

  instance
    empty-identityₗ : Morphism.Identityₗ{Morphism = empty-morphism} ⦃ empty-equiv ⦄ empty-comp empty-id
    empty-identityₗ = Morphism.intro \{}

  instance
    empty-identityᵣ : Morphism.Identityᵣ{Morphism = empty-morphism} ⦃ empty-equiv ⦄ empty-comp empty-id
    empty-identityᵣ = Morphism.intro \{}

  empty-identity : Morphism.Identity empty-comp empty-id
  empty-identity = [∧]-intro empty-identityₗ empty-identityᵣ

  instance
    empty-inverterₗ : Polymorphism.Inverterₗ {Morphism = empty-morphism} ⦃ empty-equiv ⦄ empty-comp empty-id empty-inv
    empty-inverterₗ = Polymorphism.intro \{}

  instance
    empty-inverterᵣ : Polymorphism.Inverterᵣ {Morphism = empty-morphism} ⦃ empty-equiv ⦄ empty-comp empty-id empty-inv
    empty-inverterᵣ = Polymorphism.intro \{}

  empty-inverter : Polymorphism.Inverter empty-comp empty-id empty-inv
  empty-inverter = [∧]-intro empty-inverterₗ empty-inverterᵣ

single-morphism : ∀{ℓₘ ℓ} → Unit{ℓ} → Unit{ℓ} → Type{ℓₘ}
single-morphism <> <> = Unit

single-id : Names.Reflexivity(single-morphism{ℓₘ}{ℓ})
single-id = <>

single-comp : Names.SwappedTransitivity(single-morphism{ℓₘ}{ℓ})
single-comp <> <> = <>

single-inv : Names.Symmetry(single-morphism{ℓₘ}{ℓ})
single-inv <> = <>

module _ ⦃ single-equiv : ∀{x y} → Equiv{ℓₑ}(single-morphism{ℓₘ}{ℓ} x y) ⦄ where
  instance
    single-associativity : Morphism.Associativity{Morphism = single-morphism{ℓₘ}{ℓ₁}} ⦃ single-equiv ⦄ (single-comp{ℓ = ℓ₂})
    Morphism.Associativity.proof single-associativity {<>}{<>}{<>}{<>}{<>}{<>}{<>} = Reflexivity.proof(Equiv.reflexivity (single-equiv {<>}{<>}))

  instance
    single-identityₗ : Morphism.Identityₗ{Morphism = single-morphism{ℓₘ}{ℓ₁}} ⦃ single-equiv ⦄ (single-comp{ℓ = ℓ₂}) (single-id{ℓ = ℓ₃})
    Morphism.Identityₗ.proof single-identityₗ {<>}{<>}{<>} = Reflexivity.proof(Equiv.reflexivity (single-equiv {<>}{<>}))

  instance
    single-identityᵣ : Morphism.Identityᵣ{Morphism = single-morphism{ℓₘ}{ℓ₁}} ⦃ single-equiv ⦄ (single-comp{ℓ = ℓ₂}) (single-id{ℓ = ℓ₃})
    Morphism.Identityᵣ.proof single-identityᵣ {<>}{<>}{<>} = Reflexivity.proof(Equiv.reflexivity (single-equiv {<>}{<>}))

  single-identity : Morphism.Identity{Morphism = single-morphism{ℓₘ}{ℓ₁}} (single-comp{ℓ = ℓ₂}) (single-id{ℓ = ℓ₃})
  single-identity{ℓ₁}{ℓ₂}{ℓ₃} = [∧]-intro (single-identityₗ{ℓ₁}{ℓ₂}{ℓ₃}) (single-identityᵣ{ℓ₁}{ℓ₂}{ℓ₃})

  instance
    single-inverterₗ : Polymorphism.Inverterₗ {Morphism = single-morphism{ℓₘ}{ℓ₁}} ⦃ single-equiv ⦄ (single-comp{ℓ = ℓ₂}) (single-id{ℓ = ℓ₃}) (single-inv{ℓ = ℓ₄})
    Polymorphism.Inverterₗ.proof single-inverterₗ {<>}{<>}{<>} = Reflexivity.proof(Equiv.reflexivity (single-equiv {<>}{<>}))

  instance
    single-inverterᵣ : Polymorphism.Inverterᵣ {Morphism = single-morphism{ℓₘ}{ℓ₁}} ⦃ single-equiv ⦄ (single-comp{ℓ = ℓ₂}) (single-id{ℓ = ℓ₃}) (single-inv{ℓ = ℓ₄})
    Polymorphism.Inverterᵣ.proof single-inverterᵣ {<>}{<>}{<>} = Reflexivity.proof(Equiv.reflexivity (single-equiv {<>}{<>}))

  single-inverter : Polymorphism.Inverter {Morphism = single-morphism{ℓₘ}{ℓ₁}} ⦃ single-equiv ⦄ (single-comp{ℓ = ℓ₂}) (single-id{ℓ = ℓ₃}) (single-inv{ℓ = ℓ₄})
  single-inverter{ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄} = [∧]-intro (single-inverterₗ{ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄}) (single-inverterᵣ{ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄})

module _ {Morphism : B → B → Type{ℓₘ}} ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(Morphism x y) ⦄ (f : A → B) where
  module _ {comp : Names.SwappedTransitivity(Morphism)} where
    on₂-associativity : Morphism.Associativity{Morphism = Morphism} ⦃ morphism-equiv ⦄ comp → Morphism.Associativity{Morphism = Morphism on₂ f} comp
    Morphism.Associativity.proof (on₂-associativity p) = Morphism.Associativity.proof p

    module _ {id : Names.Reflexivity(Morphism)} where
      on₂-identityₗ : Morphism.Identityₗ{Morphism = Morphism} ⦃ morphism-equiv ⦄ comp id → Morphism.Identityₗ{Morphism = Morphism on₂ f} comp id
      Morphism.Identityₗ.proof (on₂-identityₗ p) = Morphism.Identityₗ.proof p

      on₂-identityᵣ : Morphism.Identityᵣ{Morphism = Morphism} ⦃ morphism-equiv ⦄ comp id → Morphism.Identityᵣ{Morphism = Morphism on₂ f} comp id
      Morphism.Identityᵣ.proof (on₂-identityᵣ p) = Morphism.Identityᵣ.proof p

      on₂-identity : Morphism.Identity{Morphism = Morphism} ⦃ morphism-equiv ⦄ comp id → Morphism.Identity{Morphism = Morphism on₂ f} comp id
      on₂-identity ([∧]-intro l r) = [∧]-intro (on₂-identityₗ l) (on₂-identityᵣ r)

      module _ {inv : Names.Symmetry(Morphism)} where
        on₂-inverterₗ : Polymorphism.Inverterₗ {Morphism = Morphism} ⦃ morphism-equiv ⦄ comp id inv → Polymorphism.Inverterₗ {Morphism = Morphism on₂ f} comp id inv
        Polymorphism.Inverterₗ.proof (on₂-inverterₗ p) = Polymorphism.Inverterₗ.proof p

        on₂-inverterᵣ : Polymorphism.Inverterᵣ {Morphism = Morphism} ⦃ morphism-equiv ⦄ comp id inv → Polymorphism.Inverterᵣ {Morphism = Morphism on₂ f} comp id inv
        Polymorphism.Inverterᵣ.proof (on₂-inverterᵣ p) = Polymorphism.Inverterᵣ.proof p

        on₂-inverter : Polymorphism.Inverter{Morphism = Morphism} ⦃ morphism-equiv ⦄ comp id inv → Polymorphism.Inverter{Morphism = Morphism on₂ f} comp id inv
        on₂-inverter ([∧]-intro l r) = [∧]-intro (on₂-inverterₗ l) (on₂-inverterᵣ r)
