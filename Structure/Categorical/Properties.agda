module Structure.Categorical.Properties where

open import Data.Tuple using (_⨯_ ; _,_)
import      DependentFunctional as Fn
open import Functional.Instance
import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Setoid
import      Structure.Categorical.Names as Names
import      Structure.Operator.Names as Names
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Properties.Singleton

private variable ℓₒ ℓₘ ℓₑ : Lvl.Level
private variable Obj : Type{ℓₒ}

module Object where
  module _ (Morphism : Obj → Obj → Type{ℓₘ}) where
    open Names.ArrowNotation(Morphism)

    module _ ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(x ⟶ y) ⦄ where
      -- An initial object is an object in which there is an unique morphism from it to every object.
      Initial : Obj → Stmt
      Initial(x) = (∀{y} → IsUnit(x ⟶ y))
      module _ {x} ⦃ initial : Initial(x) ⦄ where
        initialMorphism : ∀(y) → (x ⟶ y)
        initialMorphism y = IsUnit.unit(initial{y})

      -- An terminal object is an object in which there is an unique morphism to it from every object.
      Terminal : Obj → Stmt
      Terminal(y) = (∀{x} → IsUnit(x ⟶ y))
      module _ {y} ⦃ terminal : Terminal(y) ⦄ where
        terminalMorphism : ∀(x) → (x ⟶ y)
        terminalMorphism x = IsUnit.unit(terminal{x})

module Morphism where
  module _ {Morphism : Obj → Obj → Type{ℓₘ}} ⦃ equiv-morphism : ∀{x y} → Equiv{ℓₑ}(Morphism x y) ⦄ where
    open Names.ArrowNotation(Morphism)
    private variable x y z : Obj

    module OperModule (_▫_ : Names.SwappedTransitivity(_⟶_)) where
      record Associativity : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
        constructor intro
        field proof : Names.Morphism.Associativity{Morphism = Morphism}(_▫_)
      associativity = inferArg Associativity.proof

      module _ (f : x ⟶ x) where
        record Idempotent : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
          constructor intro
          field proof : Names.Morphism.Idempotent{Morphism = Morphism}(_▫_)(f)
        idempotent = inferArg Idempotent.proof

      module IdModule (id : Names.Reflexivity(_⟶_)) where
        record Identityₗ : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
          constructor intro
          field proof : Names.Morphism.Identityₗ(_▫_)(\{a} → id{a})
        identityₗ = inferArg Identityₗ.proof

        record Identityᵣ : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
          constructor intro
          field proof : Names.Morphism.Identityᵣ(_▫_)(\{a} → id{a})
        identityᵣ = inferArg Identityᵣ.proof

        Identity = Identityₗ ∧ Identityᵣ
        identity-left  = inferArg{A = Identity}(Identityₗ.proof Fn.∘ [∧]-elimₗ{Q = Identityᵣ})
        identity-right = inferArg{A = Identity}(Identityᵣ.proof Fn.∘ [∧]-elimᵣ{P = Identityₗ})

        module _ (f : x ⟶ x) where
          record Involution : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
            constructor intro
            field proof : Names.Morphism.Involution{Morphism = Morphism}(_▫_)(id)(f)
          involution = inferArg Involution.proof

        module _ (f : x ⟶ y) (f⁻¹ : y ⟶ x) where
          -- A morphism have a right inverse morphism.
          -- Also called: Split epimorphism, section
          record Inverseᵣ : Stmt{ℓₘ Lvl.⊔ ℓₑ} where
            constructor intro
            field proof : Names.Morphism.Inverseᵣ(_▫_)(\{a} → id{a})(f)(f⁻¹)
          inverseᵣ = inferArg Inverseᵣ.proof

        module _ (f : x ⟶ y) where
          Invertibleᵣ = ∃(Inverseᵣ(f))

        -- A morphism have a right inverse morphism.
        -- Also called: Split monomorphism, retraction
        Inverseₗ = \{x}{y} → Fn.swap(Inverseᵣ{x}{y})
        inverseₗ = \{x}{y} → Fn.swap(inverseᵣ{x}{y})
        module Inverseₗ{x}{y}{f}{f⁻¹} inst = Inverseᵣ{x}{y}{f⁻¹}{f} inst

        module _ (f : x ⟶ y) where
          Invertibleₗ = ∃(Inverseₗ(f))

        module _ ((f⁻¹ , f) : x ⟷ y) where
          Inverse = Inverseₗ(f)(f⁻¹) ∧ Inverseᵣ(f)(f⁻¹)
          module Inverse(inverse : Inverse) where
            instance
              left : Inverseₗ(f)(f⁻¹)
              left = [∧]-elimₗ inverse

            instance
              right : Inverseᵣ(f)(f⁻¹)
              right = [∧]-elimᵣ inverse

        -- A morphism is an isomorphism when it is invertible with respect to the operator.
        -- For the set and functions category, this is usually equivalent to f being bijective.
        module _ (f : x ⟶ y) where
          Isomorphism : Stmt
          Isomorphism = ∃(\f⁻¹ → Inverse(f⁻¹ , f))
          module Isomorphism ⦃ iso : Isomorphism ⦄ where
            instance inverse = [∃]-proof iso
            instance inverse-left  = [∧]-elimₗ inverse
            instance inverse-right = [∧]-elimᵣ inverse

          inv : ⦃ Isomorphism ⦄ → (y ⟶ x)
          inv ⦃ p ⦄ = [∃]-witness p

        -- Proposition stating that two objects are isomorphic.
        module _ (x : Obj) (y : Obj) where
          Isomorphic : Stmt
          Isomorphic = ∃{Obj = (x ⟷ y)} Inverse
        module Isomorphic {x : Obj} {y : Obj} where
          module _ (iso : Isomorphic x y) where
            left : x ⟵ y
            left = [∧]-elimₗ ([∃]-witness iso)

            right : x ⟶ y
            right = [∧]-elimᵣ ([∃]-witness iso)

            instance
              inverseLeft : Inverseₗ(right)(left)
              inverseLeft = [∧]-elimₗ ([∃]-proof iso)

            instance
              inverseRight : Inverseᵣ(right)(left)
              inverseRight = [∧]-elimᵣ ([∃]-proof iso)

            instance
              inverse : Inverse([∃]-witness iso)
              inverse = [∃]-proof iso

            instance
              isomorphismLeft : Isomorphism(left)
              isomorphismLeft = [∃]-intro right ⦃ [∧]-intro inverseRight inverseLeft ⦄

            instance
              isomorphismRight : Isomorphism(right)
              isomorphismRight = [∃]-intro left

          intro-by-isomorphism : ∀{f : x ⟶ y} → Isomorphism(f) → Isomorphic x y
          intro-by-isomorphism {f} ([∃]-intro f⁻¹) = [∃]-intro (f⁻¹ , f)

        _⤖_ = Isomorphic

        module _ {x : Obj} (f : ⟲ x) where
          -- A morphism is an automorphism when it is an endomorphism and an isomorphism.
          Automorphism : Stmt
          Automorphism = Isomorphism(f)

        Automorphic : Obj → Stmt
        Automorphic(x) = ∃(Automorphism{x})

      module _ {x y : Obj} (f : x ⟶ y) where
        -- A morphism is an monomorphism when it is left-cancellable ("injective").
        -- ∀{z}{g₁ g₂ : z ⟶ x} → (f ∘ g₁ ≡ f ∘ g₂) → (g₁ ≡ g₂)
        record Monomorphism : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
          constructor intro
          field
            proof : ∀{z} → Names.CancellationOnₗ {T₂ = z ⟶ x} (_▫_) (f)
        cancellationₗ = inferArg Monomorphism.proof

        -- A morphism is an epimorphism when it is right-cancellable ("surjective").
        -- ∀{z}{g₁ g₂ : y ⟶ z} → (g₁ ∘ f ≡ g₂ ∘ f) → (g₁ ≡ g₂)
        record Epimorphism : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
          constructor intro
          field
            proof : ∀{z} → Names.CancellationOnᵣ {T₁ = y ⟶ z} (_▫_) (f)
        cancellationᵣ = inferArg Epimorphism.proof

      -- Proposition stating that two objects are monomorphic.
      Monomorphic : Obj → Obj → Stmt
      Monomorphic(x)(y) = ∃(Monomorphism{x}{y})
      _↣_ = Monomorphic

      -- Proposition stating that two objects are epimorphic.
      Epimorphic : Obj → Obj → Stmt
      Epimorphic(x)(y) = ∃(Epimorphism{x}{y})
      _↠_ = Epimorphic

    open OperModule public
    open IdModule   public

module Polymorphism where
  module _ {Morphism : Obj → Obj → Type{ℓₘ}} ⦃ equiv-morphism : ∀{x y} → Equiv{ℓₑ}(Morphism x y) ⦄ where
    open Names.ArrowNotation(Morphism)

    module OperModule (_▫_ : Names.SwappedTransitivity(_⟶_)) where
      module _ (x y : Obj) (f : ∀{x y} → (x ⟶ y)) where
        record IdempotentOn : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
          constructor intro
          field proof : Names.Polymorphism.IdempotentOn{Morphism = Morphism}(_▫_)(x)(y)(f)
        idempotent-on = inferArg IdempotentOn.proof

      module IdModule (id : Names.Reflexivity(_⟶_)) where
        module _ (x y : Obj) (f : ∀{x y} → (x ⟶ y)) where
          record InvolutionOn : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
            constructor intro
            field proof : Names.Polymorphism.InvolutionOn{Morphism = Morphism}(_▫_)(id) (x)(y) (f)
          involution-on = inferArg InvolutionOn.proof

        module _ (f : ∀{x y} → (x ⟶ y)) where
          record Involution : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
            constructor intro
            field proof : Names.Polymorphism.Involution{Morphism = Morphism}(_▫_)(id)(f)
          involution = inferArg Involution.proof

        module _ (inv : ∀{x y : Obj} → (x ⟶ y) → (y ⟶ x)) where
          -- A morphism have a right inverse morphism.
          -- Also called: Split monomorphism, retraction
          record Inverterₗ : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
            constructor intro
            field proof : ∀{x y : Obj}{f : x ⟶ y} → Names.Morphism.Inverseₗ(_▫_)(\{a} → id{a})(f)(inv f)
            instance
              inverseₗ : ∀{x y : Obj}{f : x ⟶ y} → Morphism.Inverseₗ(_▫_)(\{x} → id{x})(f)(inv f)
              inverseₗ = Morphism.intro proof

          inverterₗ = inferArg Inverterₗ.proof

          -- A morphism have a right inverse morphism.
          -- Also called: Split epimorphism, section
          record Inverterᵣ : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
            constructor intro
            field proof : ∀{x y : Obj}{f : x ⟶ y} → Names.Morphism.Inverseᵣ(_▫_)(\{a} → id{a})(f)(inv f)
            instance
              inverseᵣ : ∀{x y : Obj}{f : x ⟶ y} → Morphism.Inverseᵣ(_▫_)(\{x} → id{x})(f)(inv f)
              inverseᵣ = Morphism.intro proof
          inverterᵣ = inferArg Inverterᵣ.proof

          Inverter = Inverterₗ ∧ Inverterᵣ
          module Inverter(inverter : Inverter) where
            instance
              left : Inverterₗ
              left = [∧]-elimₗ inverter
            open Inverterₗ(left) public

            instance
              right : Inverterᵣ
              right = [∧]-elimᵣ inverter
            open Inverterᵣ(right) public

            module _ {x y : Obj} {f : x ⟶ y} where
              instance
                inverse : Morphism.Inverse(_▫_)(\{x} → id{x})(inv f , f)
                inverse = [∧]-intro inverseₗ inverseᵣ
              open Morphism.Inverse(_▫_)(\{x} → id{x})(inv f , f)(inverse) renaming (left to inverseₗ ; right to inverseᵣ)

            invertibleₗ : ∀{x y : Obj}{f : x ⟶ y} → Morphism.Invertibleₗ(_▫_)(\{x} → id{x})(f)
            invertibleₗ {f = f} = [∃]-intro (inv f) ⦃ inverseₗ ⦄

            invertibleᵣ : ∀{x y : Obj}{f : x ⟶ y} → Morphism.Invertibleᵣ(_▫_)(\{x} → id{x})(f)
            invertibleᵣ {f = f} = [∃]-intro (inv f) ⦃ inverseᵣ ⦄

            isomorphism : ∀{x y : Obj}{f : x ⟶ y} → Morphism.Isomorphism(_▫_)(\{x} → id{x})(f)
            isomorphism {f = f} = [∃]-intro (inv f) ⦃ inverse ⦄

    open OperModule public
    open IdModule   public
