module Structure.Category.Properties where

import      Functional.Dependent as Fn
open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Sets.Setoid
import      Structure.Category.Names as Names
import      Structure.Operator.Names as Names
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Unit

private variable ℓₒ ℓₘ : Lvl.Level
private variable Obj : Type{ℓₒ}

module Object where
  module _ (Morphism : Obj → Obj → Type{ℓₘ}) where
    open Names.ArrowNotation(Morphism)

    module _ ⦃ morphism-equiv : ∀{x y} → Equiv(x ⟶ y) ⦄ where
      -- An initial object is an object in which there is an unique morphism from it to every object.
      Initial : Obj → Stmt
      Initial(x) = (∀{y} → IsUnit(x ⟶ y))

      -- An terminal object is an object in which there is an unique morphism to it from every object.
      Terminal : Obj → Stmt
      Terminal(y) = (∀{x} → IsUnit(x ⟶ y))

module Morphism where
  module _ {Morphism : Obj → Obj → Type{ℓₘ}} ⦃ equiv-morphism : ∀{x y} → Equiv(Morphism x y) ⦄ where
    open Names.ArrowNotation(Morphism)

    module OperModule (_▫_ : Names.SwappedTransitivity(_⟶_)) where
      record Associativity : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
        constructor intro
        field proof : Names.Morphism.Associativity{Morphism = Morphism}(_▫_)
      associativity = inst-fn Associativity.proof

      module _ {x : Obj} (f : x ⟶ x) where
        record Idempotent : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
          constructor intro
          field proof : Names.Morphism.Idempotent{Morphism = Morphism}(_▫_)(f)
        idempotent = inst-fn Idempotent.proof

      module IdModule (id : Names.Reflexivity(_⟶_)) where
        record Identityₗ : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
          constructor intro
          field proof : Names.Morphism.Identityₗ(_▫_)(\{a} → id{a})
        identityₗ = inst-fn Identityₗ.proof

        record Identityᵣ : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
          constructor intro
          field proof : Names.Morphism.Identityᵣ(_▫_)(\{a} → id{a})
        identityᵣ = inst-fn Identityᵣ.proof

        Identity = Identityₗ ∧ Identityᵣ
        identity-left  = inst-fn{X = Identity}(Identityₗ.proof Fn.∘ [∧]-elimₗ{Q = Identityᵣ})
        identity-right = inst-fn{X = Identity}(Identityᵣ.proof Fn.∘ [∧]-elimᵣ{P = Identityₗ})
        
        module _ {x : Obj} (f : x ⟶ x) where
          record Involution : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
            constructor intro
            field proof : Names.Morphism.Involution{Morphism = Morphism}(_▫_)(id)(f)
          involution = inst-fn Involution.proof

        module _ {x y : Obj} (f : x ⟶ y) where
          module _ (f⁻¹ : y ⟶ x) where
            -- A morphism have a right inverse morphism.
            -- Also called: Split monomorphism, retraction
            record Inverseₗ : Stmt{ℓₘ} where
              constructor intro
              field proof : Names.Morphism.Inverseₗ(_▫_)(\{a} → id{a})(f)(f⁻¹)
            inverseₗ = inst-fn Inverseₗ.proof

            -- A morphism have a right inverse morphism.
            -- Also called: Split epimorphism, section
            record Inverseᵣ : Stmt{ℓₘ} where
              constructor intro
              field proof : Names.Morphism.Inverseᵣ(_▫_)(\{a} → id{a})(f)(f⁻¹)
            inverseᵣ = inst-fn Inverseᵣ.proof

            Inverse = Inverseₗ ∧ Inverseᵣ

          Invertibleₗ = ∃(Inverseₗ)
          Invertibleᵣ = ∃(Inverseᵣ)

          -- A morphism is an isomorphism when it is invertible with respect to the operator.
          -- For the set and functions category, it means that f is bijective.
          Isomorphism : Stmt
          Isomorphism = ∃(Inverse)

          module Isomorphism ⦃ iso : Isomorphism ⦄ where
            instance inverse  = [∃]-proof iso
            instance inverse-left  = [∧]-elimₗ inverse
            instance inverse-right = [∧]-elimᵣ inverse

          inv : ⦃ Isomorphism ⦄ → (y ⟶ x)
          inv ⦃ p ⦄ = [∃]-witness p

        -- Proposition stating that two objects are isomorphic.
        Isomorphic : Obj → Obj → Stmt
        Isomorphic(x)(y) = ∃(Isomorphism{x}{y})

        module _ {x : Obj} (f : ⟲ x) where
          -- A morphism is an automorphism when it is an endomorphism and an isomorphism.
          Automorphism : Stmt
          Automorphism = Isomorphism(f)

        Automorphic : Obj → Stmt
        Automorphic(x) = ∃(Automorphism{x})

      module _ {x y : Obj} (f : x ⟶ y) where
        -- A morphism is an monomorphism when it is left-cancellable ("injective").
        -- ∀{z}{g₁ g₂ : z ⟶ x} → (f ∘ g₁ ≡ f ∘ g₂) → (g₁ ≡ g₂)
        record Monomorphism : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
          constructor intro
          field
            proof : ∀{z} → Names.CancellationOnₗ {T₂ = z ⟶ x} (_▫_) (f)
        cancellationₗ = inst-fn Monomorphism.proof

        -- A morphism is an epimorphism when it is right-cancellable ("surjective").
        -- ∀{z}{g₁ g₂ : y ⟶ z} → (g₁ ∘ f ≡ g₂ ∘ f) → (g₁ ≡ g₂)
        record Epimorphism : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
          constructor intro
          field
            proof : ∀{z} → Names.CancellationOnᵣ {T₁ = y ⟶ z} (_▫_) (f)
        cancellationᵣ = inst-fn Epimorphism.proof

    open OperModule public
    open IdModule   public

module Polymorphism where
  module _ {Morphism : Obj → Obj → Type{ℓₘ}} ⦃ equiv-morphism : ∀{x y} → Equiv(Morphism x y) ⦄ where
    open Names.ArrowNotation(Morphism)

    module OperModule (_▫_ : Names.SwappedTransitivity(_⟶_)) where
      module _ (x y : Obj) (f : ∀{x y} → (x ⟶ y)) where
        record IdempotentOn : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
          constructor intro
          field proof : Names.Polymorphism.IdempotentOn{Morphism = Morphism}(_▫_)(x)(y)(f)
        idempotent-on = inst-fn IdempotentOn.proof

      module IdModule (id : Names.Reflexivity(_⟶_)) where
        module _ (x y : Obj) (f : ∀{x y} → (x ⟶ y)) where
          record InvolutionOn : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
            constructor intro
            field proof : Names.Polymorphism.InvolutionOn{Morphism = Morphism}(_▫_)(id) (x)(y) (f)
          involution-on = inst-fn InvolutionOn.proof

        module _ (f : ∀{x y} → (x ⟶ y)) where
          record Involution : Stmt{Lvl.of(Obj) Lvl.⊔ ℓₘ} where
            constructor intro
            field proof : Names.Polymorphism.Involution{Morphism = Morphism}(_▫_)(id)(f)
          involution = inst-fn Involution.proof

    open OperModule public
    open IdModule   public
