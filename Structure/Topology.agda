module Structure.Topology where

open import Logic
import      Lvl
open import Sets.ExtensionalPredicateSet hiding (_≡_)
open import Sets.Setoid
open import Type

private variable ℓ : Lvl.Level

record TopologicalSpace {ℓ₁ ℓ₂ ℓ₃} (X : Type{ℓ₁}) ⦃ equiv : Equiv(X) ⦄ (𝓣 : PredSet{ℓ₂}(PredSet{ℓ₁ ⊔ ℓ₃}(X))) : Type{Lvl.𝐒 ℓ₁ ⊔ ℓ₂ ⊔ Lvl.𝐒 ℓ₃} where
  field
    contains-empty        : (∅ ∈ 𝓣)
    contains-universe     : (𝐔 ∈ 𝓣)
    intersection-closure  : ∀{A B} → (A ∈ 𝓣) → (B ∈ 𝓣) → ((A ∩ B) ∈ 𝓣)
    indexed-union-closure : ∀{I : Type{ℓ₁ ⊔ ℓ₃}}{Ai : I → PredSet{ℓ₁ ⊔ ℓ₃}(X)} → (∀{i} → (Ai(i) ∈ 𝓣)) → ((⋃ᵢ Ai) ∈ 𝓣)

  open import Data
  open import Data.Proofs
  open import Data.Either as Either using (_‖_)
  open import Data.Either.Equiv
  open import Data.Boolean
  open import Data.Tuple as Tuple using (_⨯_ ; _,_)
  open import Functional
  open import Logic.Propositional
  open import Logic.Predicate
  open import Lvl.Proofs
  import      Relator.Equals.Proofs.Equiv
  open import Structure.Function.Domain
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  module _ where
    open Relator.Equals.Proofs.Equiv(Bool) renaming ([≡]-equiv to bool-equiv)

    union-closure : ∀{A B} → (A ∈ 𝓣) → (B ∈ 𝓣) → ((A ∪ B) ∈ 𝓣)
    union-closure {A}{B} pa pb = substitute₂(_∋_) (reflexivity(_≡_) {x = 𝓣}) (⋃ᵢ-of-bijection ([∃]-intro Lvl.Up.obj) 🝖 ⋃ᵢ-of-boolean) (indexed-union-closure f-proof) where
      f-proof : ∀{i} → ((if i then B else A) ∈ 𝓣)
      f-proof {𝐹} = pa
      f-proof {𝑇} = pb

  Open : PredSet{ℓ₁ ⊔ ℓ₃}(X) → Stmt
  Open(A) = A ∈ 𝓣

  Closed : PredSet{ℓ₁ ⊔ ℓ₃}(X) → Stmt
  Closed(A) = Open(∁ A)

  record Neighborhood (p : X) (N : PredSet{ℓ₁ ⊔ ℓ₃}(X)) : Stmt{Lvl.𝐒(ℓ₁) ⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
    constructor intro
    field
      O : PredSet{ℓ₁ ⊔ ℓ₃}(X)
      ⦃ open-set ⦄       : Open(O)
      ⦃ covers ⦄         : O ⊆ N
      ⦃ contains-point ⦄ : p ∈ O
  
  record Base {I : Type{ℓ₁ ⊔ ℓ₃}} (Bi : I → PredSet{ℓ₁ ⊔ ℓ₃}(X)) : Stmt{Lvl.𝐒(ℓ₁ ⊔ ℓ₃)} where
    constructor intro
    field
      covers-space : (∀{x} → (x ∈ (⋃ᵢ Bi)))
      generator : (x : X) → (i₁ i₂ : I) → ⦃ _ : x ∈ (Bi(i₁) ∩ Bi(i₂)) ⦄ → I
      generator-contains-point : ∀{x : X}{i₁ i₂ : I} ⦃ _ : x ∈ (Bi(i₁) ∩ Bi(i₂)) ⦄ → (x ∈ Bi(generator x i₁ i₂))
      generator-subset : ∀{x : X}{i₁ i₂ : I} ⦃ _ : x ∈ (Bi(i₁) ∩ Bi(i₂)) ⦄ → (Bi(generator x i₁ i₂) ⊆ (Bi(i₁) ∩ Bi(i₂)))
