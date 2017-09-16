module FormalLanguage.Properties where

open import Agda.Builtin.Size
open import Boolean
import      Lvl
open import FormalLanguage
open        FormalLanguage.Oper using (_is-in_)
open import Functional
open import List renaming (∅ to [])
open import Logic.Propositional{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Properties{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.SetAlgebra{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Function.Domain{Lvl.𝟎}

-- TODO: Prove all these

module _ {Σ}{s} where
  private _𝁼_ = Oper._𝁼_ {Σ}{s}
  private _∪_ = Oper._∪_ {Σ}{s}
  private _∩_ = Oper._∩_ {Σ}{s}
  private ε   = Oper.ε {Σ}{s}
  private ∅   = Oper.∅ {Σ}{s}
  private _*   = Oper._* {Σ}{s}
  private ∁_   = Oper.∁_ {Σ}{s}

  postulate [𝁼]-associativity : Associativity(_𝁼_)
  postulate [𝁼]-distributivityₗ : Distributivityₗ(_𝁼_)(_∪_)
  postulate [𝁼]-distributivityᵣ : Distributivityᵣ(_𝁼_)(_∪_)
  postulate [𝁼]-identityₗ : Identityₗ(_𝁼_)(ε)
  postulate [𝁼]-identityᵣ : Identityᵣ(_𝁼_)(ε)
  postulate [𝁼]-absorberₗ : Absorberₗ(_𝁼_)(∅)
  postulate [𝁼]-absorberᵣ : Absorberᵣ(_𝁼_)(∅)
  postulate [*]-fixpoint-[ε] : FixPoint(_*)(ε)
  postulate [*]-on-[∅] : (∅ * ≡ ε)
  postulate [*]-on-[*] : ∀{L} → ((L *)* ≡ L *)
  postulate [𝁼]-commutativity-with-[*] : ∀{L} → ((L *) 𝁼 L ≡ L 𝁼 (L *))
  -- postulate [𝁼]-set-algebra : SetAlgebra -- TODO: Complement is missing

module _ {Σ} where
  private _𝁼_ = Oper._𝁼_ {Σ}{ω}
  private _∪_ = Oper._∪_ {Σ}{ω}
  private _∩_ = Oper._∩_ {Σ}{ω}
  private ε   = Oper.ε {Σ}{ω}
  private ∅   = Oper.∅ {Σ}{ω}
  private _*   = Oper._* {Σ}{ω}
  private ∁_   = Oper.∁_ {Σ}{ω}
  private _∈_ = Oper._∈_ {Σ}
  private _∉_ = Oper._∉_ {Σ}

  postulate [∪]-containment : ∀{x}{A B : Language(Σ){ω}} → (x ∈ (A ∪ B)) ↔ ((x ∈ A)∨(x ∈ B))
  postulate [∩]-containment : ∀{x}{A B : Language(Σ){ω}} → (x ∈ (A ∩ B)) ↔ ((x ∈ A)∧(x ∈ B))
  postulate [∁]-containment : ∀{x}{A : Language(Σ){ω}} → (x ∈ (∁ A)) ↔ (x ∉ A)
  postulate [∅]-containment : ∀{x}{A : Language(Σ){ω}} → (x ∈ ∅) ↔ ⊥
  postulate [ε]-containment : ∀{x}{A : Language(Σ){ω}} → (x ∈ ε) ↔ (x ≡ [])

  -- Language-[≡]-intro : ∀{A B : Language(Σ){ω}} → (∀{w} → (w is-in A) ≡ (w is-in B)) ↔ (A ≡ B)
  -- Language-[≡]-intro = [↔]-intro Language-[≡]-introₗ Language-[≡]-introᵣ where
  --   Language-[≡]-introₗ : ∀{A B} → (∀{w} → (w is-in A) ≡ (w is-in B)) ← (A ≡ B)
  --   Language-[≡]-introₗ [≡]-intro = [≡]-intro

  --   Language-[≡]-introᵣ : ∀{A B} → (∀{w} → (w is-in A) ≡ (w is-in B)) → (A ≡ B)
  --   Language-[≡]-introᵣ {Lang 𝑇 _}{Lang 𝑇 _} f with f{[]}
  --   Language-[≡]-introᵣ {Lang 𝑇 _}{Lang 𝑇 _} f | [≡]-intro = [≡]-intro
    --   f{∅}     = [≡]-intro
    --   f{c ⊰ w} = [≡]-intro

  -- postulate Language-[≡]-intro : {A B : Language(Σ){ω}} → (∀{w} → (w ∈ A) ↔ (w ∈ B)) ↔ (A ≡ B)

-- TODO: Set properties
-- TODO: Connection with logic (from sets) in relations
