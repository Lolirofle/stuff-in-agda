module FormalLanguage.Properties where

open import Agda.Builtin.Size
import      Lvl
open import Boolean
open import Boolean.Theorems{Lvl.𝟎}
open import FormalLanguage
open        FormalLanguage.Oper using (_is-in_)
open import Functional
open import List renaming (∅ to [])
open import Logic.Propositional{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
open import Relator.Equals.Theorems{Lvl.𝟎}{Lvl.𝟎}
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

  postulate suffix-lang-containment : ∀{x}{c}{L : Language(Σ){ω}} → (x ∈ Language.suffix-lang(L)(c)) → ((c ⊰ x) ∈ L)

  [∪]-containment : ∀{x}{A B : Language(Σ){ω}} → (x ∈ (A ∪ B)) ↔ ((x ∈ A)∨(x ∈ B))
  [∪]-containment {x}{A}{B} = [↔]-intro (l{x}) (r{x}) where
    postulate l : ∀{x} → (x ∈ (A ∪ B)) ← ((x ∈ A)∨(x ∈ B))
    -- l {[]} ([∨]-introₗ [≡]-intro) = [≡]-intro
    -- l {[]} ([∨]-introᵣ [≡]-intro) = [≡]-intro

    postulate r : ∀{x} → (x ∈ (A ∪ B)) → ((x ∈ A)∨(x ∈ B))
    -- r ([≡]-intro) = [∨]-introₗ [≡]-intro

  [∩]-containment : ∀{x}{A B : Language(Σ){ω}} → (x ∈ (A ∩ B)) ↔ ((x ∈ A)∧(x ∈ B))
  [∩]-containment {x}{A}{B} = [↔]-intro (l{x}) (r{x}) where
    postulate l : ∀{x} → (x ∈ (A ∩ B)) ← ((x ∈ A)∧(x ∈ B))
    -- l {[]}    ([∧]-intro xa xb) = [∧]-intro-[𝑇] xa xb
    -- l {a ⊰ L} ([∧]-intro xa xb) = [∧]-intro-[𝑇] (l {a ⊰ L} xa) (l {a ⊰ L} xb)?

    postulate r : ∀{x} → (x ∈ (A ∩ B)) → ((x ∈ A)∧(x ∈ B))

  postulate [∁]-containment : ∀{x}{A : Language(Σ){ω}} → (x ∈ (∁ A)) ↔ (x ∉ A)

  [∅]-containment : ∀{x} → (x ∈ ∅) ↔ ⊥
  [∅]-containment {x} = [↔]-intro (l{x}) (r{x}) where
    l : ∀{x} → (x ∈ ∅) ← ⊥
    l()

    r : ∀{x} → (x ∈ ∅) → ⊥
    r {[]}    ()
    r {a ⊰ l} (proof) = r {l} (proof)

  [ε]-containment : ∀{x} → (x ∈ ε) ↔ (x ≡ [])
  [ε]-containment {x} = [↔]-intro (l{x}) (r{x}) where
    l : ∀{x} → (x ∈ ε) ← (x ≡ [])
    l [≡]-intro = [≡]-intro

    r : ∀{x} → (x ∈ ε) → (x ≡ [])
    r {[]}    [≡]-intro = [≡]-intro
    r {a ⊰ l} (proof) = [⊥]-elim (([↔]-elimᵣ ([∅]-containment {l})) (proof))

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
