module FormalLanguage.Proofs where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
open import FormalLanguage
open        FormalLanguage.Oper using (_∈?_)
open import Functional
open import Functional
open import Data.List renaming (∅ to [])
open import Lang.Size
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator.Properties
-- open import Structure.Operator.SetAlgebra
open import Structure.Function.Domain

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
  -- Identityₗ.proof([𝁼]-identityₗ) {x} = 

  postulate [𝁼]-identityᵣ : Identityᵣ(_𝁼_)(ε)
  postulate [𝁼]-absorberₗ : Absorberₗ(_𝁼_)(∅)
  postulate [𝁼]-absorberᵣ : Absorberᵣ(_𝁼_)(∅)
--  postulate [*]-fixpoint-[ε] : FixPoint(_*)(ε)
  postulate [*]-on-[∅] : (∅ * ≡ ε)
  postulate [*]-on-[*] : ∀{L} → ((L *)* ≡ L *)
  postulate [𝁼]-commutativity-with-[*] : ∀{L} → ((L *) 𝁼 L ≡ L 𝁼 (L *))
  -- postulate [𝁼]-set-algebra : SetAlgebra -- TODO: Complement is missing

module _ {Σ} where
  private _𝁼_ = Oper._𝁼_ {Σ}
  private _∪_ = Oper._∪_ {Σ}
  private _∩_ = Oper._∩_ {Σ}
  private ε   = Oper.ε {Σ}
  private ∅   = Oper.∅ {Σ}
  private _*   = Oper._* {Σ}
  private ∁_   = Oper.∁_ {Σ}
  private _∈_ = Oper._∈_ {Σ}
  private _∉_ = Oper._∉_ {Σ}

  suffix-lang-containment : ∀{c}{x}{L : Language(Σ)} → (x ∈ Language.suffix-lang(L)(c)) → ((c ⊰ x) ∈ L)
  suffix-lang-containment eq = eq

  [∪]-containment : ∀{x}{A B : Language(Σ)} → (x ∈ (A ∪ B)) ↔ ((x ∈ A)∨(x ∈ B))
  [∪]-containment {x}{A}{B} = [↔]-intro (l{x}{A}{B}) (r{x}{A}{B}) where
    l : ∀{x}{A B} → (x ∈ (A ∪ B)) ← ((x ∈ A)∨(x ∈ B))
    l {[]}    = [↔]-to-[←] IsTrue.[∨]-transfer
    l {c ⊰ w} = l {w}

    r : ∀{x}{A B} → (x ∈ (A ∪ B)) → ((x ∈ A)∨(x ∈ B))
    r {[]}    = [↔]-to-[→] IsTrue.[∨]-transfer
    r {c ⊰ w} = r {w}

  [∩]-containment : ∀{x}{A B : Language(Σ)} → (x ∈ (A ∩ B)) ↔ ((x ∈ A)∧(x ∈ B))
  [∩]-containment {x}{A}{B} = [↔]-intro (l{x}{A}{B}) (r{x}{A}{B}) where
    l : ∀{x}{A B} → (x ∈ (A ∩ B)) ← ((x ∈ A)∧(x ∈ B))
    l {[]}    = [↔]-to-[←] IsTrue.[∧]-transfer
    l {c ⊰ w} = l {w}

    r : ∀{x}{A B} → (x ∈ (A ∩ B)) → ((x ∈ A)∧(x ∈ B))
    r {[]} = [↔]-to-[→] IsTrue.[∧]-transfer
    r {c ⊰ w} = r {w}

  [∁]-containment : ∀{x}{A : Language(Σ)} → (x ∈ (∁ A)) ↔ (x ∉ A)
  [∁]-containment {x}{A} = [↔]-intro (l{x}{A}) (r{x}{A}) where
    l : ∀{x}{A} → (x ∈ (∁ A)) ← (x ∉ A)
    l {[]}    = IsTrue.[¬]-intro
    l {c ⊰ w} = l {w}

    r : ∀{x}{A} → (x ∈ (∁ A)) → (x ∉ A)
    r {[]} = IsTrue.[¬]-elim
    r {c ⊰ w} = r {w}

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
    l {[]} [≡]-intro = [⊤]-intro

    r : ∀{x} → (x ∈ ε) → (x ≡ [])
    r {[]}    _       = [≡]-intro
    r {a ⊰ l} (proof) = [⊥]-elim (([↔]-to-[→] ([∅]-containment {l})) (proof))

  -- [𝁼]-containment : ∀{x y}{A B : Language(Σ)} → ((x ++ y) ∈ (A 𝁼 B)) ← (x ∈ A)∧(y ∈ B)
  -- [𝁼]-containment : ∀{x}{A B : Language(Σ)} → (x ∈ (A 𝁼 B)) ↔ ∃(a ↦ ∃ b ↦ (a ++ b ≡ x)∧(a ∈ A)∧(b ∈ B))
  -- [𝁼]-containment {x} = [↔]-intro (l{x}) (r{x}) where

  -- TODO: This should probably be the definition of equality for languages because of no function extentionality
  -- Language-[≡]-intro : ∀{A B : Language(Σ)} → (∀{w} → (w ∈? A) ≡ (w ∈? B)) ↔ (A ≡ B)
  -- Language-[≡]-intro = [↔]-intro Language-[≡]-introₗ Language-[≡]-introᵣ where
  --   Language-[≡]-introₗ : ∀{A B} → (∀{w} → (w ∈? A) ≡ (w ∈? B)) ← (A ≡ B)
  --   Language-[≡]-introₗ [≡]-intro = [≡]-intro

  --   Language-[≡]-introᵣ : ∀{A B} → (∀{w} → (w ∈? A) ≡ (w ∈? B)) → (A ≡ B)
  --   Language-[≡]-introᵣ {Lang 𝑇 _}{Lang 𝑇 _} f with f{[]}
  --   Language-[≡]-introᵣ {Lang 𝑇 _}{Lang 𝑇 _} f | [≡]-intro = [≡]-intro
    --   f{∅}     = [≡]-intro
    --   f{c ⊰ w} = [≡]-intro

  -- postulate Language-[≡]-intro : {A B : Language(Σ)} → (∀{w} → (w ∈ A) ↔ (w ∈ B)) ↔ (A ≡ B)

-- TODO: Set properties
-- TODO: Connection with logic (from sets) in relations
