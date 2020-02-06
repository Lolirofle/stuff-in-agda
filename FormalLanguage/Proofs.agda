module FormalLanguage.Proofs where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
open import FormalLanguage
open        FormalLanguage.Oper using (_∈?_)
open import FormalLanguage.Equals
open import Data.List renaming (∅ to [])
open import Lang.Size
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
open import Sets.Setoid
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
-- open import Structure.Operator.SetAlgebra
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Type

-- TODO: Prove all these
-- TODO: http://www.cse.chalmers.se/~abela/jlamp17.pdf

module _ {Σ} where
  open Oper{Σ}

  instance
    [∪]-associativity : Associativity(_∪_)
    Associativity.proof([∪]-associativity) = [∪]-associativity-raw where
      [∪]-associativity-raw : ∀{A B C} → (((A ∪ B) ∪ C) ≅ (A ∪ (B ∪ C))) -- Names.Associativity(_∪_)
      _≅_.accepts-ε   ([∪]-associativity-raw {A})     = associativity(_||_) {Language.accepts-ε A}
      _≅_.suffix-lang ([∪]-associativity-raw {A}) {c} = [∪]-associativity-raw {Language.suffix-lang A c}

  instance
    [∪]-commutativity : Commutativity(_∪_)
    Commutativity.proof([∪]-commutativity) = [∪]-commutativity-raw where
      [∪]-commutativity-raw : ∀{A B} → ((A ∪ B) ≅ (B ∪ A))
      _≅_.accepts-ε   ([∪]-commutativity-raw {A})     = commutativity(_||_) {Language.accepts-ε A}
      _≅_.suffix-lang ([∪]-commutativity-raw {A}) {c} = [∪]-commutativity-raw {Language.suffix-lang A c}

  instance
    [∪]-identityₗ : Identityₗ(_∪_)(∅)
    Identityₗ.proof([∪]-identityₗ) = [∪]-identityₗ-raw where
      [∪]-identityₗ-raw : ∀{A} → ((∅ ∪ A) ≅ A)
      _≅_.accepts-ε   ([∪]-identityₗ-raw {A})     = [≡]-intro
      _≅_.suffix-lang ([∪]-identityₗ-raw {A}) {c} = [∪]-identityₗ-raw {Language.suffix-lang A c}

  instance
    [∪]-identityᵣ : Identityᵣ(_∪_)(∅)
    Identityᵣ.proof([∪]-identityᵣ) = [∪]-identityᵣ-raw where
      [∪]-identityᵣ-raw : ∀{A} → ((A ∪ ∅) ≅ A)
      _≅_.accepts-ε   ([∪]-identityᵣ-raw {A})     = [≡]-intro
      _≅_.suffix-lang ([∪]-identityᵣ-raw {A}) {c} = [∪]-identityᵣ-raw {Language.suffix-lang A c}

  instance
    [∪]-identity : Identity(_∪_)(∅)
    [∪]-identity = record{}

  instance
    [∪]-absorberₗ : Absorberₗ(_∪_)(Σ*)
    Absorberₗ.proof([∪]-absorberₗ) = [∪]-absorberₗ-raw where
      [∪]-absorberₗ-raw : ∀{A} → ((Σ* ∪ A) ≅ Σ*)
      _≅_.accepts-ε   ([∪]-absorberₗ-raw {A})     = [≡]-intro
      _≅_.suffix-lang ([∪]-absorberₗ-raw {A}) {c} = [∪]-absorberₗ-raw {Language.suffix-lang A c}

  instance
    [∪]-absorberᵣ : Absorberᵣ(_∪_)(Σ*)
    Absorberᵣ.proof([∪]-absorberᵣ) = [∪]-absorberᵣ-raw where
      [∪]-absorberᵣ-raw : ∀{A} → ((A ∪ Σ*) ≅ Σ*)
      _≅_.accepts-ε   ([∪]-absorberᵣ-raw {A})     = [≡]-intro
      _≅_.suffix-lang ([∪]-absorberᵣ-raw {A}) {c} = [∪]-absorberᵣ-raw {Language.suffix-lang A c}

  instance
    [∪]-absorber : Absorber(_∪_)(Σ*)
    [∪]-absorber = record{}

  instance
    [∪]-binary-operator : BinaryOperator(_∪_)
    BinaryOperator.congruence([∪]-binary-operator) = [∪]-binary-operator-raw where
      [∪]-binary-operator-raw : ∀{A₁ A₂} → (A₁ ≅ A₂) → ∀{B₁ B₂} → (B₁ ≅ B₂) → ((A₁ ∪ B₁) ≅ (A₂ ∪ B₂))
      _≅_.accepts-ε   ([∪]-binary-operator-raw aeq beq) = [≡]-with-op(_||_) (_≅_.accepts-ε aeq) (_≅_.accepts-ε beq)
      _≅_.suffix-lang ([∪]-binary-operator-raw aeq beq) = [∪]-binary-operator-raw (_≅_.suffix-lang aeq) (_≅_.suffix-lang beq)

  instance
    [∪]-monoid : Monoid(_∪_)
    [∪]-monoid = record{identity-existence = [∃]-intro(∅) ⦃ [∪]-identity ⦄}

  instance
    [∩]-associativity : Associativity(_∩_)
    Associativity.proof([∩]-associativity) = [∩]-associativity-raw where
      [∩]-associativity-raw : ∀{A B C} → (((A ∩ B) ∩ C) ≅ (A ∩ (B ∩ C)))
      _≅_.accepts-ε   ([∩]-associativity-raw {A})     = associativity(_&&_) {Language.accepts-ε A}
      _≅_.suffix-lang ([∩]-associativity-raw {A}) {c} = [∩]-associativity-raw {Language.suffix-lang A c}

  instance
    [∩]-commutativity : Commutativity(_∩_)
    Commutativity.proof([∩]-commutativity) = [∩]-commutativity-raw where
      [∩]-commutativity-raw : ∀{A B} → ((A ∩ B) ≅ (B ∩ A))
      _≅_.accepts-ε   ([∩]-commutativity-raw {A})     = commutativity(_&&_) {Language.accepts-ε A}
      _≅_.suffix-lang ([∩]-commutativity-raw {A}) {c} = [∩]-commutativity-raw {Language.suffix-lang A c}

  instance
    [∩]-identityₗ : Identityₗ(_∩_)(Σ*)
    Identityₗ.proof([∩]-identityₗ) = [∩]-identityₗ-raw where
      [∩]-identityₗ-raw : ∀{A} → ((Σ* ∩ A) ≅ A)
      _≅_.accepts-ε   ([∩]-identityₗ-raw {A})     = [≡]-intro
      _≅_.suffix-lang ([∩]-identityₗ-raw {A}) {c} = [∩]-identityₗ-raw {Language.suffix-lang A c}

  instance
    [∩]-identityᵣ : Identityᵣ(_∩_)(Σ*)
    Identityᵣ.proof([∩]-identityᵣ) = [∩]-identityᵣ-raw where
      [∩]-identityᵣ-raw : ∀{A} → ((A ∩ Σ*) ≅ A)
      _≅_.accepts-ε   ([∩]-identityᵣ-raw {A})     = [≡]-intro
      _≅_.suffix-lang ([∩]-identityᵣ-raw {A}) {c} = [∩]-identityᵣ-raw {Language.suffix-lang A c}

  instance
    [∩]-identity : Identity(_∩_)(Σ*)
    [∩]-identity = record{}

  instance
    [∩]-absorberₗ : Absorberₗ(_∩_)(∅)
    Absorberₗ.proof([∩]-absorberₗ) = [∩]-absorberₗ-raw where
      [∩]-absorberₗ-raw : ∀{A} → ((∅ ∩ A) ≅ ∅)
      _≅_.accepts-ε   ([∩]-absorberₗ-raw {A})     = [≡]-intro
      _≅_.suffix-lang ([∩]-absorberₗ-raw {A}) {c} = [∩]-absorberₗ-raw {Language.suffix-lang A c}

  instance
    [∩]-absorberᵣ : Absorberᵣ(_∩_)(∅)
    Absorberᵣ.proof([∩]-absorberᵣ) = [∩]-absorberᵣ-raw where
      [∩]-absorberᵣ-raw : ∀{A} → ((A ∩ ∅) ≅ ∅)
      _≅_.accepts-ε   ([∩]-absorberᵣ-raw {A})     = [≡]-intro
      _≅_.suffix-lang ([∩]-absorberᵣ-raw {A}) {c} = [∩]-absorberᵣ-raw {Language.suffix-lang A c}

  instance
    [∩]-absorber : Absorber(_∩_)(∅)
    [∩]-absorber = record{}

  instance
    [∩]-binary-operator : BinaryOperator(_∩_)
    BinaryOperator.congruence([∩]-binary-operator) = [∩]-binary-operator-raw where
      [∩]-binary-operator-raw : ∀{A₁ A₂} → (A₁ ≅ A₂) → ∀{B₁ B₂} → (B₁ ≅ B₂) → ((A₁ ∩ B₁) ≅ (A₂ ∩ B₂))
      _≅_.accepts-ε   ([∩]-binary-operator-raw aeq beq) = [≡]-with-op(_&&_) (_≅_.accepts-ε aeq) (_≅_.accepts-ε beq)
      _≅_.suffix-lang ([∩]-binary-operator-raw aeq beq) = [∩]-binary-operator-raw (_≅_.suffix-lang aeq) (_≅_.suffix-lang beq)

  instance
    [∩]-monoid : Monoid(_∩_)
    [∩]-monoid = record{identity-existence = [∃]-intro(Σ*) ⦃ [∩]-identity ⦄}

  instance
    [∪][∩]-distributivityₗ : Distributivityₗ(_∪_)(_∩_)
    Distributivityₗ.proof([∪][∩]-distributivityₗ) = [∪][∩]-distributivityₗ-raw where
      [∪][∩]-distributivityₗ-raw : ∀{A B C} → (A ∪ (B ∩ C)) ≅ ((A ∪ B) ∩ (A ∪ C))
      _≅_.accepts-ε   ([∪][∩]-distributivityₗ-raw {A})     = distributivityₗ(_||_)(_&&_) {Language.accepts-ε A}
      _≅_.suffix-lang ([∪][∩]-distributivityₗ-raw {A}) {c} = [∪][∩]-distributivityₗ-raw {Language.suffix-lang A c}

  instance
    [∩][∪]-distributivityₗ : Distributivityₗ(_∩_)(_∪_)
    Distributivityₗ.proof([∩][∪]-distributivityₗ) = [∩][∪]-distributivityₗ-raw where
      [∩][∪]-distributivityₗ-raw : ∀{A B C} → (A ∩ (B ∪ C)) ≅ ((A ∩ B) ∪ (A ∩ C))
      _≅_.accepts-ε   ([∩][∪]-distributivityₗ-raw {A})     = distributivityₗ(_&&_)(_||_) {Language.accepts-ε A}
      _≅_.suffix-lang ([∩][∪]-distributivityₗ-raw {A}) {c} = [∩][∪]-distributivityₗ-raw {Language.suffix-lang A c}

  {- TODO: Is it possible to describe concatenation using an algebraic property? Maybe something about that it behaves like (_⨯_) (combining every element with each other in some way)?
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
  -}

module _ {Σ} where
  open Oper{Σ}

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

  suffix-head-step : ∀{A : Language(Σ)}{a}{l} → ((a ⊰ l) ∈ A) → (l ∈ Language.suffix-lang(A)(a))
  suffix-head-step p = p

  Language-list-suffix : Language(Σ) → List(Σ) → Language(Σ)
  Language-list-suffix A []      = A
  Language-list-suffix A (x ⊰ l) = Language.suffix-lang(A)(x)

  suffix-concat-step : ∀{A : Language(Σ)}{l₁ l₂} → ((l₁ ++ l₂) ∈ A) → (l₂ ∈ Language-list-suffix(A)(l₁))
  suffix-concat-step {A}{[]}         p = p
  suffix-concat-step {A}{x ⊰ l₁}{l₂} p = {!!}

  [𝁼]-containmentₗ : ∀{x y}{A B : Language(Σ)} → (x ∈ A) → (y ∈ B) → ((x ++ y) ∈ (A 𝁼 B))
  -- [𝁼]-containmentₗ {x} {y} {A} {B} xa xb with Language.accepts-ε(A) | y Oper.∈? B
  [𝁼]-containmentₗ {LongOper.empty} {LongOper.empty} {A} {B} xa xb with Language.accepts-ε(A) | Language.accepts-ε(B)
  [𝁼]-containmentₗ {LongOper.empty} {LongOper.empty} {A} {B} xa xb | 𝑇 | 𝑇 = [⊤]-intro
  [𝁼]-containmentₗ {LongOper.empty} {LongOper.prepend x y} {A} {B} xa xb = {![⊤]-intro!} where
    test : ∀{A B : Language(Σ)}{a} → ([] ∈ A) → (a ∈ B) → (a ∈ (A 𝁼 B))
    test {A}{B}{LongOper.empty} p q with Language.accepts-ε(A) | Language.accepts-ε(B)
    test {A}{B}{LongOper.empty} p q | 𝑇 | 𝑇 = [⊤]-intro
    test {A}{B}{LongOper.prepend x a} p q = {!test {A}{B}{a} p !}
    -- test {LongOper.prepend x a} p q with test {a} p (Language.suffix-lang q)
    -- ... | test = ?
    
  [𝁼]-containmentₗ {LongOper.prepend x x₁} {LongOper.empty} {A} {B} xa xb = {!!}
  [𝁼]-containmentₗ {LongOper.prepend x x₁} {LongOper.prepend x₂ y} {A} {B} xa xb = {!!}

  -- [𝁼]-containment : ∀{x}{A B : Language(Σ)} → (x ∈ (A 𝁼 B)) ↔ ∃(a ↦ ∃ b ↦ (a ++ b ≡ x)∧(a ∈ A)∧(b ∈ B))
  -- [𝁼]-containment {x} = [↔]-intro (l{x}) (r{x}) where

  -- TODO: This coult be the definition of equality for languages because of no function extentionality, but maybe the one in Equals is easier to use
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
