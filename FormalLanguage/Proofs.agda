{-# OPTIONS --sized-types #-}

module FormalLanguage.Proofs {ℓ} where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Proofs
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
import      Data.Tuple as Tuple
open import FormalLanguage
open import FormalLanguage.Equals
open import Functional using (id)
open import Sized.Data.List renaming (∅ to [])
open import Lang.Size
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
import      Function.Names as Names
open import Structure.Setoid
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
-- open import Structure.Operator.SetAlgebra
open import Structure.Operator
open import Structure.Function.Domain
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

-- TODO: Prove all these
-- TODO: http://www.cse.chalmers.se/~abela/jlamp17.pdf

private variable s s₁ s₂ s₃ : Size

{-
module _ {Σ : Alphabet{ℓ}} where
  open Oper{ℓ}{Σ}
  open Language renaming (accepts-ε to accepts ; suffix-lang to suffix)

  instance
    [∪]-associativity : Associativity ⦃ [≅]-equiv {s = s} ⦄ (_∪_)
    Associativity.proof([∪]-associativity {s = s}) = [∪]-associativity-raw {s = s} where
      [∪]-associativity-raw : ∀{s} → Names.Associativity ⦃ [≅]-equiv {s = s} ⦄ (_∪_)
      _≅[_]≅_.accepts-ε   ([∪]-associativity-raw {x = A})     = associativity(_||_) {Language.accepts-ε A}
      _≅[_]≅_.suffix-lang ([∪]-associativity-raw {x = A}) {c} = [∪]-associativity-raw {x = Language.suffix-lang A c}

  instance
    [∪]-commutativity : Commutativity ⦃ [≅]-equiv {s = s} ⦄ (_∪_)
    Commutativity.proof([∪]-commutativity {s = s}) = [∪]-commutativity-raw {s = s} where
      [∪]-commutativity-raw : ∀{s} → Names.Commutativity ⦃ [≅]-equiv {s = s} ⦄ (_∪_)
      _≅[_]≅_.accepts-ε   ([∪]-commutativity-raw {x = A})     = commutativity(_||_) {Language.accepts-ε A}
      _≅[_]≅_.suffix-lang ([∪]-commutativity-raw {x = A}) {c} = [∪]-commutativity-raw {x = Language.suffix-lang A c}

  instance
    [∪]-identityₗ : Identityₗ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(∅)
    Identityₗ.proof([∪]-identityₗ {s = s}) = [∪]-identityₗ-raw {s = s} where
      [∪]-identityₗ-raw : ∀{s} → Names.Identityₗ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(∅)
      _≅[_]≅_.accepts-ε   ([∪]-identityₗ-raw {x = A})     = [≡]-intro
      _≅[_]≅_.suffix-lang ([∪]-identityₗ-raw {x = A}) {c} = [∪]-identityₗ-raw {x = Language.suffix-lang A c}

  instance
    [∪]-identityᵣ : Identityᵣ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(∅)
    Identityᵣ.proof([∪]-identityᵣ {s = s}) = [∪]-identityᵣ-raw {s = s} where
      [∪]-identityᵣ-raw : ∀{s} → Names.Identityᵣ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(∅)
      _≅[_]≅_.accepts-ε   ([∪]-identityᵣ-raw {x = A})     = [≡]-intro
      _≅[_]≅_.suffix-lang ([∪]-identityᵣ-raw {x = A}) {c} = [∪]-identityᵣ-raw {x = Language.suffix-lang A c}

  instance
    [∪]-identity : Identity ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(∅)
    [∪]-identity = intro

  instance
    [∪]-absorberₗ : Absorberₗ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(𝐔)
    Absorberₗ.proof([∪]-absorberₗ {s = s}) = [∪]-absorberₗ-raw {s = s} where
      [∪]-absorberₗ-raw : ∀{s} → Names.Absorberₗ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(𝐔)
      _≅[_]≅_.accepts-ε   ([∪]-absorberₗ-raw {x = A})     = [≡]-intro
      _≅[_]≅_.suffix-lang ([∪]-absorberₗ-raw {x = A}) {c} = [∪]-absorberₗ-raw {x = Language.suffix-lang A c}

  instance
    [∪]-absorberᵣ : Absorberᵣ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(𝐔)
    Absorberᵣ.proof([∪]-absorberᵣ {s = s}) = [∪]-absorberᵣ-raw {s = s} where
      [∪]-absorberᵣ-raw : ∀{s} → Names.Absorberᵣ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(𝐔)
      _≅[_]≅_.accepts-ε   ([∪]-absorberᵣ-raw {x = A})     = [≡]-intro
      _≅[_]≅_.suffix-lang ([∪]-absorberᵣ-raw {x = A}) {c} = [∪]-absorberᵣ-raw {x = Language.suffix-lang A c}

  instance
    [∪]-absorber : Absorber ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(𝐔)
    [∪]-absorber = intro

  instance
    [∪]-binaryOperator : BinaryOperator ⦃ [≅]-equiv {s = s} ⦄ ⦃ [≅]-equiv {s = s} ⦄ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)
    BinaryOperator.congruence([∪]-binaryOperator {s = s}) = [∪]-binaryOperator-raw {s = s} where
      [∪]-binaryOperator-raw : ∀{s} → Names.Congruence₂ ⦃ [≅]-equiv {s = s} ⦄ ⦃ [≅]-equiv {s = s} ⦄ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)
      _≅[_]≅_.accepts-ε   ([∪]-binaryOperator-raw aeq beq) = [≡]-with-op(_||_) (_≅[_]≅_.accepts-ε aeq) (_≅[_]≅_.accepts-ε beq)
      _≅[_]≅_.suffix-lang ([∪]-binaryOperator-raw aeq beq) = [∪]-binaryOperator-raw (_≅[_]≅_.suffix-lang aeq) (_≅[_]≅_.suffix-lang beq)

  instance
    [∪]-monoid : Monoid ⦃ [≅]-equiv {s = s} ⦄ (_∪_)
    Monoid.identity-existence [∪]-monoid = [∃]-intro(∅)

  instance
    [∩]-associativity : Associativity ⦃ [≅]-equiv {s = s} ⦄ (_∩_)
    Associativity.proof([∩]-associativity {s = s}) = [∩]-associativity-raw {s = s} where
      [∩]-associativity-raw : ∀{s} → Names.Associativity ⦃ [≅]-equiv {s = s} ⦄ (_∩_)
      _≅[_]≅_.accepts-ε   ([∩]-associativity-raw {x = A})     = associativity(_&&_) {Language.accepts-ε A}
      _≅[_]≅_.suffix-lang ([∩]-associativity-raw {x = A}) {c} = [∩]-associativity-raw {x = Language.suffix-lang A c}

  instance
    [∩]-commutativity : Commutativity ⦃ [≅]-equiv {s = s} ⦄ (_∩_)
    Commutativity.proof([∩]-commutativity {s = s}) = [∩]-commutativity-raw {s = s} where
      [∩]-commutativity-raw : ∀{s} → Names.Commutativity ⦃ [≅]-equiv {s = s} ⦄ (_∩_)
      _≅[_]≅_.accepts-ε   ([∩]-commutativity-raw {x = A})     = commutativity(_&&_) {Language.accepts-ε A}
      _≅[_]≅_.suffix-lang ([∩]-commutativity-raw {x = A}) {c} = [∩]-commutativity-raw {x = Language.suffix-lang A c}

  instance
    [∩]-identityₗ : Identityₗ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(𝐔)
    Identityₗ.proof([∩]-identityₗ {s = s}) = [∩]-identityₗ-raw {s = s} where
      [∩]-identityₗ-raw : ∀{s} → Names.Identityₗ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(𝐔)
      _≅[_]≅_.accepts-ε   ([∩]-identityₗ-raw {x = A})     = [≡]-intro
      _≅[_]≅_.suffix-lang ([∩]-identityₗ-raw {x = A}) {c} = [∩]-identityₗ-raw {x = Language.suffix-lang A c}

  instance
    [∩]-identityᵣ : Identityᵣ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(𝐔)
    Identityᵣ.proof([∩]-identityᵣ {s = s}) = [∩]-identityᵣ-raw {s = s} where
      [∩]-identityᵣ-raw : ∀{s} → Names.Identityᵣ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(𝐔)
      _≅[_]≅_.accepts-ε   ([∩]-identityᵣ-raw {x = A})     = [≡]-intro
      _≅[_]≅_.suffix-lang ([∩]-identityᵣ-raw {x = A}) {c} = [∩]-identityᵣ-raw {x = Language.suffix-lang A c}

  instance
    [∩]-identity : Identity ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(𝐔)
    [∩]-identity = intro

  instance
    [∩]-absorberₗ : Absorberₗ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(∅)
    Absorberₗ.proof([∩]-absorberₗ {s = s}) = [∩]-absorberₗ-raw {s = s} where
      [∩]-absorberₗ-raw : ∀{s} → Names.Absorberₗ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(∅)
      _≅[_]≅_.accepts-ε   ([∩]-absorberₗ-raw {x = A})     = [≡]-intro
      _≅[_]≅_.suffix-lang ([∩]-absorberₗ-raw {x = A}) {c} = [∩]-absorberₗ-raw {x = Language.suffix-lang A c}

  instance
    [∩]-absorberᵣ : Absorberᵣ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(∅)
    Absorberᵣ.proof([∩]-absorberᵣ {s = s}) = [∩]-absorberᵣ-raw {s = s} where
      [∩]-absorberᵣ-raw : ∀{s} → Names.Absorberᵣ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(∅)
      _≅[_]≅_.accepts-ε   ([∩]-absorberᵣ-raw {x = A})     = [≡]-intro
      _≅[_]≅_.suffix-lang ([∩]-absorberᵣ-raw {x = A}) {c} = [∩]-absorberᵣ-raw {x = Language.suffix-lang A c}

  instance
    [∩]-absorber : Absorber ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(∅)
    [∩]-absorber = intro

  instance
    [∩]-binaryOperator : BinaryOperator ⦃ [≅]-equiv {s = s} ⦄ ⦃ [≅]-equiv {s = s} ⦄ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)
    BinaryOperator.congruence([∩]-binaryOperator {s = s}) = [∩]-binaryOperator-raw {s = s} where
      [∩]-binaryOperator-raw : ∀{s} → Names.Congruence₂ ⦃ [≅]-equiv {s = s} ⦄ ⦃ [≅]-equiv {s = s} ⦄ ⦃ [≅]-equiv {s = s} ⦄(_∩_)
      _≅[_]≅_.accepts-ε   ([∩]-binaryOperator-raw aeq beq) = [≡]-with-op(_&&_) (_≅[_]≅_.accepts-ε aeq) (_≅[_]≅_.accepts-ε beq)
      _≅[_]≅_.suffix-lang ([∩]-binaryOperator-raw aeq beq) = [∩]-binaryOperator-raw (_≅[_]≅_.suffix-lang aeq) (_≅[_]≅_.suffix-lang beq)

  instance
    [∩]-monoid : Monoid ⦃ [≅]-equiv {s = s} ⦄ (_∩_)
    Monoid.identity-existence [∩]-monoid = [∃]-intro(𝐔)

  instance
    [∪][∩]-distributivityₗ : Distributivityₗ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(_∩_)
    Distributivityₗ.proof([∪][∩]-distributivityₗ {s = s}) = [∪][∩]-distributivityₗ-raw {s = s} where
      [∪][∩]-distributivityₗ-raw : ∀{s} → Names.Distributivityₗ ⦃ [≅]-equiv {s = s} ⦄ (_∪_)(_∩_)
      _≅[_]≅_.accepts-ε   ([∪][∩]-distributivityₗ-raw {x = A})     = distributivityₗ(_||_)(_&&_) {x = Language.accepts-ε A}
      _≅[_]≅_.suffix-lang ([∪][∩]-distributivityₗ-raw {x = A}) {c} = [∪][∩]-distributivityₗ-raw {x = Language.suffix-lang A c}

  instance
    [∩][∪]-distributivityₗ : Distributivityₗ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(_∪_)
    Distributivityₗ.proof([∩][∪]-distributivityₗ {s = s}) = [∩][∪]-distributivityₗ-raw {s = s} where
      [∩][∪]-distributivityₗ-raw : ∀{s} → Names.Distributivityₗ ⦃ [≅]-equiv {s = s} ⦄ (_∩_)(_∪_)
      _≅[_]≅_.accepts-ε   ([∩][∪]-distributivityₗ-raw {x = A})     = distributivityₗ(_&&_)(_||_) {x = Language.accepts-ε A}
      _≅[_]≅_.suffix-lang ([∩][∪]-distributivityₗ-raw {x = A}) {c} = [∩][∪]-distributivityₗ-raw {x = Language.suffix-lang A c}

  instance
    [𝁼][∪]-distributivityₗ : Distributivityₗ ⦃ [≅]-equiv {s = s} ⦄ (_𝁼_)(_∪_)
    Distributivityₗ.proof ([𝁼][∪]-distributivityₗ {s = s}) = [𝁼][∪]-distributivityₗ-raw {s = s} where
      [𝁼][∪]-distributivityₗ-raw : ∀{s} → Names.Distributivityₗ ⦃ [≅]-equiv {s = s} ⦄ (_𝁼_)(_∪_)
      _≅[_]≅_.accepts-ε ([𝁼][∪]-distributivityₗ-raw {x = x}) with accepts x
      ... | 𝑇 = [≡]-intro
      ... | 𝐹 = [≡]-intro
      _≅[_]≅_.suffix-lang ([𝁼][∪]-distributivityₗ-raw {x = x}{y}{z}) {c} with accepts x
      ... | 𝑇 =
        ((suffix x c) 𝁼 (y ∪ z)) ∪ ((suffix y c) ∪ (suffix z c))                  🝖[ _≅_ ]-[ congruence₂-₁(_∪_) _ [𝁼][∪]-distributivityₗ-raw ]
        (((suffix x c) 𝁼 y) ∪ ((suffix x c) 𝁼 z)) ∪ ((suffix y c) ∪ (suffix z c)) 🝖[ _≅_ ]-[ One.associate-commute4 (commutativity(_∪_)) ]
        (((suffix x c) 𝁼 y) ∪ (suffix y c)) ∪ (((suffix x c) 𝁼 z) ∪ (suffix z c)) 🝖[ _≅_ ]-end
      ... | 𝐹 = [𝁼][∪]-distributivityₗ-raw

{-TODO
idempotence-by-dist-id-abs-idemp
x ∪ x
(x ∩ x) ∪ (x ∩ x)
(x ∪ x) ∩ x
(x ∪ x) ∩ (x ∪ ∅)
x ∪ (x ∩ ∅)
x ∪ ∅
x

idempotence-by-dist-inv-id
x ∪ x
(x ∪ x) ∩ 𝐔
(x ∪ x) ∩ (x ∪ (∁ x))
x ∪ (x ∩ (∁ x))
x ∪ ∅
x
-}

  instance
    [𝁼][∪]-distributivityᵣ : Distributivityᵣ ⦃ [≅]-equiv {s = s} ⦄ (_𝁼_)(_∪_)
    Distributivityᵣ.proof ([𝁼][∪]-distributivityᵣ {s}) = [𝁼][∪]-distributivityᵣ-raw where
      [𝁼][∪]-distributivityᵣ-raw : ∀{s} → Names.Distributivityᵣ ⦃ [≅]-equiv {s = s} ⦄ (_𝁼_)(_∪_)
      _≅[_]≅_.accepts-ε ([𝁼][∪]-distributivityᵣ-raw {x = x}{y}{z}) with accepts z
      ... | 𝑇 = [≡]-intro
      ... | 𝐹 = [≡]-intro
      _≅[_]≅_.suffix-lang ([𝁼][∪]-distributivityᵣ-raw {x = x}{y}{z}) {c} with accepts x | accepts y
      ... | 𝑇 | 𝑇 =
        (((suffix x c) ∪ (suffix y c)) 𝁼 z) ∪ (suffix z c)                        🝖[ _≅_ ]-[ congruence₂-₁(_∪_) _ [𝁼][∪]-distributivityᵣ-raw ]
        (((suffix x c) 𝁼 z) ∪ ((suffix y c) 𝁼 z)) ∪ (suffix z c)                  🝖[ _≅_ ]-[ congruence₂-₂(_∪_) _ {!!} ]-sym
        (((suffix x c) 𝁼 z) ∪ ((suffix y c) 𝁼 z)) ∪ ((suffix z c) ∪ (suffix z c)) 🝖[ _≅_ ]-[ One.associate-commute4 (commutativity(_∪_)) ]
        (((suffix x c) 𝁼 z) ∪ (suffix z c)) ∪ (((suffix y c) 𝁼 z) ∪ (suffix z c)) 🝖[ _≅_ ]-end
      ... | 𝑇 | 𝐹 = {!!}
      ... | 𝐹 | 𝑇 = {!!}
      ... | 𝐹 | 𝐹 = {!!}

  instance
    [𝁼]-associativity : Associativity ⦃ [≅]-equiv {s = s} ⦄ (_𝁼_)
    Associativity.proof ([𝁼]-associativity {s = s}) = [𝁼]-associativity-raw {s = s} where
      [𝁼]-associativity-raw : ∀{s} → Names.Associativity ⦃ [≅]-equiv {s = s} ⦄ (_𝁼_)
      _≅[_]≅_.accepts-ε   ([𝁼]-associativity-raw {s = s} {x} {y} {z} ) with Language.accepts-ε(x)
      ... | 𝑇 = [≡]-intro
      ... | 𝐹 = [≡]-intro
      _≅[_]≅_.suffix-lang ([𝁼]-associativity-raw {s = s} {x} {y} {z}) {c} {sₛ} with [𝁼]-associativity-raw {s = sₛ} {suffix x c}{y}{z} | accepts(x) | accepts(y)
      ... | p | 𝑇 | 𝑇 =
        ((((suffix x c) 𝁼 y) ∪ (suffix y c)) 𝁼 z) ∪ (suffix z c)       🝖[ _≅_ ]-[ congruence₂-₁(_∪_) _ (distributivityᵣ(_𝁼_)(_∪_)) ]
        ((((suffix x c) 𝁼 y) 𝁼 z) ∪ ((suffix y c) 𝁼 z)) ∪ (suffix z c) 🝖[ _≅_ ]-[ congruence₂-₁(_∪_) _ (congruence₂-₁(_∪_) _ p) ]
        (((suffix x c) 𝁼 (y 𝁼 z)) ∪ ((suffix y c) 𝁼 z)) ∪ (suffix z c) 🝖[ _≅_ ]-[ associativity(_∪_) ]
        ((suffix x c) 𝁼 (y 𝁼 z)) ∪ (((suffix y c) 𝁼 z) ∪ (suffix z c)) 🝖[ _≅_ ]-end
      ... | p | 𝑇 | 𝐹 =
        (((suffix x c) 𝁼 y) ∪ (suffix y c)) 𝁼 z       🝖[ _≅_ ]-[ distributivityᵣ(_𝁼_)(_∪_) ]
        (((suffix x c) 𝁼 y) 𝁼 z) ∪ ((suffix y c) 𝁼 z) 🝖[ _≅_ ]-[ congruence₂-₁(_∪_) _ p ]
        ((suffix x c) 𝁼 (y 𝁼 z)) ∪ ((suffix y c) 𝁼 z) 🝖[ _≅_ ]-end
      ... | p | 𝐹 | _ = p

  {- TODO: Is it possible to describe concatenation using an algebraic property? Maybe something about that it behaves like (_⨯_) (combining every element with each other in some way)? Probably a "Kleene algebra".

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

-}




module _ {Σ : Alphabet{ℓ}} where
  open Oper{ℓ}{Σ}
  open Language renaming (accepts-ε to accepts ; suffix-lang to suffix)

  open import Logic.IntroInstances
  open import Structure.Sets.Operator hiding (_∪_ ; _∩_ ; ∁ ; ∅ ; 𝐔)
  open import Structure.Sets.Relator hiding (_≡_ ; _⊆_)

  instance
    [≅]-set-equality : SetEqualityRelation([ s ]_∈_)([ s ]_∈_)(_≅[ s ]≅_)
    SetEqualityRelation.membership [≅]-set-equality {A}{B} = [↔]-intro (l{A = A}{B = B}) (r{A = A}{B = B}) where
      l : ∀{A B : Language(Σ)} → (A ≅[ s ]≅ B) ← (∀{w} → ([ s ] w ∈ A) ↔ ([ s ] w ∈ B))
      _≅[_]≅_.accepts-ε (l {A = A} {B = B} p) with accepts A | accepts B | p{[]}
      ... | 𝑇 | 𝑇 | _ = [≡]-intro
      ... | 𝑇 | 𝐹 | q with () ← [↔]-to-[→] q <>
      ... | 𝐹 | 𝑇 | q with () ← [↔]-to-[←] q <>
      ... | 𝐹 | 𝐹 | _ = [≡]-intro
      _≅[_]≅_.suffix-lang (l {A = A} {B = B} p) {c} = l {A = suffix A c}{B = suffix B c} (\{w} → p{c ⊰ w})

      r : ∀{A B : Language(Σ)} → (A ≅[ s ]≅ B) → (∀{w} → ([ s ] w ∈ A) ↔ ([ s ] w ∈ B))
      Tuple.left (r ab {[]}) wB = substitute₁ₗ(IsTrue) (_≅[_]≅_.accepts-ε ab) wB
      Tuple.right (r ab {[]}) wA = substitute₁ᵣ(IsTrue) (_≅[_]≅_.accepts-ε ab) wA
      Tuple.left (r {s = s} {A} {B} ab {_⊰_ {sₛ} x w}) wB = [↔]-to-[←] (r {s = sₛ} (_≅[_]≅_.suffix-lang {s = s} ab {sₛ = sₛ}) {w}) wB
      Tuple.right (r {s = s} {A} {B} ab {_⊰_ {sₛ} x w}) wA = [↔]-to-[→] (r {s = sₛ} (_≅[_]≅_.suffix-lang {s = s} ab {sₛ = sₛ}) {w}) wA

  instance
    [∪]-operator : UnionOperator([ s ]_∈_)([ s ]_∈_)([ s ]_∈_)(_∪_)
    UnionOperator.membership [∪]-operator {A}{B}{w} = [↔]-intro (l{w = w}{A}{B}) (r{w = w}{A}{B}) where
      l : ∀{w}{A B} → ([ s ] w ∈ (A ∪ B)) ← (([ s ] w ∈ A) ∨ ([ s ] w ∈ B))
      l {w = []}    = [↔]-to-[←] IsTrue.preserves-[||][∨]
      l {w = c ⊰ w} = l {w = w}

      r : ∀{w}{A B} → ([ s ] w ∈ (A ∪ B)) → (([ s ] w ∈ A) ∨ ([ s ] w ∈ B))
      r {w = []}    = [↔]-to-[→] IsTrue.preserves-[||][∨]
      r {w = c ⊰ w} = r {w = w}

  instance
    [∩]-operator : IntersectionOperator([ s ]_∈_)([ s ]_∈_)([ s ]_∈_)(_∩_)
    IntersectionOperator.membership [∩]-operator {A}{B}{w} = [↔]-intro (l{w = w}{A}{B}) (r{w = w}{A}{B}) where
      l : ∀{w}{A B} → ([ s ] w ∈ (A ∩ B)) ← (([ s ] w ∈ A) ∧ ([ s ] w ∈ B))
      l {w = []}    = [↔]-to-[←] IsTrue.preserves-[&&][∧]
      l {w = c ⊰ w} = l {w = w}

      r : ∀{w}{A B} → ([ s ] w ∈ (A ∩ B)) → (([ s ] w ∈ A) ∧ ([ s ] w ∈ B))
      r {w = []}    = [↔]-to-[→] IsTrue.preserves-[&&][∧]
      r {w = c ⊰ w} = r {w = w}

  instance
    [∁]-operator : ComplementOperator([ s ]_∈_)([ s ]_∈_)(∁_)
    ComplementOperator.membership [∁]-operator {A}{w} = [↔]-intro (l{w = w}{A}) (r{w = w}{A}) where
      l : ∀{w}{A} → ([ s ] w ∈ (∁ A)) ← ¬([ s ] w ∈ A)
      l {w = []}    = [↔]-to-[←] IsTrue.preserves-[!][¬]
      l {w = c ⊰ w} = l {w = w}

      r : ∀{w}{A} → ([ s ] w ∈ (∁ A)) → ¬([ s ] w ∈ A)
      r {w = []} = [↔]-to-[→] IsTrue.preserves-[!][¬]
      r {w = c ⊰ w} = r {w = w}

  instance
    [∅]-set : EmptySet([ s ]_∈_)(∅)
    EmptySet.membership [∅]-set {x = w} = p{w = w} where
      p : ∀{w} → ¬([ s ] w ∈ ∅)
      p {w = []} ()
      p {w = x ⊰ w} = p {w = w}

  instance
    [𝐔]-set : UniversalSet([ s ]_∈_)(𝐔)
    UniversalSet.membership [𝐔]-set {x = w} = p{w = w} where
      p : ∀{w} → ([ s ] w ∈ 𝐔)
      p {w = []}    = [⊤]-intro
      p {w = c ⊰ w} = p {w = w}

  [ε]-set : ∀{x} → (x ∈ ε) ↔ (x ≡ [])
  [ε]-set {x} = [↔]-intro (l{x}) (r{x}) where
    l : ∀{x} → (x ∈ ε) ← (x ≡ [])
    l {[]} [≡]-intro = [⊤]-intro

    r : ∀{x} → (x ∈ ε) → (x ≡ [])
    r {[]}    _     = [≡]-intro
    r {a ⊰ l} proof with () ← [∅]-membership {x = l} proof

  {-open import Structure.Container.SetLike hiding (_∪_ ; _∩_ ; ∁ ; ∅ ; 𝐔)
  -- TODO: Copy-pasted from the previous code that only used coinduction
  instance
    [𝁼][∪]-distributivityₗ : Distributivityₗ ⦃ [≅]-equiv {s = s} ⦄ (_𝁼_)(_∪_)
    Distributivityₗ.proof ([𝁼][∪]-distributivityₗ {s = s}) = [𝁼][∪]-distributivityₗ-raw {s = s} where
      [𝁼][∪]-distributivityₗ-raw : ∀{s} → Names.Distributivityₗ ⦃ [≅]-equiv {s = s} ⦄ (_𝁼_)(_∪_)
      _≅[_]≅_.accepts-ε ([𝁼][∪]-distributivityₗ-raw {x = x}) with accepts x
      ... | 𝑇 = [≡]-intro
      ... | 𝐹 = [≡]-intro
      _≅[_]≅_.suffix-lang ([𝁼][∪]-distributivityₗ-raw {s = s} {x = x}{y}{z}) {c} with accepts x
      ... | 𝑇 =
        ((suffix x c) 𝁼 (y ∪ z)) ∪ ((suffix y c) ∪ (suffix z c))                  🝖[ _≅[ s ]≅_ ]-[ congruence₂-₁(_∪_) _ [𝁼][∪]-distributivityₗ-raw ]
        (((suffix x c) 𝁼 y) ∪ ((suffix x c) 𝁼 z)) ∪ ((suffix y c) ∪ (suffix z c)) 🝖[ _≅[ s ]≅_ ]-[ One.associate-commute4 (commutativity(_∪_)) ]
        (((suffix x c) 𝁼 y) ∪ (suffix y c)) ∪ (((suffix x c) 𝁼 z) ∪ (suffix z c)) 🝖[ _≅[ s ]≅_ ]-end
      ... | 𝐹 = [𝁼][∪]-distributivityₗ-raw
  -}



{- -- TODO: Sizes and (_++_)
  [𝁼]-membershipₗ : ∀{x y}{A B : Language(Σ)} → ([ s ] x ∈ A) → ([ s ] y ∈ B) → ([ s ] (x ++ y) ∈ (A 𝁼 B))
  [𝁼]-membershipₗ {x = []}   {[]}   {A}{B} xA yB with accepts A | accepts B
  ... | 𝑇 | 𝑇 = <>
  [𝁼]-membershipₗ {x = []}   {c ⊰ y}{A}{B} xA yB with accepts A
  ... | 𝑇 = [↔]-to-[←] (Union.membership {a = suffix A c 𝁼 B} {b = suffix B c} {x = y}) ([∨]-introᵣ yB)
  [𝁼]-membershipₗ {x = c ⊰ x}{y}{A}{B} xA yB with accepts A
  ... | 𝑇 = {!!}
  ... | 𝐹 = [𝁼]-membershipₗ {x = x}{y}{suffix A c}{B} {!xA!} {!!}
-}

-- [𝁼]-membershipₗ {[]}{y}{suffix }
-- [↔]-to-[←] (Union.membership {a = {!!}}{b = {!!}}{x = {!!}}) ([∨]-introᵣ yB)
{-

  single-containment : ⦃ _ : ComputablyDecidable(_≡_) ⦄ → ∀{x}{a} → (x ∈ single(a)) ↔ (x ≡ singleton(a))
  single-containment ⦃ dec ⦄ = [↔]-intro l r where
    postulate l : ∀{x}{a} → (x ∈ single(a)) ← (x ≡ singleton(a))
    {-l {c ⊰ w} [≡]-intro with ComputablyDecidable.decide(_≡_) ⦃ dec ⦄ c c
    ... | 𝑇 = {!!}
    ... | 𝐹 = {!!}-}

    postulate r : ∀{x}{a} → (x ∈ single(a)) → (x ≡ singleton(a))
    --r {c ⊰ w} p = {![↔]-to-[←] (ComputablyDecidable.proof-istrue(_≡_) {x = ?}) ?!}

  Language-list-suffix : Language(Σ) → List(Σ) → Language(Σ)
  Language-list-suffix A []      = A
  Language-list-suffix A (x ⊰ l) = Language.suffix-lang(A)(x)

  postulate suffix-concat-step : ∀{A : Language(Σ)}{l₁ l₂} → ((l₁ ++ l₂) ∈ A) → (l₂ ∈ Language-list-suffix(A)(l₁))
  -- suffix-concat-step {A}{[]}         p = p
  -- suffix-concat-step {A}{x ⊰ l₁}{l₂} p = {!!}

  postulate [𝁼]-containmentₗ : ∀{x y}{A B : Language(Σ)} → (x ∈ A) → (y ∈ B) → ((x ++ y) ∈ (A 𝁼 B))
  -- [𝁼]-containmentₗ {x} {y} {A} {B} xa xb with Language.accepts-ε(A) | y Oper.∈? B
  {-[𝁼]-containmentₗ {LongOper.empty} {LongOper.empty} {A} {B} xa xb with Language.accepts-ε(A) | Language.accepts-ε(B)
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
-}

  -- [𝁼]-containment : ∀{x}{A B : Language(Σ)} → (x ∈ (A 𝁼 B)) ↔ ∃(a ↦ ∃ b ↦ (a ++ b ≡ x)∧(a ∈ A)∧(b ∈ B))
  -- [𝁼]-containment {x} = [↔]-intro (l{x}) (r{x}) where

-- TODO: Set properties
-- TODO: Connection with logic (from sets) in relations
-}
