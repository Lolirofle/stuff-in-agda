{-# OPTIONS --cubical #-}

module Miscellaneous.IdentityKElimProof where

open import Logic.Classical
open import Type.Properties.Decidable.Proofs
open import Operator.Equals
open import Structure.Type.Identity
open import Structure.Type.Identity.Eliminator.Equality
open import Structure.Type.Identity.Proofs

{- TODO: test50 is supposed to be a generalization of this. Not sure how to do it, if it is possible even
Bool-Id-kElim : ∀{ℓ} → IdentityKEliminator(Id{T = Bool}) {ℓ}
IdentityKEliminator.elim Sign-Id-kElim P p {𝐹} = idElimFixedᵣ(Id) (\{ {𝐹} → const Empty ; {𝑇} → P }) p
IdentityKEliminator.elim Sign-Id-kElim P p {𝑇} = idElimFixedᵣ(Id) (\{ {𝑇} → const Empty ; {𝐹} → P }) p
-}

open import Data.Boolean

-- test50 : ⦃ EquivDecidable(Bool) ⦄ → ∀{ℓ} → IdentityKEliminator(Path{P = Bool}) {ℓ}
-- IdentityKEliminator.elim test50 P p {x} xx = idElimFixedᵣ(Path) (\{y} xy → P{y} {!substitute₂-₁ᵣ(Path)(y) xy xy!}) {!!} xx

{-
import      Lvl
open import Type

private variable ℓ : Lvl.Level
private variable ℓₑ : Lvl.Level → Lvl.Level
private variable T : Type{ℓ}
private variable Id : ∀{ℓ}{T : Type{ℓ}} → T → T → Type{ℓₑ(ℓ)}

open import Logic.Classical
open import Logic.Predicate
open import Logic.Propositional
-- open import Logic.Propositional.Equiv
open import Structure.Relator
open import Structure.Relator.Properties
open import Type.Properties.Decidable.Proofs
open import Operator.Equals

private instance _ = identityEliminator-to-transitivity
private instance _ = identityEliminator-to-symmetry
private instance _ = identityEliminator-to-equiv
private instance _ = identityEliminator-to-function

module _ ⦃ ident : IdentityType(Id) ⦄ ⦃ dec : EquivDecidable(T) ⦄ where
  decidable-to-Id-kElim : ∀{ℓ} → IdentityKEliminator(Id{T = T}) {ℓ}
  IdentityKEliminator.elim decidable-to-Id-kElim P p {b} eq = substitute₁ᵣ(P) ⦃ {!!} ⦄ {!!} (idElim(Id) (\{x}{y} xy → [∨]-elim P (\nid → [⊥]-elim(nid(reflexivity(Id)))) (excluded-middle(Id x x) ⦃ decider-classical(Id x x) ⦃ {![∃]-proof dec!} ⦄ ⦄)) {!!} {!!})
  -- [∨]-elim P (\nid → [⊥]-elim(nid(reflexivity(Id)))) (excluded-middle(Id x x) ⦃ decider-classical(Id x x) ⦃ {![∃]-proof dec!} ⦄ ⦄)
  -- substitute₁ᵣ(P) ⦃ {!!} ⦄ {!!} (idElimFixedᵣ(Id) (\bB → P (transitivity(Id) (symmetry(Id) bB) bB)) (substitute₁ₗ(P) ⦃ {!!} ⦄ identity p) eq) where
  --   identity : ∀{x : T} → Id (transitivity(Id) (symmetry(Id) (reflexivity(Id))) (reflexivity(Id))) (reflexivity(Id) {x})
  -- idElimFixedᵣ{T = Bool}(Id) {x = b} (\{B} bB → P{B} (transitivity(Id) (symmetry(Id) bB) bB)) (substitute₁ₗ(P) {!!} p) {y = b} {!transitivity(Path) (symmetry(Path) eq) eq!}
  -- [∨]-elim ? ? (excluded-middle(Path b B) ⦃ decider-classical _ ⦃ [∃]-proof dec ⦄  ⦄)
-- (\{bb} → if b then P{b} else ?)

{-
open import Type.Cubical
open import Type.Cubical.Path.Functions

test10 : ∀{x y : Bool} → Id x y → Path x y
test10 intro = point

test11 : ∀{x y : Bool} → Path x y → Id x y
test11 {𝑇}{𝑇} p = intro
test11 {𝑇}{𝐹} p = empty(Bool-different-values(reverse p))
test11 {𝐹}{𝑇} p = empty(Bool-different-values p)
test11 {𝐹}{𝐹} p = intro
{-
open import Logic.Propositional.Equiv
open import Type.Identity.Proofs
test12' : ∀{x y}{p : Path x y} → Id(test11 p) (substitute₂-₂ᵣ ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ (Id) ⦃ Id-to-function₂ ⦄ (x) (test11 p) intro)
-- (substitute₂-₂ᵣ(Id) ⦃ {!!} ⦄ (x) {!!} intro)
test12' {𝑇}{𝑇}    = intro
test12' {𝑇}{𝐹}{p} = empty(Bool-different-values(reverse p))
test12' {𝐹}{𝑇}{p} = empty(Bool-different-values p)
test12' {𝐹}{𝐹}    = intro

test12'' : ∀{x y}{p : Path x y} → Path (test10(test11 p)) p
test12'' {x} {y} {p} = {!!}
-}

test12 : ∀{x y}{p : Path x y} → Path (test10(test11 p)) p
test12 {𝑇}{𝑇}{p} = {!p j!}
test12 {𝑇}{𝐹}{p} = empty(Bool-different-values(reverse p))
test12 {𝐹}{𝑇}{p} = empty(Bool-different-values p)
test12 {𝐹}{𝐹}{p} i j = {!p j!}

test13 : ∀{x y}{p : Id x y} → Path (test11(test10 p)) p
test13 {𝑇} {p = intro} i = intro
test13 {𝐹} {p = intro} i = intro

test15 : ∀{x y}{p : Id x y} → Id(test11(test10 p)) p
test15 {𝑇}{p = intro} = intro
test15 {𝐹}{p = intro} = intro
-}
-}
