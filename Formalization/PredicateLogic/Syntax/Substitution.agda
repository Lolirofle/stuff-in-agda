open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Syntax.Substitution (𝔏 : Signature) where
open Signature(𝔏)

open import Data.Boolean
open import Data.ListSized
import      Data.ListSized.Functions as List
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Functional using (_∘_ ; _∘₂_ ; id ; apply)
open import Numeral.CoordinateVector as Vector using (Vector)
open import Numeral.Finite
open import Numeral.Natural
open import Syntax.Function
open import Type

private variable args n vars vars₁ vars₂ : ℕ

-- Substitutes the variables of a term by mapping every variable index to a term.
substituteTerm : Vector(vars₁)(Term(vars₂)) → Term(vars₁) → Term(vars₂)
substituteTerm₊ : Vector(vars₁)(Term(vars₂)) → List(Term(vars₁))(args) → List(Term(vars₂))(args)
substituteTerm  t (var v)    = Vector.proj t v
substituteTerm  t (func f x) = func f (substituteTerm₊ t x)
substituteTerm₊ t ∅        = ∅
substituteTerm₊ t (x ⊰ xs) = (substituteTerm t x) ⊰ (substituteTerm₊ t xs)

-- Adds a new untouched variable to a term mapper.
-- Example: termMapper𝐒(0 ↦ t0 ; 1 ↦ t1 ; 2 ↦ t2) = (0 ↦ var 0 ; 1 ↦ t0 ; 2 ↦ t1 ; 3 ↦ t2)
termMapper𝐒 : Vector(vars₁)(Term(vars₂)) → Vector(𝐒(vars₁))(Term(𝐒(vars₂)))
termMapper𝐒 = Vector.prepend(var 𝟎) ∘ Vector.map(substituteTerm(var ∘ 𝐒))

-- Substitutes the variables of a formula by mapping every variable index to a term.
substitute : Vector(vars₁)(Term(vars₂)) → Formula(vars₁) → Formula(vars₂)
substitute t (P $ x)  = P $ (substituteTerm₊ t x)
substitute t ⊤        = ⊤
substitute t ⊥        = ⊥
substitute t (φ ∧ ψ)  = (substitute t φ) ∧ (substitute t ψ)
substitute t (φ ∨ ψ)  = (substitute t φ) ∨ (substitute t ψ)
substitute t (φ ⟶ ψ)  = (substitute t φ) ⟶ (substitute t ψ)
substitute t (Ɐ φ)    = Ɐ(substitute (termMapper𝐒 t) φ)
substitute t (∃ φ)    = ∃(substitute (termMapper𝐒 t) φ)

-- Substitutes the most recent variable of a formula by mapping it to a term.
substitute0 : Term(vars) → Formula(𝐒(vars)) → Formula(vars)
substitute0 = substitute ∘ (t ↦ Vector.prepend t var)

-- Substitutes a single arbitrary variable of a formula by mapping it to a term.
-- Note: (substituteN 𝟎) normalizes to substitute0 because of the definition for Vector.insert.
substituteN : 𝕟₌(vars) → Term(vars) → Formula(𝐒(vars)) → Formula(vars)
substituteN n = substitute ∘ (t ↦ Vector.insert₊ n t var)

open import Data
open import Function.Equals
import      Function.Names as Names
import      Lvl
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator
open import Syntax.Number

private variable ℓ : Lvl.Level
private variable A B : Type{ℓ}
private variable f g : A → B
private variable φ : Formula(vars)

termMapper𝐒-identity : (termMapper𝐒{vars₁ = vars} var ⊜ var)
_⊜_.proof termMapper𝐒-identity {x = 𝟎}   = [≡]-intro
_⊜_.proof termMapper𝐒-identity {x = 𝐒 v} = [≡]-intro

module _ {f g : 𝕟(vars₁) → Term(vars₂)} (eq : f ⊜ g) where
  termMapper𝐒-equal-functions : (termMapper𝐒 f ⊜ termMapper𝐒 g)
  _⊜_.proof termMapper𝐒-equal-functions {𝟎} = [≡]-intro
  _⊜_.proof termMapper𝐒-equal-functions {𝐒 v} rewrite _⊜_.proof eq{v} = [≡]-intro

  substituteTerm-equal-functions-raw : (substituteTerm f Names.⊜ substituteTerm g)
  substituteTerm₊-equal-functions-raw : (substituteTerm₊{args = args} f Names.⊜ substituteTerm₊ g)
  (substituteTerm-equal-functions-raw) {var x} = _⊜_.proof eq
  (substituteTerm-equal-functions-raw) {func f x}
    rewrite substituteTerm₊-equal-functions-raw {x = x}
    = [≡]-intro
  (substituteTerm₊-equal-functions-raw) {x = ∅}      = [≡]-intro
  (substituteTerm₊-equal-functions-raw) {x = x ⊰ xs}
    rewrite substituteTerm-equal-functions-raw {x}
    rewrite substituteTerm₊-equal-functions-raw {x = xs}
    = [≡]-intro
  substituteTerm-equal-functions : (substituteTerm f ⊜ substituteTerm g)
  substituteTerm-equal-functions = intro(\{x} → substituteTerm-equal-functions-raw{x})
  substituteTerm₊-equal-functions : (substituteTerm₊{args = args} f ⊜ substituteTerm₊ g)
  substituteTerm₊-equal-functions = intro substituteTerm₊-equal-functions-raw

substitute-equal-functions : (f ⊜ g) → (substitute f ⊜ substitute g)
substitute-equal-functions = intro ∘ p where
  p : (f ⊜ g) → (substitute f Names.⊜ substitute g)
  p eq {P $ x}
    rewrite _⊜_.proof (substituteTerm₊-equal-functions eq) {x}
    = [≡]-intro
  p eq {⊤}     = [≡]-intro
  p eq {⊥}     = [≡]-intro
  p eq {φ ∧ ψ}
    rewrite p eq {φ}
    rewrite p eq {ψ}
    = [≡]-intro
  p eq {φ ∨ ψ}
    rewrite p eq {φ}
    rewrite p eq {ψ}
    = [≡]-intro
  p eq {φ ⟶ ψ}
    rewrite p eq {φ}
    rewrite p eq {ψ}
    = [≡]-intro
  p eq {Ɐ φ}
    rewrite p (termMapper𝐒-equal-functions eq) {φ}
    = [≡]-intro
  p eq {∃ φ}
    rewrite p (termMapper𝐒-equal-functions eq) {φ}
    = [≡]-intro

substituteTerm-identity-raw : (substituteTerm{vars₁ = vars} var Names.⊜ id)
substituteTerm₊-identity-raw : (substituteTerm₊{vars₁ = vars}{args = args} var Names.⊜ id)
substituteTerm-identity-raw {x = var x}    = [≡]-intro
substituteTerm-identity-raw {x = func f x} rewrite substituteTerm₊-identity-raw{x = x} = [≡]-intro
substituteTerm₊-identity-raw {x = ∅} = [≡]-intro
substituteTerm₊-identity-raw {x = x ⊰ xs}
  rewrite substituteTerm-identity-raw{x = x}
  rewrite substituteTerm₊-identity-raw{x = xs}
  = [≡]-intro
substituteTerm-identity : (substituteTerm{vars₁ = vars} var ⊜ id)
substituteTerm-identity = intro substituteTerm-identity-raw
substituteTerm₊-identity : (substituteTerm₊{vars₁ = vars}{args = args} var ⊜ id)
substituteTerm₊-identity = intro substituteTerm₊-identity-raw

substitute-identity : (substitute{vars₁ = vars} var ⊜ id)
substitute-identity = intro p where
  p : (substitute{vars₁ = vars} var Names.⊜ id)
  p {x = P $ x} rewrite _⊜_.proof substituteTerm₊-identity {x} = [≡]-intro
  p {x = ⊤}     = [≡]-intro
  p {x = ⊥}     = [≡]-intro
  p {x = φ ∧ ψ} rewrite p {x = φ} rewrite p {x = ψ} = [≡]-intro
  p {x = φ ∨ ψ} rewrite p {x = φ} rewrite p {x = ψ} = [≡]-intro
  p {x = φ ⟶ ψ} rewrite p {x = φ} rewrite p {x = ψ} = [≡]-intro
  p {x = Ɐ φ}
    rewrite _⊜_.proof (substitute-equal-functions termMapper𝐒-identity) {φ}
    rewrite p {x = φ}
    = [≡]-intro
  p {x = ∃ φ}
    rewrite _⊜_.proof (substitute-equal-functions termMapper𝐒-identity) {φ}
    rewrite p {x = φ}
    = [≡]-intro

{-
test1 : ∀{t : Term(vars)}{n : 𝕟(𝐒(𝐒 vars))} → (termMapper𝐒 (introduceVar t) n ≡ introduceVar (termVar𝐒 t) n)
test1 {t = var 𝟎} {𝟎} = {!introduceVar(termVar𝐒{_}(?)) 0!}
test1 {t = var 𝟎} {𝐒 n} = {!termMapper𝐒(introduceVar(?)) 1!}
test1 {t = var (𝐒 v)}{n} = {!!}
test1 {t = func f x}{n} = {!!}

test : ∀{t}{φ : Formula(𝐒 vars)} → (substitute(introduceVar t) φ ≡ substitute0 t φ)
test {vars} {t} {P $ x} = {!!}
test {vars} {t} {⊤} = [≡]-intro
test {vars} {t} {⊥} = [≡]-intro
test {vars} {t} {φ ∧ ψ} rewrite test {vars}{t}{φ} rewrite test{vars}{t}{ψ} = [≡]-intro
test {vars} {t} {φ ∨ ψ} rewrite test {vars}{t}{φ} rewrite test{vars}{t}{ψ} = [≡]-intro
test {vars} {t} {φ ⟶ ψ} rewrite test {vars}{t}{φ} rewrite test{vars}{t}{ψ} = [≡]-intro
test {vars} {t} {Ɐ φ} = {!test{𝐒 vars}{termVar𝐒 t}{φ}!}
test {vars} {t} {∃ φ} = {!!}
-}
