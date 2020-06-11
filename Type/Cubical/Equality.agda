{-# OPTIONS --cubical #-}

module Type.Cubical.Equality where

open import Functional
open import Function.Axioms
import      Lvl
open import Logic
open import Logic.Predicate
open import Type
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Proofs as Path
open import Type.Homotopy
open import Type.Properties.Singleton.Proofs
open import Type.Properties.Singleton
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Setoid using (Equiv ; intro)

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable f : A → B
private variable _▫_ : A → B → C
private variable P : T → Type{ℓ}
private variable x y : T

_≡_ : T → T → Type
_≡_ = Path

instance
  [≡]-reflexivity : Reflexivity(_≡_ {T = T})
  [≡]-reflexivity = intro Path.point

instance
  [≡]-symmetry : Symmetry(_≡_ {T = T})
  [≡]-symmetry = intro Path.reverse

instance
  [≡]-transitivity : Transitivity(_≡_ {T = T})
  [≡]-transitivity = intro Path.concat

instance
  [≡]-equivalence : Equivalence(_≡_ {T = T})
  [≡]-equivalence = intro

instance
  [≡]-equiv : Equiv(T)
  [≡]-equiv = intro(_≡_) ⦃ [≡]-equivalence ⦄

instance
  [≡]-congruence₁ : Function(f)
  [≡]-congruence₁ {f = f} = intro(Path.map f)

instance
  [≡]-congruence₂ : BinaryOperator(_▫_)
  [≡]-congruence₂ {_▫_ = _▫_} = intro(Path.map₂(_▫_))

instance
  [≡]-substitution₁ : UnaryRelator(P)
  [≡]-substitution₁ {P = P} = intro(Path.liftedSpaceMap P)

instance
  [≡]-substitution₂ : BinaryRelator(_▫_)
  [≡]-substitution₂ {_▫_ = _▫_} = intro(Path.liftedSpaceMap₂(_▫_))

instance
  [≡][→]-sub : (_≡_) ⊆₂ (_→ᶠ_ {ℓ}{ℓ})
  [≡][→]-sub = intro(Path.spaceMap)

instance
  [≡]-function-extensionality : FunctionExtensionality A B
  [≡]-function-extensionality = intro Path.mapping

instance
  [≡]-dependent-function-extensionality : ∀{A : Type{ℓ₁}}{B : (a : A) → Type{ℓ₂}} → DependentFunctionExtensionality A B
  [≡]-dependent-function-extensionality = intro Path.mapping

instance
  [≡]-function-application : FunctionApplication A B
  [≡]-function-application = intro Path.mappingPoint

prop-is-prop-unit : ⦃ proof : MereProposition(A) ⦄ → IsUnit(MereProposition(A))
MereProposition.uniqueness (IsUnit.unit prop-is-prop-unit) {x} {y} = uniqueness _
MereProposition.uniqueness (IsUnit.uniqueness prop-is-prop-unit {intro p} i) {x}{y} j = Interval.hComp d x where
  d : Interval → Interval.Partial (Interval.max (Interval.max (Interval.flip i) i) (Interval.max (Interval.flip j) j)) _
  d k (i = Interval.𝟎) = uniqueness _ {x}{p{x}{y} j} k
  d k (i = Interval.𝟏) = uniqueness _ {x}{uniqueness _ {x}{y} j} k
  d k (j = Interval.𝟎) = uniqueness _ {x}{x} k
  d k (j = Interval.𝟏) = uniqueness _ {x}{y} k

[≡]-isUnit : ∀{ℓ}{A : Type{ℓ}} → ⦃ _ : MereProposition(A) ⦄ → (∀{x y : A} → IsUnit(x ≡ y))
IsUnit.unit [≡]-isUnit = uniqueness _
IsUnit.uniqueness ([≡]-isUnit {x = x} {y = y}) {p} = congruence₁ (prop ↦ MereProposition.uniqueness prop {x}{y}) (IsUnit.uniqueness prop-is-prop-unit {intro (\{x y} → {!p!})})



data PropSquash(A : Type{ℓ}) : Type{ℓ} where
  propSquash : A → PropSquash(A)
  PropSquash-prop-raw : ∀{x y : PropSquash(A)} → (x ≡ y)

instance
  PropSquash-prop : MereProposition(PropSquash(A))
  PropSquash-prop = intro PropSquash-prop-raw

PropSquash-function : ⦃ prop : MereProposition(B) ⦄ → (A → B) → (PropSquash(A) → B)
PropSquash-function         f (propSquash a)                 = f(a)
PropSquash-function {B = B} f (PropSquash-prop-raw {x}{y} i) = uniqueness(B) {PropSquash-function f x} {PropSquash-function f y} i

module _ {P : PropSquash(A) → Type{ℓ}} ⦃ prop-p : ∀{a} → MereProposition(P(a)) ⦄ where
  PropSquash-elim : (∀{x} → P(propSquash x)) → (∀{a} → P(a))
  PropSquash-elim p {propSquash a} = p{a}
  PropSquash-elim p {PropSquash-prop-raw {x} {y} i} = uniqueness _ ⦃ inst = {!prop-dependent-implication ⦃ prop-b = prop-p ⦄!} ⦄ {{!PropSquash-elim p{}!}}{{!!}} i
  -- uniqueness {!!} {PropSquash-elim p {{!x!}}} {PropSquash-elim p} i



data SetSquash(A : Type{ℓ}) : Type{ℓ} where
  setSquash : A → SetSquash(A)
  SetSquash-set-raw : ∀{x y : SetSquash(A)}{p₁ p₂ : (x ≡ y)} → (p₁ ≡ p₂)



data Quotient(_▫_ : T → T → Type{ℓ}) : Type{Lvl.of(T) Lvl.⊔ ℓ} where
  class : T → Quotient(_▫_)
  class-extensionality : (x ▫ y) → (class x ≡ class y)

postulate class-property : ⦃ prop : ∀{c : Quotient(_▫_)} → MereProposition(P(c)) ⦄ → (∀{a} → P(class a)) → (∀{c} → P(c))
-- class-property p {class a} = p{a}
-- class-property p {class-extensionality xy i} = {!!}
-- class-property p {quotient-squash p₁ p₂ i i₁} = {!!}

{- TODO: Needs something about mere propositions. Surjective uses existence defined as Σ, so it is not a mere proposition
instance
  class-surjective : Trunc(Surjective(class{_▫_ = _▫_}))
  class-surjective {_▫_ = _▫_} = class-property{_▫_ = _▫_} ⦃ intro trunc-squash ⦄ \{x} → trunc(intro([∃]-intro x))
-}

class-extensionality-proof : (class{_▫_ = _▫_} x ≡ class y) → (x ▫ y)
class-extensionality-proof {x = x} {y} p with p Interval.𝟎
... | class x₁ = {!!}
... | class-extensionality x₁ i = {!!}
