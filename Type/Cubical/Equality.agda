{-# OPTIONS --cubical #-}

module Type.Cubical.Equality where

open import Functional
open import Function.Axioms
import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Type
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Proofs as Path
open import Type.Properties.MereProposition
open import Type.Properties.Singleton.Proofs
open import Type.Properties.Singleton
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Setoid.WithLvl using (Equiv ; intro)
open import Structure.Type.Identity

private variable ℓ ℓ₁ ℓ₂ ℓₚ : Lvl.Level
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
  [≡]-sub-of-reflexive : ⦃ refl : Reflexivity(_▫_) ⦄ → ((_≡_) ⊆₂ (_▫_))
  [≡]-sub-of-reflexive {_▫_ = _▫_} = intro(\{a b} → ab ↦ sub₂(_≡_)(_→ᶠ_) ⦃ [≡][→]-sub ⦄ (congruence₂ᵣ(_▫_)(a) ab) (reflexivity(_▫_) {a}))

instance
  [≡]-function-extensionality : FunctionExtensionality A B
  [≡]-function-extensionality = intro Path.mapping

instance
  [≡]-dependent-function-extensionality : ∀{A : Type{ℓ₁}}{B : (a : A) → Type{ℓ₂}} → DependentFunctionExtensionality A B
  [≡]-dependent-function-extensionality = intro Path.mapping

instance
  [≡]-function-application : FunctionApplication A B
  [≡]-function-application = intro Path.mappingPoint

[≡]-identity-eliminator : IdentityEliminator{ℓₚ = ℓₚ}(_≡_ {T = T})
IdentityEliminator.proof [≡]-identity-eliminator P prefl eq  = sub₂(_≡_)(_→ᶠ_) ⦃ [≡][→]-sub ⦄ (\i → P(\j → eq(Interval.min i j))) prefl

-- TODO: Organize and move everything below

prop-is-prop-unit : ⦃ proof : MereProposition(A) ⦄ → IsUnit(MereProposition(A))
MereProposition.uniqueness (IsUnit.unit prop-is-prop-unit) {x} {y} = uniqueness _
MereProposition.uniqueness (IsUnit.uniqueness (prop-is-prop-unit {A = A}) {intro p} i) {x}{y} j = Interval.hComp d x where
  d : Interval → Interval.Partial (Interval.max (Interval.max (Interval.flip i) i) (Interval.max (Interval.flip j) j)) A
  d k (i = Interval.𝟎) = uniqueness(A) {x}{p{x}{y} j} k
  d k (i = Interval.𝟏) = uniqueness(A) {x}{uniqueness(A) {x}{y} j} k
  d k (j = Interval.𝟎) = uniqueness(A) {x}{x} k
  d k (j = Interval.𝟏) = uniqueness(A) {x}{y} k

{-
[≡]-isUnit : ∀{ℓ}{A : Type{ℓ}} → ⦃ _ : MereProposition(A) ⦄ → (∀{x y : A} → IsUnit(x ≡ y))
IsUnit.unit       ([≡]-isUnit {A = A}) = uniqueness(A)
IsUnit.uniqueness ([≡]-isUnit {A = A} ⦃ mere-A ⦄ {x = x} {y = y}) {p} i = Interval.hComp d p where
  d : Interval → Interval.Partial (Interval.max (Interval.flip i) i) (Path x y)
  d j (i = Interval.𝟎) = p
  d j (i = Interval.𝟏) = {!uniqueness(A) {x}{y}!}
-- congruence₁ (prop ↦ MereProposition.uniqueness prop {x}{y}) (IsUnit.uniqueness prop-is-prop-unit {intro (\{x y} → {!p!})})
-}


open import Type.Properties.Homotopy
data HTrunc₁(A : Type{ℓ}) : Type{ℓ} where
  trunc : A → HTrunc₁(A)
  trunc-proof : HomotopyLevel(1) (HTrunc₁(A))

instance
  HTrunc₁-prop : MereProposition(HTrunc₁(A))
  HTrunc₁-prop = intro trunc-proof

module _ ⦃ prop : MereProposition(B) ⦄ where
  HTrunc₁-function : (A → B) → (HTrunc₁(A) → B)
  HTrunc₁-function f (trunc a)              = f(a)
  HTrunc₁-function f (trunc-proof {x}{y} i) = uniqueness(B) {HTrunc₁-function f x} {HTrunc₁-function f y} i

module _ {P : HTrunc₁(A) → Type{ℓ}} ⦃ prop-p : ∀{a} → MereProposition(P(a)) ⦄ where
  HTrunc₁-elim : (∀{x} → P(trunc x)) → (∀{a} → P(a))
  HTrunc₁-elim axpx {a} = HTrunc₁-function (x ↦ substitute₁(P) (uniqueness(HTrunc₁(A)) {trunc x}{a}) axpx) a

[∨trunc]-introₗ : A → HTrunc₁(A ∨ B)
[∨trunc]-introₗ a = trunc([∨]-introₗ a)

[∨trunc]-introᵣ : B → HTrunc₁(A ∨ B)
[∨trunc]-introᵣ b = trunc([∨]-introᵣ b)

[∨trunc]-elim : ⦃ prop-C : MereProposition(C) ⦄ → (A → C) → (B → C) → HTrunc₁(A ∨ B) → C
[∨trunc]-elim = HTrunc₁-function ∘₂ [∨]-elim

private variable Obj : Type{ℓ}
private variable Pred : Obj → Type{ℓ}

[∃trunc]-intro : (witness : Obj) → ⦃ proof : Pred(witness) ⦄ → HTrunc₁(∃(Pred))
[∃trunc]-intro witness ⦃ proof ⦄ = trunc ([∃]-intro witness ⦃ proof ⦄)

[∃trunc]-elim : ⦃ prop-A : MereProposition(A) ⦄ → (∀{x : Obj} → Pred(x) → A) → HTrunc₁(∃(Pred)) → A
[∃trunc]-elim = HTrunc₁-function ∘ [∃]-elim

open import Structure.Setoid.Uniqueness
open import Type.Dependent

-- TODO
-- ∀{eu₁ eu₂ : ∃!{Obj = Obj}(Pred)} → () → (eu₁ ≡ eu₂)

{-
Unique-MereProposition-equivalence : ⦃ prop : ∀{x} → MereProposition(P(x)) ⦄ → (Unique(P) ↔ MereProposition(∃ P))
Unique-MereProposition-equivalence {P = P} = [↔]-intro l r where
  l : Unique(P) ← MereProposition(∃ P)
  l (intro p) {x} {y} px py = mapP([∃]-witness) (p{[∃]-intro x ⦃ px ⦄} {[∃]-intro y ⦃ py ⦄})
  r : Unique(P) → MereProposition(∃ P)
  MereProposition.uniqueness (r p) {[∃]-intro w₁ ⦃ p₁ ⦄} {[∃]-intro w₂ ⦃ p₂ ⦄} i = mapP (mapP (\w p → [∃]-intro w ⦃ p ⦄) (p p₁ p₂) i) {!!} i
  -- mapP [∃]-intro (p p₁ p₂) i ⦃ {!!} ⦄

Unique-prop : ⦃ prop : ∀{x} → MereProposition(P(x)) ⦄ → MereProposition(Unique(P))
MereProposition.uniqueness Unique-prop {u₁} {u₂} i {x} {y} px py j = Interval.hComp d x where
  d : Interval → Interval.Partial (Interval.max (Interval.max (Interval.flip i) i) (Interval.max (Interval.flip j) j)) A
  d k (i = Interval.𝟎) = {!!}
  d k (i = Interval.𝟏) = {!!}
  d k (j = Interval.𝟎) = {!!}
  d k (j = Interval.𝟏) = {!!}

[∃!trunc]-to-existence : ⦃ prop : ∀{x} → MereProposition(Pred(x)) ⦄ → HTrunc₁(∃!{Obj = Obj}(Pred)) → HomotopyLevel(0)(∃{Obj = Obj}(Pred))
[∃!trunc]-to-existence {Pred = Pred} (trunc ([∧]-intro e u)) = intro e (\{e₂} i → [∃]-intro (u ([∃]-proof e₂) ([∃]-proof e) i) ⦃ {!!} ⦄)
-- MereProposition.uniqueness test) {u _ _ _}
-- sub₂(_≡_)(_→ᶠ_) ⦃ [≡][→]-sub ⦄ (congruence₁(Pred) ?) ?
[∃!trunc]-to-existence (trunc-proof i) = {!!}
-}

{-
[∃!]-squashed-witness : HTrunc₁(∃!{Obj = Obj}(Pred)) → Obj
[∃!]-squashed-witness (trunc eu) = [∃]-witness([∧]-elimₗ eu)
[∃!]-squashed-witness (trunc-proof {trunc ([∧]-intro e₁ u₁)} {trunc ([∧]-intro e₂ u₂)} i) = u₁ ([∃]-proof e₁) ([∃]-proof e₂) i
[∃!]-squashed-witness (trunc-proof {trunc ([∧]-intro e₁ u₁)} {trunc-proof j} i) = {!!}
[∃!]-squashed-witness (trunc-proof {trunc-proof i₁} {trunc x} i) = {!!}
[∃!]-squashed-witness (trunc-proof {trunc-proof i₁} {trunc-proof i₂} i) = {!!}
-}
data HTrunc₂(A : Type{ℓ}) : Type{ℓ} where
  trunc : A → HTrunc₂(A)
  trunc-proof : HomotopyLevel(2) (HTrunc₂(A))

{- TODO: Does not work because when using a definition like `HomotopyLevel`, it must be normalized to fit as a data variant
open import Numeral.Natural

data HTrunc (n : ℕ) (A : Type{ℓ}) : Type{ℓ} where
  trunc : A → HTrunc(n)(A)
  trunc-proof : HomotopyLevel(n) (HTrunc(n)(A))
-}

data Quotient(_▫_ : T → T → Type{ℓ}) : Type{Lvl.of(T) Lvl.⊔ ℓ} where
  class : T → Quotient(_▫_)
  class-extensionality : (x ▫ y) → (class x ≡ class y)

module _ ⦃ prop-P : ∀{c : Quotient(_▫_)} → MereProposition(P(c)) ⦄ where
  Quotient-property-pathP : ∀{x y}{px : P(x)}{py : P(y)} → (xy : x ≡ y) → PathP(\i → P(xy i)) px py
  Quotient-property-pathP {x}{y}{px}{py} xy = IdentityEliminator.proof [≡]-identity-eliminator (xy ↦ (∀{px}{py} → PathP(\i → P(xy i)) px py)) (\{c} → uniqueness(P(c))) {x}{y} xy {px}{py}

  class-property : (∀{a} → P(class a)) → (∀{c} → P(c))
  class-property p {class a} = p{a}
  class-property p {class-extensionality {x} {y} xy i} = Quotient-property-pathP {px = p{x}}{py = p{y}} (class-extensionality xy) i

{- TODO: Needs something about mere propositions. Surjective uses existence defined as Σ, so it is not a mere proposition
instance
  class-surjective : Trunc(Surjective(class{_▫_ = _▫_}))
  class-surjective {_▫_ = _▫_} = class-property{_▫_ = _▫_} ⦃ intro trunc-squash ⦄ \{x} → trunc(intro([∃]-intro x))
-}

{-
module _ ⦃ equivalence : Equivalence(_▫_) ⦄ ⦃ prop-relator : ∀{x y} → MereProposition(x ▫ y) ⦄ where
  class-extensionality-proof : (class{_▫_ = _▫_} x ≡ class y) → (x ▫ y)
  class-extensionality-proof {x = x} {y = y} p = sub₂(_≡_)(_→ᶠ_) ⦃ [≡][→]-sub ⦄ xxxy (reflexivity(_▫_)) where
    xxxy : (x ▫ x) ≡ (x ▫ y)
    xxxy i = {!!}
-}
