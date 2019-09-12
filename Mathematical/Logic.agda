module Mathematical.Logic where

import      Lang.Irrelevance
import      Lvl
open import Functional
open import Type

{-import      Lvl
open import Logic.Classical{Lvl.𝟎}
open import Logic.Propositional{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎} -- TODO: Is incompatible with without-K?
open import Type{Lvl.𝟎}

instance postulate classical : ∀{P} → Classical(P) -- TODO: There may be a problem assuming this? It could probably be interpreted as: everything is computable

-- postulate [≡]-stmt : ∀{Proof : Stmt}{x y : Proof} → (x ≡ y)


module _ where
  open import Structure.Relator.Equivalence{Lvl.𝟎}
  open import Structure.Relator.Properties{Lvl.𝟎}

  -- Quotient type
  -- data _/_ (T : Type) (_≅_ : T → T → Stmt) ⦃ _ : Equivalence(_≅_) ⦄ : Type where
  --   [_] : (a : T) → (b : T) → ⦃ _ : a ≅ b ⦄ → Quotient(_≅_)

  -- data [_of_] {T : Type} (a : T) (_≅_ : T → T → Stmt) ⦃ _ : Equivalence(_≅_) ⦄ : Type where
  --   intro : (b : T) → ⦃ _ : (a ≅ b) ⦄ → [ a of (_≅_) ]

  -- [_of_] : ∀{T : Type} → T → (_≅_ : T → T → Stmt) → ⦃ _ : Equivalence(_≅_) ⦄ → T → Type
  -- [ x of _≅_ ] y = (x ≅ y)

  -- [≡]-quotient : ∀{T : Type}{_≅_} → ⦃ _ : Equivalence(_≅_) ⦄ → ∀{x y : T} → (x ≅ y) → ([ x of (_≅_) ] ≡ [ y of (_≅_) ])
  -- [≡]-quotient proof = [≡]-function proof
-}

module _ {ℓ₁ ℓ₂} where
  ------------------------------------------
  -- Conjunction (AND)

  record _∧_ (X : Prop(ℓ₁)) (Y : Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
    instance constructor intro
    field
      ⦃ [∧]-elimₗ ⦄ : X
      ⦃ [∧]-elimᵣ ⦄ : Y
  open _∧_ ⦃ ... ⦄ public

  [∧]-intro : ∀{X Y} → X → Y → (X ∧ Y)
  [∧]-intro x y = _∧_.intro ⦃ x ⦄ ⦃ y ⦄

  ------------------------------------------
  -- Implication

  record _⟶_ (X : Prop(ℓ₁)) (Y : Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
    constructor [⟶]-intro
    field
      [⟶]-elim : X → Y
  open _⟶_ public

  ------------------------------------------
  -- Reverse implication

  _⟵_ = swap(_⟶_)

  pattern [⟵]-intro = [⟶]-intro

  [⟵]-elim = [⟶]-elim

  ------------------------------------------
  -- Equivalence

  record _⟷_ (X : Prop(ℓ₁)) (Y : Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
    constructor [⟷]-intro
    field
      [⟷]-elimₗ : Y → X
      [⟷]-elimᵣ : X → Y
  open _⟷_ public

  ------------------------------------------
  -- Disjunction (OR)

  data _∨_ (X : Prop(ℓ₁)) (Y : Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
    instance [∨]-introₗ : X → (X ∨ Y)
    instance [∨]-introᵣ : Y → (X ∨ Y)

  [∨]-elim : ∀{ℓ₃}{X}{Y}{Z : Prop(ℓ₃)} → (X → Z) → (Y → Z) → (X ∨ Y) → Z
  [∨]-elim(f₁) (_) ([∨]-introₗ x) = f₁(x)
  [∨]-elim(_) (f₂) ([∨]-introᵣ y) = f₂(y)

module _ {ℓ} where
  ------------------------------------------
  -- Bottom (false, absurdity, empty, contradiction)

  data ⊥ : Prop(ℓ) where

  [⊥]-intro : ∀{ℓ₂}{X : Prop(ℓ₂)} → X → (X → ⊥) → ⊥
  [⊥]-intro x f = f(x)

  [⊥]-elim : ∀{ℓ₂}{X : Prop(ℓ₂)} → ⊥ → X
  [⊥]-elim()

  ------------------------------------------
  -- Top (true, truth, unit, validity)

  data ⊤ : Prop(ℓ) where
    instance [⊤]-intro : ⊤

  ------------------------------------------
  -- Negation

  record ¬_ (X : Prop(ℓ)) : Prop(ℓ) where
    constructor [¬]-intro
    field
      [¬]-elim : X → ⊥
  open ¬_ public

module _ {ℓ₁ ℓ₂} where
  ------------------------------------------
  -- Universal quantification (FORALL)
  record ∀ₗ {X : Type{ℓ₁}} (Pred : X → Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
    instance constructor [∀]-intro
    field
      [∀]-elim : (x : X) → Pred(x)
  open ∀ₗ public

  ------------------------------------------
  -- Existential quantification (EXISTS)
  data ∃ {X : Type{ℓ₁}} (Pred : X → Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ Lvl.𝐒(ℓ₂)) where
    [∃]-intro : (x : X) → ⦃ _ : Pred(x) ⦄ → ∃(Pred)

  record Filter {X : Type{ℓ₁}} (P : X → Prop(ℓ₂)) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
    instance constructor intro
    field
      obj : X
      ⦃ proof ⦄ : P(obj)

  Filter-to-[∃] : ∀{X : Type{ℓ₁}}{P : X → Prop(ℓ₂)} → Filter(P) → ∃(P)
  Filter-to-[∃] (intro obj ⦃ proof ⦄) = [∃]-intro obj ⦃ proof ⦄

  -- .[∃]-witness : ∀{X : Type{ℓ₁}}{P : X → Prop(ℓ₂)} → ∃(P) → X
  -- [∃]-witness ([∃]-intro x) = Lang.Irrelevance.axiom(x)

  -- [∃]-to-Filter : ∀{X : Type{ℓ₁}}{P : X → Prop(ℓ₂)} → ∃(P) → Filter(P)
  -- [∃]-to-Filter ([∃]-intro obj ⦃ proof ⦄) = intro obj ⦃ proof ⦄

module _ {ℓ₁ ℓ₂ ℓ₃} where
  [∃]-elim : ∀{X : Type{ℓ₁}}{P : X → Prop(ℓ₂)}{Q : Prop(ℓ₃)} → (∀{x : X} → P(x) → Q) → ∃(P) → Q
  [∃]-elim f ([∃]-intro x ⦃ px ⦄) = f{x}(px)

module _ {ℓ₁ ℓ₂ ℓ₃} where
  [∃]-map : ∀{X : Type{ℓ₁}}{P : X → Prop(ℓ₂)}{Q : X → Prop(ℓ₃)} → (∀{x : X} → P(x) → Q(x)) → ∃(P) → ∃(Q)
  [∃]-map f ([∃]-intro x ⦃ px ⦄) = [∃]-intro x ⦃ f{x}(px) ⦄

module _ {ℓ} where
  -- Equality of objects (type inhabitants) of the same type
  data _≡_ {X : Type{ℓ}} : X → X → Prop(ℓ) where
    instance [≡]-intro : ∀{x : X} → (x ≡ x)

  -- Equality of objects (type inhabitants) of any types in the same universe
  data _≋_ : ∀{X : Type{ℓ}}{Y : Type{ℓ}} → X → Y → Prop(Lvl.𝐒(ℓ)) where
    instance [≋]-intro : ∀{X}{x : X} → (x ≋ x)

  -- Equality of proofs in an universe with propositions
  data _≡ₚ_ : ∀{X : Prop(ℓ)}{Y : Prop(ℓ)} → X → Y → Prop(Lvl.𝐒(ℓ)) where
    instance [≡ₚ]-intro : ∀{X}{x : X} → (x ≡ₚ x)

  [≡]-to-[≋] : ∀{X}{x y : X} → (x ≡ y) → (x ≋ y)
  [≡]-to-[≋] [≡]-intro = [≋]-intro

module _ {ℓ} where
  [≋]-same-type : ∀{X Y : Type{ℓ}}{x : X}{y : Y} → (x ≋ y) → (X ≡ Y)
  [≋]-same-type [≋]-intro = [≡]-intro

  -- TODO: Is there a way to make the type system know that (X = Y) holds so that x and y have the same type?
  -- [≋]-to-[≡] : ∀{X Y}{x : X}{y : Y} → (proof : x ≋ y) → let [≡]-intro = [≋]-same-type proof in (x ≡ y)
  -- [≋]-to-[≡] [≋]-intro = [≡]-intro

module _ {ℓ} where
  -- Uniqueness of proofs of the same proposition
  [≡ₚ]-all : ∀{P : Prop(ℓ)} → (proof₁ : P) → (proof₂ : P) → (proof₁ ≡ₚ proof₂)
  [≡ₚ]-all _ _ = [≡ₚ]-intro

  -- Uniqueness of proofs of the same proposition
  -- TODO: This gives a compiler error
  -- [≡ₚ]-same-proposition : ∀{P Q : Prop(ℓ)}{proof₁ : P}{proof₂ : Q} → (proof₁ ≡ₚ proof₂) → (P ≡ Q)
  -- [≡ₚ]-same-proposition [≡ₚ]-intro = [≡]-intro

  -- Uniqueness of identity proofs
  [≡ₚ]-uip : ∀{T : Type{ℓ}}{x y : T} → (proof₁ : (x ≡ y)) → (proof₂ : (x ≡ y)) → (proof₁ ≡ₚ proof₂)
  [≡ₚ]-uip = [≡ₚ]-all

module _ {ℓ₁}{ℓ₂} where
  -- Replaces occurrences of an element in a predicate
  [≡]-substitutionₗ : ∀{A : Type{ℓ₁}}{x y : A} → (x ≡ y) → ∀{P : A → Prop(ℓ₂)} → P(y) → P(x)
  [≡]-substitutionₗ [≡]-intro y = y

  -- Replaces occurrences of an element in a predicate
  [≡]-substitutionᵣ : ∀{A : Type{ℓ₁}}{x y : A} → (x ≡ y) → ∀{P : A → Prop(ℓ₂)} → P(x) → P(y)
  [≡]-substitutionᵣ [≡]-intro y = y

  [≡]-functionₗ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}}{f g : X → Y} → (f ≡ g) → (∀{x} → (f(x) ≡ g(x)))
  [≡]-functionₗ [≡]-intro {_} = [≡]-intro

module _ {ℓ} where
  IsUnit : Type{ℓ} → Prop(Lvl.𝐒(ℓ))
  IsUnit(T) = ∃(unit ↦ ∀{x : T} → (x ≡ unit))

module _ {ℓ₁}{ℓ₂} where
  Unapply : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}} → (f : X → Y) → (y : Y) → Type{ℓ₁ Lvl.⊔ ℓ₂}
  Unapply f(y) = Filter(obj ↦ f(obj) ≡ y)

  Bijective : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}} → (X → Y) → Prop(Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂))
  Bijective(f) = ∀ₗ(y ↦ IsUnit(Unapply f(y)))

  -- TODO: Because one cannot take out x in these situations, it becomes more tedious to work with Prop
  -- .inv : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}} → (f : X → Y) → . ⦃ _ : Bijective(f) ⦄ → (Y → X)
  -- inv f ⦃ all ⦄ (y) = Lang.Irrelevance.axiom([∀]-elim all y)
  -- inv f ⦃ [∀]-intro(proof) ⦄ (y) with proof{y}
  -- ... | [∃]-intro (intro x) = Lang.Irrelevance.axiom x

-- ∀{y : Y} → ∃(unit ↦ ∀{x : Filter(obj ↦ f(obj) ≡ y)} → (x ≡ unit))

  _≍_ : Type{ℓ₁} → Type{ℓ₂} → Prop(Lvl.𝐒(Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂)))
  X ≍ Y = ∃(Bijective{X}{Y})



-- ∃((f : X → Y) ↦ ∀{y : Y} → ∃(unit ↦ ∀{x : Filter(obj ↦ f(obj) ≡ y)} → (x ≡ unit)))

  -- [↔]-to-[≍] : ∀{P : Prop(ℓ₁)}{Q : Prop(ℓ₂)} → (P ↔ Q) → (P ≡ₚ Q)
  -- [↔]-to-[≍] (pq) = 

  -- [↔]-to-[≡ₚ] : ∀{P : Prop(ℓ₁)}{Q : Prop(ℓ₂)} → (P ↔ Q) → (P ≡ₚ Q)
  -- [↔]-to-[≡ₚ] (pq) = 

module _ {ℓ₁}{ℓ₂} where
  postulate [≡]-functionᵣ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}}{f g : X → Y} → (∀{x} → (f(x) ≡ g(x))) → (f ≡ g)

module _ {ℓₗ ℓₒ} where
  -- Filtered "subset" type
  record Filter (T : Type{ℓₒ}) (P : T → Prop(ℓₗ)) : Type{ℓₗ Lvl.⊔ ℓₒ} where
    constructor intro
    field
      element   : T
      ⦃ proof ⦄ : P(element)

  record Reflexivity {T : Type{ℓₒ}} (_≅_ : T → T → Prop(ℓₗ)) : Prop(ℓₗ Lvl.⊔ ℓₒ) where
    constructor intro
    field
      reflexivity : ∀{x : T} → (x ≅ x)
  open Reflexivity ⦃ ... ⦄ public

  record Symmetry {T : Type{ℓₒ}} (_≅_ : T → T → Prop(ℓₗ)) : Prop(ℓₗ Lvl.⊔ ℓₒ) where
    constructor intro
    field
      symmetry : ∀{x y : T} → (x ≅ y) → (y ≅ x)
  open Symmetry ⦃ ... ⦄ public

  record Transitivity {T : Type{ℓₒ}} (_≅_ : T → T → Prop(ℓₗ)) : Prop(ℓₗ Lvl.⊔ ℓₒ) where
    constructor intro
    field
      transitivity : ∀{x y z : T} → (x ≅ y) → (y ≅ z) → (x ≅ z)
  open Transitivity ⦃ ... ⦄ public

  record Equivalence {T : Type{ℓₒ}} (_≅_ : T → T → Prop(ℓₗ)) : Prop(ℓₗ Lvl.⊔ ℓₒ) where
    constructor intro
    field
      ⦃ reflexivity ⦄  : Reflexivity (_≅_)
      ⦃ symmetry ⦄     : Symmetry    (_≅_)
      ⦃ transitivity ⦄ : Transitivity(_≅_)

  -- Quotient type (TODO: Does not work)
  -- data _/_ (T : Type{ℓₒ}) (_≅_ : T → T → Prop(ℓₗ)) ⦃ _ : Equivalence(_≅_) ⦄ : Type{ℓₗ Lvl.⊔ ℓₒ} where
  --   [_] : (a : T) → (b : T) → .⦃ _ : (a ≅ b) ⦄ → (T / (_≅_))

  -- eqClass-reflexive : ∀{T : Type{ℓₒ}}{_≅_} → ⦃ _ : Equivalence(_≅_) ⦄ → T → (T / (_≅_))
  -- eqClass-reflexive(a) = [ a ] (a) ⦃ reflexivity ⦄

  -- eqClass-symmetric : ∀{T : Type{ℓₒ}}{_≅_} → ⦃ _ : Equivalence(_≅_) ⦄ → (T / (_≅_)) → (T / (_≅_))
  -- eqClass-symmetric ([ a ] (b) ⦃ proof ⦄) = [ b ] (a) ⦃ symmetry proof ⦄

  -- [≡]-quotient-test : ∀{T : Type{ℓₒ}}{_≅_} → ⦃ _ : Equivalence(_≅_) ⦄ → ∀{x y : T} → (x ≅ y) → ([ x ] (y) ≡ [ y ] (x))
  -- [≡]-quotient-test proof = [≡]-functionᵣ proof



  -- postulate [_of_] : ∀{T : Type{ℓₒ}} → T → (_≅_ : T → T → Prop(ℓₗ)) → ⦃ _ : Equivalence(_≅_) ⦄ → Type{ℓₗ Lvl.⊔ ℓₒ}
  -- postulate [≡]-eqClass : ∀{T : Type{ℓₒ}}{_≅_} → ⦃ _ : Equivalence(_≅_) ⦄ → ∀{x y : T} → (x ≅ y) ⟷ ([ x of (_≅_) ] ≡ [ y of (_≅_) ])
  -- data _/_ (T : Type{ℓₒ}) (_≅_ : T → T → Prop(ℓₗ)) ⦃ _ : Equivalence(_≅_) ⦄ : Type{ℓₗ Lvl.⊔ ℓₒ} where
  --   intro : ∀{x} → [ x of (_≅_) ] → (T / (_≅_))
