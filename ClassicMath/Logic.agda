{-# OPTIONS --without-K #-} -- --cubical

module ClassicMath.Logic where

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

module _ {ℓ} where
  ------------------------------------------
  -- Conjunction (AND)

  record _∧_ (X : Prop(ℓ)) (Y : Prop(ℓ)) : Prop(ℓ) where
    instance constructor intro
    field
      ⦃ [∧]-elimₗ ⦄ : X
      ⦃ [∧]-elimᵣ ⦄ : Y
  open _∧_ ⦃ ... ⦄ public

  [∧]-intro : ∀{X Y} → X → Y → (X ∧ Y)
  [∧]-intro x y = _∧_.intro ⦃ x ⦄ ⦃ y ⦄

  ------------------------------------------
  -- Implication

  record _⟶_ (X : Prop(ℓ)) (Y : Prop(ℓ)) : Prop(ℓ) where
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

  record _⟷_ (X : Prop(ℓ)) (Y : Prop(ℓ)) : Prop(ℓ) where
    constructor [⟷]-intro
    field
      [⟷]-elimₗ : Y → X
      [⟷]-elimᵣ : X → Y
  open _⟷_ public

  ------------------------------------------
  -- Disjunction (OR)

  data _∨_ (X : Prop(ℓ)) (Y : Prop(ℓ)) : Prop(ℓ) where
    instance [∨]-introₗ : X → (X ∨ Y)
    instance [∨]-introᵣ : Y → (X ∨ Y)

  [∨]-elim : ∀{X Y Z : Prop(ℓ)} → (X → Z) → (Y → Z) → (X ∨ Y) → Z
  [∨]-elim(f₁) (_) ([∨]-introₗ x) = f₁(x)
  [∨]-elim(_) (f₂) ([∨]-introᵣ y) = f₂(y)

  ------------------------------------------
  -- Bottom (false, absurdity, empty, contradiction)

  data ⊥ : Prop(ℓ) where

  [⊥]-intro : ∀{X : Prop(ℓ)} → X → (X → ⊥) → ⊥
  [⊥]-intro x f = f(x)

  [⊥]-elim : ∀{X : Prop(ℓ)} → ⊥ → X
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

  ------------------------------------------
  -- Universal quantification (FORALL)

  record ∀ₗ {X : Type{ℓ}} (Pred : X → Prop(ℓ)) : Prop(ℓ) where
    instance constructor [∀]-intro
    field
      [∀]-elim : ∀{x : X} → Pred(x)

  ------------------------------------------
  -- Existential quantification (EXISTS)
  record ∃ {ℓ}{X : Type{ℓ}} (Pred : X → Prop(ℓ)) : Prop(Lvl.𝐒(ℓ)) where
    inductive
    instance constructor [∃]-intro
    field
      [∃]-elim : ∀{P : X → Prop(ℓ)} → (∀{x : X} → Pred(x) → P(x)) → ∃(P)

  {-
  record ∃ {ℓ}{X : Type{ℓ}} (Pred : X → Prop(ℓ)) : Prop(ℓ) where
    instance constructor [∃]-intro
    field
      witness   : X
      ⦃ proof ⦄ : Pred(witness)
  -}



  data _≡_ {X : Type{ℓ}} : X → X → Prop(ℓ) where
    instance [≡]-intro : ∀{x : X} → (x ≡ x)

  data _≡ₚ_ {X : Prop(ℓ)} : X → X → Prop(ℓ) where
    instance [≡ₚ]-intro : ∀{x : X} → (x ≡ₚ x)

  [≡ₚ]-all : ∀{P : Prop(ℓ)} → (proof₁ : P) → (proof₂ : P) → (proof₁ ≡ₚ proof₂)
  [≡ₚ]-all _ _ = [≡ₚ]-intro

  [≡]-uip : ∀{T : Type{ℓ}}{x y : T} → (proof₁ : (x ≡ y)) → (proof₂ : (x ≡ y)) → (proof₁ ≡ₚ proof₂)
  [≡]-uip _ _ = [≡ₚ]-intro

module _ {ℓ₁}{ℓ₂} where
  -- Replaces occurrences of an element in a predicate
  [≡]-substitutionₗ : ∀{A : Type{ℓ₁}}{x y : A} → (x ≡ y) → ∀{P : A → Prop(ℓ₂)} → P(y) → P(x)
  [≡]-substitutionₗ [≡]-intro y = y

  -- Replaces occurrences of an element in a predicate
  [≡]-substitutionᵣ : ∀{A : Type{ℓ₁}}{x y : A} → (x ≡ y) → ∀{P : A → Prop(ℓ₂)} → P(x) → P(y)
  [≡]-substitutionᵣ [≡]-intro y = y

  [≡]-functionₗ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}}{f g : X → Y} → (f ≡ g) → (∀{x} → (f(x) ≡ g(x)))
  [≡]-functionₗ [≡]-intro {_} = [≡]-intro

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
