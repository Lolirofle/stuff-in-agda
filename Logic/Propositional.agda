module Logic.Propositional where

open import Data
open import Functional
import      Level as Lvl
open import Relator.Equals(Lvl.𝟎)

-- Propositional logic. Working with propositions and their truth (whether they are true or false).

module Syntax where
  record Symbols {lvl₁} {lvl₂} (Stmt : Set(lvl₁)) (Formula : Set(lvl₁) → Set(lvl₂)) : Set(lvl₁ Lvl.⊔ lvl₂) where
    infixl 1011 •_
    infixl 1010 ¬_
    infixl 1005 _∧_
    infixl 1004 _∨_ _⊕_
    infixl 1000 _⇐_ _⇔_ _⇒_

    field
      •_ : Stmt → Formula(Stmt)
      ⊤ : Formula(Stmt)
      ⊥ : Formula(Stmt)
      ¬_ : Formula(Stmt) → Formula(Stmt)
      _∧_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
      _∨_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
      _⇒_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
      _⇐_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
      _⇔_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
      _⊕_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)

-- Also known as Interpretation, Structure, Model
record Model {lvl} (Stmt : Set(lvl)) : Set(lvl) where
  field
    interpretStmt : Stmt → Bool

module Semantics {lvl₁} {lvl₂} {Stmt : Set(lvl₁)} {Formula : Set(lvl₁) → Set(lvl₂)} (symbols : Syntax.Symbols Stmt Formula) (meta-symbols : Syntax.Symbols (Set(lvl₁ Lvl.⊔ lvl₂)) (const(Set(lvl₁ Lvl.⊔ lvl₂)))) where
  open import List
  open Syntax.Symbols(symbols)
  open Syntax.Symbols(meta-symbols)
    renaming (
      •_ to ◦_ ;
      ⊤   to ⊤ₘ ;
      ⊥   to ⊥ₘ ;
      ¬_  to ¬ₘ_ ;
      _∧_ to _∧ₘ_ ;
      _∨_ to _∨ₘ_ ;
      _⇒_ to _⇒ₘ_ )

  -- TODO: Can this be called a "theory" of propositional logic? So that instances of the type Semantics is the "models" of logic?
  record Theory : Set(Lvl.𝐒(lvl₁ Lvl.⊔ lvl₂)) where
    field -- Definitions
      {_⊧_} : Model(Stmt) → Formula(Stmt) → Set(lvl₁ Lvl.⊔ lvl₂)
    field -- Axioms
      [•]-satisfaction : ∀{𝔐 : Model(Stmt)}{stmt : Stmt} → (Model.interpretStmt 𝔐 stmt ≡ 𝑇) → ◦(𝔐 ⊧ (• stmt))
      [⊤]-satisfaction : ∀{𝔐 : Model(Stmt)} → ◦(𝔐 ⊧ ⊤)
      [⊥]-satisfaction : ∀{𝔐 : Model(Stmt)} → ¬ₘ ◦(𝔐 ⊧ ⊥)
      [¬]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ : Formula(Stmt)} → (¬ₘ ◦(𝔐 ⊧ φ)) → ◦(𝔐 ⊧ (¬ φ))
      [∧]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → (◦(𝔐 ⊧ φ₁) ∧ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ∧ φ₂))
      [∨]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → (◦(𝔐 ⊧ φ₁) ∨ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ∨ φ₂))
      [⇒]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → ((¬ₘ ◦(𝔐 ⊧ φ₁)) ∨ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ⇒ φ₂))
    -- TODO: How does the satisfaction definitions look like in constructive logic?

    -- Entailment
    _⊨_ : List(Formula(Stmt)) → Formula(Stmt) → Set(lvl₁ Lvl.⊔ lvl₂)
    _⊨_ Γ φ = (∀{𝔐 : Model(Stmt)} → (List.foldᵣ (_∧ₘ_) (⊤ₘ) (List.map (\γ → ◦(𝔐 ⊧ γ)) Γ)) ⇒ₘ ◦(𝔐 ⊧ φ))

    _⊭_ : List(Formula(Stmt)) → Formula(Stmt) → Set(lvl₁ Lvl.⊔ lvl₂)
    _⊭_ Γ φ = ¬ₘ(_⊨_ Γ φ)

    -- Validity
    valid : Formula(Stmt) → Set(lvl₁ Lvl.⊔ lvl₂)
    valid = (∅ ⊨_)

module ProofSystems {lvl₁} {lvl₂} {Stmt : Set(lvl₁)} {Formula : Set(lvl₁) → Set(lvl₂)} (symbols : Syntax.Symbols Stmt Formula) where
  open Syntax.Symbols(symbols)

  module TruthTables where

  -- The "proofs" that results by these postulates are very much alike the classical notation of natural deduction proofs in written as trees.
  -- A function that has the type (Prop(A) → Prop(B)) is a proof of (A ⊢ B) (A is the assumption, B is the single conclusion)
  -- A function that has the type (Prop(A₁) → Prop(A₂) → Prop(A₃) →  .. → Prop(B)) is a proof of ({A₁,A₂,A₃,..} ⊢ B) (Aᵢ is the assumptions, B is the single result)
  -- A function's function body is the "tree proof"
  -- • The inner most (deepest) expression is at the top of a normal tree
  -- • The outer most (shallow) expression is at the bottom of a normal tree that should result in a construction of the conclusion
  -- One difference is that one cannot introduce assumptions however one wants. There are however rules that allows one to to this by using a function, and can be written as a lambda abstraction if one want it to look similar to the tree proofs.
  module NaturalDeduction where
    open import List

    -- Intro rules are like constructors
    -- Elimination rules are like deconstructors
    module Classic where
      record Rules : Set(Lvl.𝐒(lvl₁ Lvl.⊔ lvl₂)) where
        field
          {Prop} : Formula(Stmt) → Set(lvl₁ Lvl.⊔ lvl₂)

        -- Derivability
        -- Examples:
        --   (∅ ⊢ ⊤) becomes Prop(⊤)
        --   ([ φ ⊰ (¬ φ) ] ⊢ ⊥) becomes (Prop(φ) → (Prop(¬ φ) → Prop(⊥)))
        _⊢_ : List(Formula(Stmt)) → Formula(Stmt) → Set(lvl₁ Lvl.⊔ lvl₂)
        _⊢_ Γ φ = (List.foldₗ (_←_) (Prop(φ)) (List.map Prop (List.reverse Γ)))
        -- _⊢_ Γ φ = (Prop(List.foldᵣ (_∧_) (⊤) Γ) → Prop(φ))

        field
          [⊤]-intro : Prop(⊤)

          [⊥]-intro : ∀{φ : Formula(Stmt)} → Prop(φ) → Prop(¬ φ) → Prop(⊥)

          [¬]-intro : ∀{φ : Formula(Stmt)} → (Prop(φ) → Prop(⊥)) → Prop(¬ φ)
          [¬]-elim  : ∀{φ : Formula(Stmt)} → (Prop(¬ φ) → Prop(⊥)) → Prop(φ)

          [∧]-intro : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₁) → Prop(φ₂) → Prop(φ₁ ∧ φ₂)
          [∧]-elimₗ  : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₁ ∧ φ₂) → Prop(φ₁)
          [∧]-elimᵣ  : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₁ ∧ φ₂) → Prop(φ₂)

          [∨]-introₗ : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₁) → Prop(φ₁ ∨ φ₂)
          [∨]-introᵣ : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₂) → Prop(φ₁ ∨ φ₂)
          [∨]-elim  : ∀{φ₁ φ₂ φ₃ : Formula(Stmt)} → (Prop(φ₁) → Prop(φ₃)) → (Prop(φ₂) → Prop(φ₃)) → Prop(φ₁ ∨ φ₂) → Prop(φ₃)

          [⇒]-intro : ∀{φ₁ φ₂ : Formula(Stmt)} → (Prop(φ₁) → Prop(φ₂)) → Prop(φ₁ ⇒ φ₂)
          [⇒]-elim  : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₁ ⇒ φ₂) → Prop(φ₁) → Prop(φ₂)

          [⇐]-intro : ∀{φ₁ φ₂ : Formula(Stmt)} → (Prop(φ₂) → Prop(φ₁)) → Prop(φ₁ ⇐ φ₂)
          [⇐]-elim : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₁ ⇐ φ₂) → Prop(φ₂) → Prop(φ₁)

          [⇔]-intro : ∀{φ₁ φ₂ : Formula(Stmt)} → (Prop(φ₂) → Prop(φ₁)) → (Prop(φ₁) → Prop(φ₂)) → Prop(φ₁ ⇔ φ₂)
          [⇔]-elimₗ : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₁ ⇔ φ₂) → Prop(φ₂) → Prop(φ₁)
          [⇔]-elimᵣ : ∀{φ₁ φ₂ : Formula(Stmt)} → Prop(φ₁ ⇔ φ₂) → Prop(φ₁) → Prop(φ₂)

        -- Double negated proposition is positive
        [¬¬]-elim : ∀{φ : Formula(Stmt)} → Prop(¬ (¬ φ)) → Prop(φ)
        [¬¬]-elim nna = [¬]-elim(na ↦ [⊥]-intro na nna)

        [⊥]-elim : ∀{φ : Formula(Stmt)} → Prop(⊥) → Prop(φ)
        [⊥]-elim bottom = [¬]-elim(_ ↦ bottom)

      module Meta(rules : Rules) (meta-symbols : Syntax.Symbols (Set(lvl₁ Lvl.⊔ lvl₂)) (const(Set(lvl₁ Lvl.⊔ lvl₂)))) where
        open Rules(rules) using (_⊢_) public
        open Syntax.Symbols(meta-symbols)
          renaming (
            •_ to ◦_ ;
            ⊤   to ⊤ₘ ;
            ⊥   to ⊥ₘ ;
            ¬_  to ¬ₘ_ ;
            _∧_ to _∧ₘ_ ;
            _∨_ to _∨ₘ_ ;
            _⇒_ to _⇒ₘ_ )

        _⊬_ : List(Formula(Stmt)) → Formula(Stmt) → Set(lvl₁ Lvl.⊔ lvl₂)
        _⊬_ Γ φ = ¬ₘ(_⊢_ Γ φ)

        -- Consistency
        inconsistent : List(Formula(Stmt)) → Set(lvl₁ Lvl.⊔ lvl₂)
        inconsistent Γ = (Γ ⊢ ⊥)

        consistent : List(Formula(Stmt)) → Set(lvl₁ Lvl.⊔ lvl₂)
        consistent Γ = ¬ₘ(inconsistent Γ)

      module Theorems(rules : Rules) where
        open Rules(rules)

        -- Ensures that a certain proof is a certain proposition
        -- (Like type ascription, ensures that a certain expression has a certain type)
        -- Example:
        --   (A :with: a) where a : Prop(A)
        --   ((A ∧ B) :with: [∧]-intro a b) where a : Prop(A), b : Prop(B)
        _:with:_ : ∀(φ : Formula(Stmt)) → Prop(φ) → Prop(φ)
        _:with:_ _ x = x
        infixl 100 _:with:_

        -- The ability to derive anything from a contradiction
        ex-falso-quodlibet : ∀{A : Formula(Stmt)} → [ ⊥ ] ⊢ A
        ex-falso-quodlibet = [⊥]-elim

        [∧]-commutativity : ∀{A B : Formula(Stmt)} → Prop(A ∧ B) → Prop(B ∧ A)
        [∧]-commutativity {A} {B} A∧B =
          ((B ∧ A) :with: [∧]-intro
            (B :with: [∧]-elimᵣ(A∧B))
            (A :with: [∧]-elimₗ(A∧B))
          )

        [∨]-commutativity : ∀{A B : Formula(Stmt)} → Prop(A ∨ B) → Prop(B ∨ A)
        [∨]-commutativity {A} {B} A∨B =
          ((B ∨ A) :with: [∨]-elim
            [∨]-introᵣ
            [∨]-introₗ
            A∨B
          )

        contrapositive : ∀{A B : Formula(Stmt)} → Prop(A ⇒ B) → Prop((¬ B) ⇒ (¬ A))
        contrapositive {A} {B} A→B =
          ((¬ B) ⇒ (¬ A)) :with: [⇒]-intro(nb ↦
            (¬ A) :with: [¬]-intro(a ↦
              ⊥ :with: [⊥]-intro
                (B     :with: [⇒]-elim (A→B) a)
                ((¬ B) :with: nb)
            )
          )

        [⇒]-syllogism : ∀{A B C : Formula(Stmt)} → Prop(A ⇒ B) → Prop(B ⇒ C) → Prop(A ⇒ C)
        [⇒]-syllogism {A} {B} {C} A→B B→C =
          ([⇒]-intro(a ↦
            ([⇒]-elim
              B→C
              ([⇒]-elim A→B a)
            )
          ))

        [∨]-syllogism : ∀{A B : Formula(Stmt)} → Prop(A ∨ B) → Prop((¬ A) ⇒ B)
        [∨]-syllogism {A} {B} A∨B =
          ([∨]-elim
            (a ↦ ((¬ A) ⇒ B) :with: [⇒]-syllogism
              (((¬ A) ⇒ (¬ (¬ B))) :with: contrapositive
                (((¬ B) ⇒ A) :with: [⇒]-intro(_ ↦ a))
              )
              (((¬ (¬ B)) ⇒ B) :with: [⇒]-intro [¬¬]-elim)
            )
            (b ↦ ((¬ A) ⇒ B) :with: [⇒]-intro(_ ↦ b))
            A∨B
          )

        -- Currying
        [∧]→[⇒]-in-assumption : {X Y Z : Formula(Stmt)} → Prop((X ∧ Y) ⇒ Z) → Prop(X ⇒ (Y ⇒ Z))
        [∧]→[⇒]-in-assumption x∧y→z =
          ([⇒]-intro(x ↦
            ([⇒]-intro(y ↦
              ([⇒]-elim
                (x∧y→z)
                ([∧]-intro x y)
              )
            ))
          ))

        -- Uncurrying
        [∧]←[⇒]-in-assumption : {X Y Z : Formula(Stmt)} → Prop(X ⇒ (Y ⇒ Z)) → Prop((X ∧ Y) ⇒ Z)
        [∧]←[⇒]-in-assumption x→y→z =
          ([⇒]-intro(x∧y ↦
            ([⇒]-elim
              ([⇒]-elim
                (x→y→z)
                ([∧]-elimₗ x∧y)
              )
              ([∧]-elimᵣ x∧y)
            )
          ))

        -- It is either that a proposition is true or its negation is true.
        -- A proposition is either true or false.
        -- There is no other truth values than true and false.
        excluded-middle : ∀{A : Formula(Stmt)} → Prop(A ∨ (¬ A))
        excluded-middle {A} =
          ([¬]-elim(¬[a∨¬a] ↦
            (⊥ :with: [⊥]-intro
              ((A ∨ (¬ A)) :with: [∨]-introᵣ
                ((¬ A) :with: [¬]-intro(a ↦
                  (⊥ :with: [⊥]-intro
                    ((A ∨ (¬ A))    :with: [∨]-introₗ(a))
                    ((¬(A ∨ (¬ A))) :with: ¬[a∨¬a])
                  )
                ))
              )
              (¬[a∨¬a])
            )
          ))

        -- It cannot be that a proposition is true and its negation is true at the same time.
        -- A proposition cannot be true and false at the same time.
        non-contradiction : ∀{A : Formula(Stmt)} → Prop(¬ (A ∧ (¬ A)))
        non-contradiction {A} =
          ([¬]-intro(a∧¬a ↦
            (⊥ :with: [⊥]-intro
              (A     :with: [∧]-elimₗ a∧¬a)
              ((¬ A) :with: [∧]-elimᵣ a∧¬a)
            )
          ))

        -- TODO: Mix of excluded middle and non-contradiction: (A ⊕ (¬ A))

        -- The standard proof technic: Assume the opposite of the conclusion and prove that it leads to a contradiction
        proof-by-contradiction : ∀{A B : Formula(Stmt)} → (Prop(¬ A) → Prop(B)) → (Prop(¬ A) → Prop(¬ B)) → Prop(A)
        proof-by-contradiction {A} {B} ¬a→b ¬a→¬b =
          (A :with: [¬]-elim(¬a ↦
            (⊥ :with: [⊥]-intro
              (B     :with: ¬a→b(¬a))
              ((¬ B) :with: ¬a→¬b(¬a))
            )
          ))

        peirce : ∀{A B : Formula(Stmt)} → Prop((A ⇒ B) ⇒ A) → Prop(A)
        peirce {A} {B} [A→B]→A =
          (A :with: [¬]-elim(¬a ↦
            ([⊥]-intro
              (A :with: [⇒]-elim
                [A→B]→A
                ((A ⇒ B) :with: [⇒]-intro(a ↦
                  (B :with: [⊥]-elim
                    ([⊥]-intro
                      a
                      ¬a
                    )
                  )
                ))
              )
              ((¬ A) :with: ¬a)
            )
          ))

        skip-[⇒]-assumption : ∀{A B : Formula(Stmt)} → (Prop(A ⇒ B) → Prop(A)) → Prop(A)
        skip-[⇒]-assumption A⇒B→A =
          (peirce
            ([⇒]-intro
              (A⇒B→A)
            )
          )
