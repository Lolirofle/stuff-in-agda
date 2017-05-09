module Logic.Classic.Propositional where

open import Boolean
open import Data
open import Functional
import      Level as Lvl

-- Propositional logic. Working with propositions and their truth (whether they are true or false).

module Syntax {lvl₁} {lvl₂} (Prop : Set(lvl₁)) (Formula : Set(lvl₁) → Set(lvl₂)) where
  record Symbols : Set(lvl₁ Lvl.⊔ lvl₂) where
    infixl 1011 •_
    infixl 1010 ¬_
    infixl 1005 _∧_
    infixl 1004 _∨_ _⊕_
    infixl 1000 _⇐_ _⇔_ _⇒_

    field
      •_ : Prop → Formula(Prop)
      ⊤ : Formula(Prop)
      ⊥ : Formula(Prop)
      ¬_ : Formula(Prop) → Formula(Prop)
      _∧_ : Formula(Prop) → Formula(Prop) → Formula(Prop)
      _∨_ : Formula(Prop) → Formula(Prop) → Formula(Prop)
      _⇒_ : Formula(Prop) → Formula(Prop) → Formula(Prop)
      _⇐_ : Formula(Prop) → Formula(Prop) → Formula(Prop)
      _⇔_ : Formula(Prop) → Formula(Prop) → Formula(Prop)
      _⊕_ : Formula(Prop) → Formula(Prop) → Formula(Prop)

-- A model decides whether a proposition is true or false
-- Also known as Interpretation, Structure, Model
record Model {lvl} (Prop : Set(lvl)) : Set(lvl) where
  field
    interpretProp : Prop → Bool

module Semantics {lvl₁} {lvl₂} {Prop : Set(lvl₁)} {Formula : Set(lvl₁) → Set(lvl₂)} (symbols : Syntax.Symbols Prop Formula) (meta-symbols : Syntax.Symbols (Set(lvl₁ Lvl.⊔ lvl₂)) id) where
  open import Relator.Equals{lvl₁}{lvl₂}
  open import SimpleSet{lvl₂}{lvl₁}
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
      {_⊧_} : Model(Prop) → Formula(Prop) → Set(lvl₁ Lvl.⊔ lvl₂)
    field -- Axioms
      [•]-satisfaction : ∀{𝔐 : Model(Prop)}{x : Prop} → (Model.interpretProp 𝔐 x ≡ 𝑇) → ◦(𝔐 ⊧ (• x))
      [⊤]-satisfaction : ∀{𝔐 : Model(Prop)} → ◦(𝔐 ⊧ ⊤)
      [⊥]-satisfaction : ∀{𝔐 : Model(Prop)} → ¬ₘ ◦(𝔐 ⊧ ⊥)
      [¬]-satisfaction : ∀{𝔐 : Model(Prop)}{φ : Formula(Prop)} → (¬ₘ ◦(𝔐 ⊧ φ)) → ◦(𝔐 ⊧ (¬ φ))
      [∧]-satisfaction : ∀{𝔐 : Model(Prop)}{φ₁ φ₂ : Formula(Prop)} → (◦(𝔐 ⊧ φ₁) ∧ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ∧ φ₂))
      [∨]-satisfaction : ∀{𝔐 : Model(Prop)}{φ₁ φ₂ : Formula(Prop)} → (◦(𝔐 ⊧ φ₁) ∨ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ∨ φ₂))
      [⇒]-satisfaction : ∀{𝔐 : Model(Prop)}{φ₁ φ₂ : Formula(Prop)} → ((¬ₘ ◦(𝔐 ⊧ φ₁)) ∨ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ⇒ φ₂))
    -- TODO: How does the satisfaction definitions look like in constructive logic?

    -- Entailment
    _⊨_ : SSet(Formula(Prop)) → Formula(Prop) → Set(lvl₁ Lvl.⊔ lvl₂)
    _⊨_ Γ φ = (∀{𝔐 : Model(Prop)} → (∀{γ} → (γ ∈ Γ) → ◦(𝔐 ⊧ γ)) ⇒ₘ ◦(𝔐 ⊧ φ))

    _⊭_ : SSet(Formula(Prop)) → Formula(Prop) → Set(lvl₁ Lvl.⊔ lvl₂)
    _⊭_ Γ φ = ¬ₘ(_⊨_ Γ φ)

    -- Validity
    valid : Formula(Prop) → Set(lvl₁ Lvl.⊔ lvl₂)
    valid = (∅ ⊨_)

module ProofSystems {lvl₁} {lvl₂} {Prop : Set(lvl₁)} {Formula : Set(lvl₁) → Set(lvl₂)} (symbols : Syntax.Symbols Prop Formula) where
  open Syntax.Symbols(symbols)

  module TruthTables where

  -- The "proofs" that results by these postulates are very much alike the classical notation of natural deduction proofs in written as trees.
  -- A function that has the type (Node(A) → Node(B)) is a proof of (A ⊢ B) (A is the assumption, B is the single conclusion)
  -- A function that has the type (Node(A₁) → Node(A₂) → Node(A₃) →  .. → Node(B)) is a proof of ({A₁,A₂,A₃,..} ⊢ B) (Aᵢ is the assumptions, B is the single result)
  -- A function's function body is the "tree proof"
  -- • The inner most (deepest) expression is at the top of a normal tree
  -- • The outer most (shallow) expression is at the bottom of a normal tree that should result in a construction of the conclusion
  -- One difference is that one cannot introduce assumptions however one wants. There are however rules that allows one to to this by using a function, and can be written as a lambda abstraction if one want it to look similar to the tree proofs.
  module NaturalDeduction where
    open import SimpleSet{lvl₂}{lvl₁}

    -- Intro rules are like constructors
    -- Elimination rules are like deconstructors
    module Classic where
      record Rules : Set(Lvl.𝐒(lvl₁ Lvl.⊔ lvl₂)) where
        field
          {Node} : Formula(Prop) → Set(lvl₁ Lvl.⊔ lvl₂)

        -- Derivability
        -- Examples:
        --   (∅ ⊢ ⊥) becomes (Node(⊤) → Node(⊥))
        --   ([ φ ⊰ (¬ φ) ] ⊢ ⊥) becomes ((Node(φ) ∧ Node(¬ φ)) → Node(⊥))
        _⊢_ : SSet(Formula(Prop)) → Formula(Prop) → Set(lvl₁ Lvl.⊔ lvl₂)
        _⊢_ Γ φ = (∀{γ} → {_ : γ ∈ Γ} → Node(γ) → Node(φ))
        --   (∅ ⊢ ⊤) becomes Node(⊤)
        --   ([ φ ⊰ (¬ φ) ] ⊢ ⊥) becomes (Node(φ) → (Node(¬ φ) → Node(⊥)))
        -- _⊢_ Γ φ = (Node(SSet.foldᵣ (_∧_) ⊤ Γ) → Node(φ))
        -- _⊢_ Γ φ = (SSet.foldₗ (_←_) (Node(φ)) (SSet.map Node (SSet.reverse Γ)))

        field
          [⊤]-intro : Node(⊤)

          [⊥]-intro : ∀{φ : Formula(Prop)} → Node(φ) → Node(¬ φ) → Node(⊥)

          [¬]-intro : ∀{φ : Formula(Prop)} → (Node(φ) → Node(⊥)) → Node(¬ φ)
          [¬]-elim  : ∀{φ : Formula(Prop)} → (Node(¬ φ) → Node(⊥)) → Node(φ)

          [∧]-intro : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₁) → Node(φ₂) → Node(φ₁ ∧ φ₂)
          [∧]-elimₗ  : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₁ ∧ φ₂) → Node(φ₁)
          [∧]-elimᵣ  : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₁ ∧ φ₂) → Node(φ₂)

          [∨]-introₗ : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₁) → Node(φ₁ ∨ φ₂)
          [∨]-introᵣ : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₂) → Node(φ₁ ∨ φ₂)
          [∨]-elim  : ∀{φ₁ φ₂ φ₃ : Formula(Prop)} → (Node(φ₁) → Node(φ₃)) → (Node(φ₂) → Node(φ₃)) → Node(φ₁ ∨ φ₂) → Node(φ₃)

          [⇒]-intro : ∀{φ₁ φ₂ : Formula(Prop)} → (Node(φ₁) → Node(φ₂)) → Node(φ₁ ⇒ φ₂)
          [⇒]-elim  : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₁ ⇒ φ₂) → Node(φ₁) → Node(φ₂)

          [⇐]-intro : ∀{φ₁ φ₂ : Formula(Prop)} → (Node(φ₂) → Node(φ₁)) → Node(φ₁ ⇐ φ₂)
          [⇐]-elim : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₁ ⇐ φ₂) → Node(φ₂) → Node(φ₁)

          [⇔]-intro : ∀{φ₁ φ₂ : Formula(Prop)} → (Node(φ₂) → Node(φ₁)) → (Node(φ₁) → Node(φ₂)) → Node(φ₁ ⇔ φ₂)
          [⇔]-elimₗ : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₁ ⇔ φ₂) → Node(φ₂) → Node(φ₁)
          [⇔]-elimᵣ : ∀{φ₁ φ₂ : Formula(Prop)} → Node(φ₁ ⇔ φ₂) → Node(φ₁) → Node(φ₂)

        -- Double negated proposition is positive
        [¬¬]-elim : ∀{φ : Formula(Prop)} → Node(¬ (¬ φ)) → Node(φ)
        [¬¬]-elim nna = [¬]-elim(na ↦ [⊥]-intro na nna)

        [⊥]-elim : ∀{φ : Formula(Prop)} → Node(⊥) → Node(φ)
        [⊥]-elim bottom = [¬]-elim(_ ↦ bottom)

      module Meta(rules : Rules) (meta-symbols : Syntax.Symbols (Set(lvl₁ Lvl.⊔ lvl₂)) id) where
        open Rules(rules) hiding (_⊢_)
        open Rules(rules) using  (_⊢_) public
        open Syntax.Symbols(meta-symbols)
          renaming (
            •_ to ◦_ ;
            ⊤   to ⊤ₘ ;
            ⊥   to ⊥ₘ ;
            ¬_  to ¬ₘ_ ;
            _∧_ to _∧ₘ_ ;
            _∨_ to _∨ₘ_ ;
            _⇒_ to _⇒ₘ_ )

        _⊬_ : SSet(Formula(Prop)) → Formula(Prop) → Set(lvl₁ Lvl.⊔ lvl₂)
        _⊬_ Γ φ = ¬ₘ(_⊢_ Γ φ)

        -- Consistency
        inconsistent : SSet(Formula(Prop)) → Set(lvl₁ Lvl.⊔ lvl₂)
        inconsistent Γ = (Γ ⊢ ⊥)

        consistent : SSet(Formula(Prop)) → Set(lvl₁ Lvl.⊔ lvl₂)
        consistent Γ = ¬ₘ(inconsistent Γ)

        module Theorems where
          -- [⊢]-id : ∀{φ} → (S[ φ ] ⊢ φ)
          -- [⊢]-id = id

          -- [⊢]-compose : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ([ φ₁ ] ⊢ φ₂) → (Γ ⊢ φ₂)
          -- [⊢]-compose proof-Γ⊢φ₁ proof-φ₁⊢φ₂ = (proof-Γ ↦ proof-φ₁⊢φ₂(proof-Γ⊢φ₁ proof-Γ))

          -- [⊢]-compose₂ : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ φ₂)
          -- [⊢]-compose₂ proof-Γ⊢φ₁ proof-φ₁Γ⊢φ₂ = (proof-Γ ↦ proof-φ₁Γ⊢φ₂([∧]-intro (proof-Γ⊢φ₁ proof-Γ) proof-Γ))

          -- [⊢]-weakening : ∀{Γ}{φ₁} → (Γ ⊢ φ₁) → ∀{φ₂} → ((φ₂ ⊰ Γ) ⊢ φ₁)
          -- [⊢]-weakening proof-Γ⊢φ₁ = (proof-φ₂⊰Γ ↦ proof-Γ⊢φ₁ ([∧]-elimᵣ(proof-φ₂⊰Γ)))

          -- olt-9-17 : ∀{Γ}{φ} → (Γ ⊢ φ) → ((φ ⊰ Γ) ⊢ ⊥) → (inconsistent Γ)
          -- olt-9-17 Γ⊢φ Γφ⊢⊥ = (Γ ↦ [⊥]-intro (Γ⊢φ Γ) ([⊥]-elim(Γφ⊢⊥ Γ)))

      module Theorems(rules : Rules) where
        open Rules(rules)

        -- Ensures that a certain proof is a certain proposition
        -- (Like type ascription, ensures that a certain expression has a certain type)
        -- Example:
        --   (A :with: a) where a : Node(A)
        --   ((A ∧ B) :with: [∧]-intro a b) where a : Node(A), b : Node(B)
        _:with:_ : ∀(φ : Formula(Prop)) → Node(φ) → Node(φ)
        _:with:_ _ x = x
        infixl 100 _:with:_

        -- The ability to derive anything from a contradiction
        ex-falso-quodlibet : ∀{A : Formula(Prop)} → Node(⊥) → Node(A)
        ex-falso-quodlibet = [⊥]-elim

        [∧]-commutativity : ∀{A B : Formula(Prop)} → Node(A ∧ B) → Node(B ∧ A)
        [∧]-commutativity {A} {B} A∧B =
          ((B ∧ A) :with: [∧]-intro
            (B :with: [∧]-elimᵣ(A∧B))
            (A :with: [∧]-elimₗ(A∧B))
          )

        [∨]-commutativity : ∀{A B : Formula(Prop)} → Node(A ∨ B) → Node(B ∨ A)
        [∨]-commutativity {A} {B} A∨B =
          ((B ∨ A) :with: [∨]-elim
            [∨]-introᵣ
            [∨]-introₗ
            A∨B
          )

        contrapositive : ∀{A B : Formula(Prop)} → Node(A ⇒ B) → Node((¬ B) ⇒ (¬ A))
        contrapositive {A} {B} A→B =
          ((¬ B) ⇒ (¬ A)) :with: [⇒]-intro(nb ↦
            (¬ A) :with: [¬]-intro(a ↦
              ⊥ :with: [⊥]-intro
                (B     :with: [⇒]-elim (A→B) a)
                ((¬ B) :with: nb)
            )
          )

        [⇒]-syllogism : ∀{A B C : Formula(Prop)} → Node(A ⇒ B) → Node(B ⇒ C) → Node(A ⇒ C)
        [⇒]-syllogism {A} {B} {C} A→B B→C =
          ([⇒]-intro(a ↦
            ([⇒]-elim
              B→C
              ([⇒]-elim A→B a)
            )
          ))

        [∨]-syllogism : ∀{A B : Formula(Prop)} → Node(A ∨ B) → Node((¬ A) ⇒ B)
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
        [∧]→[⇒]-in-assumption : {X Y Z : Formula(Prop)} → Node((X ∧ Y) ⇒ Z) → Node(X ⇒ (Y ⇒ Z))
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
        [∧]←[⇒]-in-assumption : {X Y Z : Formula(Prop)} → Node(X ⇒ (Y ⇒ Z)) → Node((X ∧ Y) ⇒ Z)
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
        excluded-middle : ∀{A : Formula(Prop)} → Node(A ∨ (¬ A))
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
        non-contradiction : ∀{A : Formula(Prop)} → Node(¬ (A ∧ (¬ A)))
        non-contradiction {A} =
          ([¬]-intro(a∧¬a ↦
            (⊥ :with: [⊥]-intro
              (A     :with: [∧]-elimₗ a∧¬a)
              ((¬ A) :with: [∧]-elimᵣ a∧¬a)
            )
          ))

        -- TODO: Mix of excluded middle and non-contradiction: (A ⊕ (¬ A))

        -- The standard proof technic: Assume the opposite of the conclusion and prove that it leads to a contradiction
        proof-by-contradiction : ∀{A B : Formula(Prop)} → (Node(¬ A) → Node(B)) → (Node(¬ A) → Node(¬ B)) → Node(A)
        proof-by-contradiction {A} {B} ¬a→b ¬a→¬b =
          (A :with: [¬]-elim(¬a ↦
            (⊥ :with: [⊥]-intro
              (B     :with: ¬a→b(¬a))
              ((¬ B) :with: ¬a→¬b(¬a))
            )
          ))

        peirce : ∀{A B : Formula(Prop)} → Node((A ⇒ B) ⇒ A) → Node(A)
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

        skip-[⇒]-assumption : ∀{A B : Formula(Prop)} → (Node(A ⇒ B) → Node(A)) → Node(A)
        skip-[⇒]-assumption A⇒B→A =
          (peirce
            ([⇒]-intro
              (A⇒B→A)
            )
          )

{-
data □ : Formula(Prop) → Set where
  Initial   : ∀{φ} → □(φ)
  [∧]-intro : ∀{φ₁ φ₂} → □(φ₁) → □(φ₂) → □(φ₁ ∧ φ₂)
  [∧]-elimₗ  : ∀{φ₁ φ₂} → □(φ₁ ∧ φ₂) → □(φ₁)
  [∧]-elimᵣ  : ∀{φ₁ φ₂} → □(φ₁ ∧ φ₂) → □(φ₂)
  [∨]-introₗ : ∀{φ₁ φ₂} → □(φ₁) → □(φ₁ ∨ φ₂)
  [∨]-introᵣ : ∀{φ₁ φ₂} → □(φ₁) → □(φ₁ ∨ φ₂)
  [∨]-elim  : ∀{φ₁ φ₂ φ₃} → (□(φ₁) → □(φ₃)) → (□(φ₂) → □(φ₃)) → □(φ₃)
  [⇒]-intro : ∀{φ₁ φ₂} → (□(φ₁) → □(φ₂)) → □(φ₁ ⇒ φ₂)
  [⇒]-elim  : ∀{φ₁ φ₂} → □(φ₁ ⇒ φ₂) → □(φ₁) → □(φ₂)
  [¬]-intro : ∀{φ} → (□(φ) → □(⊥)) → □(¬ φ)
  [¬]-elim  : ∀{φ} → (□(¬ φ) → □(⊥)) → □(φ)

data □ : Formula(Prop) → Set where
  Initial   : ∀{φ} → □(φ)
  [∧]-intro : ∀{φ₁ φ₂} → □(φ₁) → □(φ₂) → □(φ₁ ∧ φ₂)
  [∧]-elimₗ  : ∀{φ₁ φ₂} → □(φ₁ ∧ φ₂) → □(φ₁)
  [∧]-elimᵣ  : ∀{φ₁ φ₂} → □(φ₁ ∧ φ₂) → □(φ₂)
  [∨]-introₗ : ∀{φ₁ φ₂} → □(φ₁) → □(φ₁ ∨ φ₂)
  [∨]-introᵣ : ∀{φ₁ φ₂} → □(φ₁) → □(φ₁ ∨ φ₂)
  [∨]-elim  : ∀{φ₁ φ₂ φ₃} → (□(φ₁) → □(φ₃)) → (□(φ₂) → □(φ₃)) → □(φ₃)
  [⇒]-intro : ∀{φ₁ φ₂} → (□(φ₁) → □(φ₂)) → □(φ₁ ⇒ φ₂)
  [⇒]-elim  : ∀{φ₁ φ₂} → □(φ₁ ⇒ φ₂) → □(φ₁) → □(φ₂)
  [¬]-intro : ∀{φ} → (□(φ) → □(⊥)) → □(¬ φ)
  [¬¬]-elim  : ∀{φ} → □(¬(¬ φ)) → □(φ)
-}