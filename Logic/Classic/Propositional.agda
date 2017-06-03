module Logic.Classic.Propositional where

open import Boolean
open import Data
open import Functional
import      Level as Lvl

-- Propositional logic. Working with propositions and their truth (whether they are true or false).



module ProofSystems {ℓ₁} {ℓ₂} {Prop : Set(ℓ₁)} {Formula : Set(ℓ₁) → Set(ℓ₂)} (symbols : Syntax.Symbols Prop Formula) where
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
    -- Intro rules are like constructors of formulas
    -- Elimination rules are like deconstructors of formulas
    record Rules : Set(Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂)) where
      field
        {Node} : Formula(Prop) → Set(ℓ₁ Lvl.⊔ ℓ₂)

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

    module Meta(rules : Rules) (meta-symbols : Syntax.Symbols (Set(ℓ₁ Lvl.⊔ ℓ₂)) id) where
      open import List
      open        Rules(rules)
      open        Syntax.Symbols(meta-symbols)
        renaming (
          •_ to ◦_ ;
          ⊤   to ⊤ₘ ;
          ⊥   to ⊥ₘ ;
          ¬_  to ¬ₘ_ ;
          _∧_ to _∧ₘ_ ;
          _∨_ to _∨ₘ_ ;
          _⇒_ to _⇒ₘ_ )


      module Theorems where
        open import List.Properties{ℓ₁}{ℓ₂}
        import      List.Theorems
        open        List.Theorems.Sets
        open        List.Theorems.Sets.Relators
        open import Relator.Equals{ℓ₁}{ℓ₂}

        -- [⊢]-subset : (Γ₁ ⊆ Γ₂) → (Γ₁ ⊢ φ) → (Γ₂ ⊢ φ)
        -- [⊢]-subset proof = 
        -- [⊢]-subset : ∀{T}{L₁ L₂ : List(Stmt)} → (L₁ ⊆ L₂) → ∀{X} → (f(L₁) → X) → (f(L₂) → X)

        [⊢]-id : ∀{φ} → ([ φ ] ⊢ φ)
        [⊢]-id = id

        -- [⊢]-lhs-commutativity : ∀{Γ₁ Γ₂}{φ} → ((Γ₁ ++ Γ₂) ⊢ φ) → ((Γ₂ ++ Γ₁) ⊢ φ)
        -- [⊢]-lhs-commutativity = id

        -- [⊢]-test : ∀{φ₁ φ₂ φ₃} → ([ φ₁ ⊰ φ₂ ⊰ φ₃ ] ⊢ φ₁) → (Node(φ₁) ⨯ (Node(φ₂) ⨯ Node(φ₃)) → Node(φ₁))
        -- [⊢]-test = id

        [⊢]-weakening : ∀{Γ}{φ₁} → (Γ ⊢ φ₁) → ∀{φ₂} → ((φ₂ ⊰ Γ) ⊢ φ₁)
        [⊢]-weakening {∅}     (⊢φ₁) (φ₂)      = (⊢φ₁)
        [⊢]-weakening {_ ⊰ _} (Γ⊢φ₁) (φ₂ , Γ) = (Γ⊢φ₁) (Γ)

        -- [⊢]-weakening₂ : ∀{Γ₁}{φ₁} → (Γ₁ ⊢ φ₁) → ∀{Γ₂} → ((Γ₁ ++ Γ₂) ⊢ φ₁)
        -- [⊢]-weakening₂ {Γ₁}{φ₁} (Γ⊢φ₁)  {∅}       = [≡]-elimᵣ {_}{_}{_} [++]-identityₗ {expr ↦ (expr ⊢ φ₁)} Γ⊢φ₁
        -- [⊢]-weakening₂ {Γ₁}{φ₁} (Γ₁⊢φ₁) {φ₂ ⊰ Γ₂} = [⊢]-weakening₂ {Γ₁}{φ₁} ([⊢]-weakening{Γ₁}{φ₁} (Γ₁⊢φ₁) {φ₂}) {Γ₂}

        [⊢]-compose : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ([ φ₁ ] ⊢ φ₂) → (Γ ⊢ φ₂)
        [⊢]-compose {∅}     (φ₁)   (φ₁⊢φ₂)      = (φ₁⊢φ₂) (φ₁)
        [⊢]-compose {_ ⊰ _} (Γ⊢φ₁) (φ₁⊢φ₂) (Γ) = (φ₁⊢φ₂) ((Γ⊢φ₁) (Γ))

        [⊢]-compose₂ : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ φ₂)
        [⊢]-compose₂ {∅}     (φ₁)   (φ₁⊢φ₂)      = (φ₁⊢φ₂)(φ₁)
        [⊢]-compose₂ {_ ⊰ _} (Γ⊢φ₁) (φ₁Γ⊢φ₂) (Γ) = (φ₁Γ⊢φ₂) ((Γ⊢φ₁) (Γ) , (Γ))
        -- [⊢]-test : ∀{φ₁ φ₂ γ₁ γ₂} → ([ γ₁ ⊰ γ₂ ] ⊢ φ₁) → ([ φ₁ ⊰ γ₁ ⊰ γ₂ ] ⊢ φ₂) → ([ γ₁ ⊰ γ₂ ] ⊢ φ₂)
        -- [⊢]-test (Γ⊢φ₁) (φ₁Γ⊢φ₂) (Γ) = (φ₁Γ⊢φ₂) ((Γ⊢φ₁) (Γ) , (Γ))

        -- [⊢]-compose₃ : ∀{Γ₁ Γ₂}{φ₁ φ₂} → (Γ₁ ⊢ φ₁) → ((φ₁ ⊰ Γ₂) ⊢ φ₂) → ((Γ₁ ++ Γ₂) ⊢ φ₂)
        -- [⊢]-compose₃ {∅}    {∅} (φ₁) (φ₁⊢φ₂) = (φ₁⊢φ₂) (φ₁)
        -- [⊢]-compose₃ {_ ⊰ _}{∅} = [⊢]-compose
        -- [⊢]-compose₃ {∅}{∅} (φ₁)   (φ₁⊢φ₂)      = (φ₁⊢φ₂) (φ₁)
        -- [⊢]-compose₃ {Γ}{∅} = [≡]-elimᵣ [++]-identityₗ [⊢]-compose{Γ}
        -- [⊢]-compose₃ {∅}{Γ}  = [⊢]-compose₂{Γ}
        -- [⊢]-compose₃ {_ ⊰ _}{_ ⊰ _}  = [⊢]-compose₂

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
