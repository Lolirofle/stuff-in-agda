module Logic.Classic lvl where

open import Data
open import Functional
import      Level as Lvl

-- Makes Stmt a non-set (separate from Set(lvl))
postulate Stmt : Set(Lvl.𝐒(lvl))

-- Required because functions only take sets
-- (Because it seems like that _→_ : ∀{lvl} → Set(lvl) → Set(lvl) → Set(lvl) → Set(lvl))
postulate Prop : Stmt → Set(lvl)

-- Logical operators
postulate ⊤ : Stmt
postulate ⊥ : Stmt
postulate ¬_ : Stmt → Stmt
postulate _∧_ : Stmt → Stmt → Stmt
postulate _∨_ : Stmt → Stmt → Stmt
postulate _⇒_ : Stmt → Stmt → Stmt
postulate _⇔_ : Stmt → Stmt → Stmt

_⇐_ : Stmt → Stmt → Stmt
_⇐_ A B = _⇒_ B A

-- Ensures that a certain proof is a certain proposition
-- (Like type ascription, ensures that a certain expression has a certain type)
-- Example:
--   (A :with: a) where a : Prop(A)
--   ((A ∧ B) :with: [∧]-intro a b) where a : Prop(A), b : Prop(B)
_:with:_ : ∀(A : Stmt) → Prop(A) → Prop(A)
_:with:_ _ x = x

_⊢_ : Set(lvl) → Set(lvl) → Set(lvl)
a ⊢ b = a → b -- TODO: Have Prop builtin: a ⊢ b = Prop(a) → Prop(b), and have a (_⨯_) and (_,_)

-- The "proofs" that results by these postulates are very much alike the classical notation of natural deduction proofs in written as trees.
-- A function that has the type (Prop(A) → Prop(B)) is a proof of (A ⊢ B) (A is the assumption, B is the single conclusion)
-- A function that has the type (Prop(A₁) → Prop(A₂) → Prop(A₃) →  .. → Prop(B)) is a proof of ({A₁,A₂,A₃,..} ⊢ B) (Aᵢ is the assumptions, B is the single result)
-- A function's function body is the "tree proof"
-- • The inner most (deepest) expression is at the top of a normal tree
-- • The outer most (shallow) expression is at the bottom of a normal tree that should result in a construction of the conclusion
-- One difference is that one cannot introduce assumptions however one wants. There are however rules that allows one to to this by using a function, and can be written as a lambda abstraction if one want it to look similar to the tree proofs.
module NaturalDeduction where
  -- Intro rules are like constructors
  -- Elimination rules are like deconstructors

  postulate [⊤]-intro : Prop(⊤)

  postulate [⊥]-intro : ∀{A : Stmt} → Prop(A) → Prop(¬ A) ⊢ Prop(⊥)

  postulate [¬]-intro : ∀{A : Stmt} → (Prop(A) → Prop(⊥)) ⊢ Prop(¬ A)
  postulate [¬]-elim  : ∀{A : Stmt} → (Prop(¬ A) → Prop(⊥)) ⊢ Prop(A)

  postulate [∧]-intro : ∀{A B : Stmt} → Prop(A) → Prop(B) ⊢ Prop(A ∧ B)
  postulate [∧]-elimₗ  : ∀{A B : Stmt} → Prop(A ∧ B) ⊢ Prop(A)
  postulate [∧]-elimᵣ  : ∀{A B : Stmt} → Prop(A ∧ B) ⊢ Prop(B)

  postulate [∨]-introₗ : ∀{A B : Stmt} → Prop(A) ⊢ Prop(A ∨ B)
  postulate [∨]-introᵣ : ∀{A B : Stmt} → Prop(B) ⊢ Prop(A ∨ B)
  postulate [∨]-elim  : ∀{A B C : Stmt} → (Prop(A) → Prop(C)) → (Prop(B) → Prop(C)) → Prop(A ∨ B) ⊢ Prop(C)

  postulate [⇒]-intro : ∀{A B : Stmt} → (Prop(A) → Prop(B)) ⊢ Prop(A ⇒ B)
  postulate [⇒]-elim  : ∀{A B : Stmt} → Prop(A ⇒ B) → Prop(A) ⊢ Prop(B)

  module Theorems where
    -- Double negated proposition is positive
    [¬¬]-elim : ∀{A : Stmt} → Prop(¬ (¬ A)) ⊢ Prop(A)
    [¬¬]-elim nna = [¬]-elim(λ na → [⊥]-intro na nna)

    [⊥]-elim : ∀{A : Stmt} → Prop(⊥) ⊢ Prop(A)
    [⊥]-elim bottom = [¬]-elim (λ _ → bottom)

    -- The ability to derive anything from a contradiction
    ex-falso-quodlibet : ∀{A : Stmt} → Prop(⊥) ⊢ Prop(A)
    ex-falso-quodlibet = [⊥]-elim

    [∧]-commutativity : ∀{A B : Stmt} → Prop(A ∧ B) ⊢ Prop(B ∧ A)
    [∧]-commutativity {A} {B} A∧B =
      ((B ∧ A) :with: [∧]-intro
        (B :with: [∧]-elimᵣ(A∧B))
        (A :with: [∧]-elimₗ(A∧B))
      )

    [∨]-commutativity : ∀{A B : Stmt} → Prop(A ∨ B) ⊢ Prop(B ∨ A)
    [∨]-commutativity {A} {B} A∨B =
      ((B ∨ A) :with: [∨]-elim
        [∨]-introᵣ
        [∨]-introₗ
        A∨B
      )

    contrapositive : ∀{A B : Stmt} → Prop(A ⇒ B) ⊢ Prop((¬ A) ⇐ (¬ B))
    contrapositive {A} {B} A→B =
      ((¬ B) ⇒ (¬ A)) :with: [⇒]-intro(λ nb →
        (¬ A) :with: [¬]-intro(λ a →
          ⊥ :with: [⊥]-intro
            (B     :with: [⇒]-elim (A→B) a)
            ((¬ B) :with: nb)
        )
      )

    [⇒]-syllogism : ∀{A B C : Stmt} → Prop(A ⇒ B) → Prop(B ⇒ C) ⊢ Prop(A ⇒ C)
    [⇒]-syllogism {A} {B} {C} A→B B→C =
      ([⇒]-intro(λ a →
        ([⇒]-elim
          B→C
          ([⇒]-elim A→B a)
        )
      ))

    [∨]-syllogism : ∀{A B : Stmt} → Prop(A ∨ B) ⊢ Prop((¬ A) ⇒ B)
    [∨]-syllogism {A} {B} A∨B =
      ([∨]-elim
        (λ a → ((¬ A) ⇒ B) :with: [⇒]-syllogism
          (((¬ A) ⇒ (¬ (¬ B))) :with: contrapositive
            (((¬ B) ⇒ A) :with: [⇒]-intro(λ _ → a))
          )
          (((¬ (¬ B)) ⇒ B) :with: [⇒]-intro [¬¬]-elim)
        )
        (λ b → ((¬ A) ⇒ B) :with: [⇒]-intro(λ _ → b))
        A∨B
      )

    -- Currying
    [∧]→[⇒]-in-assumption : {X Y Z : Stmt} → Prop((X ∧ Y) ⇒ Z) ⊢ Prop(X ⇒ (Y ⇒ Z))
    [∧]→[⇒]-in-assumption x∧y→z =
      ([⇒]-intro(λ x →
        ([⇒]-intro(λ y →
          ([⇒]-elim
            (x∧y→z)
            ([∧]-intro x y)
          )
        ))
      ))

    -- Uncurrying
    [∧]←[⇒]-in-assumption : {X Y Z : Stmt} → Prop(X ⇒ (Y ⇒ Z)) ⊢ Prop((X ∧ Y) ⇒ Z)
    [∧]←[⇒]-in-assumption x→y→z =
      ([⇒]-intro(λ x∧y →
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
    excluded-middle : ∀{A : Stmt} → Prop(A ∨ (¬ A))
    excluded-middle {A} =
      ([¬]-elim(λ ¬[a∨¬a] →
        (⊥ :with: [⊥]-intro
          ((A ∨ (¬ A)) :with: [∨]-introᵣ
            ((¬ A) :with: [¬]-intro(λ a →
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
    non-contradiction : ∀{A : Stmt} → Prop(¬ (A ∧ (¬ A)))
    non-contradiction {A} =
      ([¬]-intro(λ a∧¬a →
        (⊥ :with: [⊥]-intro
          (A     :with: [∧]-elimₗ a∧¬a)
          ((¬ A) :with: [∧]-elimᵣ a∧¬a)
        )
      ))

    -- TODO: Mix of excluded middle and non-contradiction: (A ⊕ (¬ A))

    -- The standard proof technic: Assume the opposite of the conclusion and prove that it leads to a contradiction
    proof-by-contradiction : ∀{A B : Stmt} → (Prop(¬ A) → Prop(B)) → (Prop(¬ A) → Prop(¬ B)) ⊢ Prop(A)
    proof-by-contradiction {A} {B} ¬a→b ¬a→¬b =
      (A :with: [¬]-elim(λ ¬a →
        (⊥ :with: [⊥]-intro
          (B     :with: ¬a→b(¬a))
          ((¬ B) :with: ¬a→¬b(¬a))
        )
      ))

    peirce : ∀{A B : Stmt} → Prop((A ⇒ B) ⇒ A) ⊢ Prop(A)
    peirce {A} {B} [A→B]→A =
      (A :with: [¬]-elim(λ ¬a →
        ([⊥]-intro
          (A :with: [⇒]-elim
            [A→B]→A
            ((A ⇒ B) :with: [⇒]-intro(λ a →
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

    skip-[⇒]-assumption : ∀{A B : Stmt} → (Prop(A ⇒ B) → Prop(A)) ⊢ Prop(A)
    skip-[⇒]-assumption A⇒B→A =
      (peirce
        ([⇒]-intro
          (A⇒B→A)
        )
      )
