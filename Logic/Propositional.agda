module Logic.Propositional where

open import Data
import      Level as Lvl
open import Relator.Equals(Lvl.𝟎)

record Syntax (Stmt : Set) (Formula : Set → Set) : Set where
  field
    Prop : Stmt → Formula(Stmt)
    ⊤ : Formula(Stmt)
    ⊥ : Formula(Stmt)
    ¬_ : Formula(Stmt) → Formula(Stmt)
    _∧_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _∨_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇒_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇐_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇔_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⊕_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
open Syntax

-- Also known as Interpretation, Structure, Model
record Model (Stmt : Set) : Set where
  field
    interpretStmt : Stmt → Bool

-- interpret : ∀{Stmt} → Model(Stmt) → Formula(Stmt) → Bool
-- interpret 𝔐 φ = substitute (interpretStmt 𝔐) φ

InterpretationFn : Set → (Set → Set) → Set
InterpretationFn Stmt Formula = (Model(Stmt) → Formula(Stmt) → Bool)

_⊧_ : ∀{Stmt : Set}{Formula : Set → Set}{_ : InterpretationFn Stmt Formula} → Model(Stmt) → Formula(Stmt) → Set
_⊧_ {_} {_} {interpret} 𝔐 φ = ((interpret 𝔐 φ) ≡ 𝑇)

record Semantics {Stmt : Set}{Formula : Set → Set}{_ : InterpretationFn Stmt Formula} : Set where
  field
    [⊤]-satisfaction : ∀{𝔐 : Model(Stmt)} → (𝔐 ⊧ ⊤)
