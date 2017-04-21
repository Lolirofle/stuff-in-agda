module Logic.Propositional where

open import Data

record Syntax (Formula : Set → Set) : Set where
  field
    ⊤ : ∀{Stmt} → Formula(Stmt)
    ⊥ : ∀{Stmt} → Formula(Stmt)
    ¬_ : ∀{Stmt} → Formula(Stmt) → Formula(Stmt)
    _∧_ : ∀{Stmt} → Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _∨_ : ∀{Stmt} → Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇒_ : ∀{Stmt} → Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇐_ : ∀{Stmt} → Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇔_ : ∀{Stmt} → Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⊕_ : ∀{Stmt} → Formula(Stmt) → Formula(Stmt) → Formula(Stmt)

-- Also known as Interpretation, Structure, Model
record Model (Stmt : Set) : Set where
  field
    interpretStmt : Stmt → Bool

interpret : ∀{Stmt} → Model(Stmt) → Formula(Stmt) → Bool
interpret 𝔐 φ = substitute (interpretStmt 𝔐) φ

_⊧_ : Model → Formula → Set
𝔐 ⊧ φ = (interpret 𝔐 φ) ≡ 𝑇

record Satisfaction (Formula : Set → Set) (syntax : Syntax(Formula)) (_⊨_ : Formula → Formula) : Set where
  field
    [⊤]-satisfaction : ∀{𝔐 : Model} → (𝔐 ⊧ ⊤)
