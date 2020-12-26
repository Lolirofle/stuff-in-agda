module Formalization.ImperativePL where

open import Data.Boolean
open import Data.List
import      Lvl
open import Numeral.Natural
open import String
open import Type

Ident : TYPE
data Lit : TYPE
data Stmt : TYPE
data Expr : TYPE
Ty : TYPE
record Context : TYPE₁

Ident = String

data Lit where
  unit : Lit
  bool : Bool → Lit
  nat  : ℕ → Lit

data Expr where
  lit    : Lit → Expr
  ident  : Ident → Expr
  apply  : Expr → Expr → Expr
  func   : Ident → Ty → Expr → Expr
  ifelse : Expr → Expr → Expr → Expr
  stmts  : List(Stmt) → Expr

Ty = Expr

data Stmt where
  expr       : Expr → Stmt
  decl       : Ident → Ty → Stmt
  def        : Ident → Expr → Stmt
  loop       : Stmt → Stmt
  return     : ℕ → Expr → Stmt

record Context where
  inductive
  field
    typing : Ident → Ty → TYPE

open import Logic.Propositional
open import Relator.Equals

add : Ident → Ty → Context → Context
Context.typing (add name ty ctx) a b = (Context.typing ctx a b) ∨ (a ≡ name)

pattern UnitTy   = ident "Unit"
pattern BoolTy   = ident "Bool"
pattern NatTy    = ident "Nat"
pattern FnTy A B = apply (apply (ident "→") A) B

data _⊢ₛ_,_ : Context → Context → Stmt → TYPE₁
data _⊢ₑ_,_=:_ : Context → Context → Expr → Ty → TYPE₁

data _⊢ₛ_,_ where
  expr : ∀{Γ₁ Γ₂}{e}{T} → (Γ₁ ⊢ₑ Γ₂ , e =: T) → (Γ₁ ⊢ₛ Γ₂ , expr e)
  decl : ∀{Γ}{name}{T} → (Γ ⊢ₛ (add name T Γ) , decl name T)
  def  : ∀{Γ₁ Γ₂}{name}{e}{T} → Context.typing Γ₁ name T → (Γ₁ ⊢ₑ Γ₂ , e =: T) → (Γ₁ ⊢ₛ Γ₂ , def name e)
  loop : ∀{Γ₁ Γ₂}{s} → (Γ₁ ⊢ₛ Γ₂ , s) → (Γ₁ ⊢ₛ Γ₁ , loop s)

data _⊢ₑ_,_=:_ where
  unit   : ∀{Γ} → (Γ ⊢ₑ Γ , (lit unit) =: UnitTy)
  bool   : ∀{Γ}{b} → (Γ ⊢ₑ Γ , (lit(bool b)) =: BoolTy)
  nat    : ∀{Γ}{n} → (Γ ⊢ₑ Γ , (lit(nat n)) =: NatTy)
  ident  : ∀{Γ}{i}{ty} → Context.typing Γ i ty → (Γ ⊢ₑ Γ , (ident i) =: ty)
  apply  : ∀{Γ₁ Γ₂ Γ₃}{f x}{A B} → (Γ₁ ⊢ₑ Γ₂ , x =: A) → (Γ₂ ⊢ₑ Γ₃ , f =: FnTy A B) → (Γ₁ ⊢ₑ Γ₃ , (apply f x) =: B)
  func   : ∀{Γ₁ Γ₂}{A B}{var}{body} → ((add var A Γ₁) ⊢ₑ Γ₂ , body =: B) → (Γ₁ ⊢ₑ Γ₁ , (func var A body) =: FnTy A B)
  ifelse : ∀{Γ₁ Γ₂ Γ₃ Γ₄}{b t f}{T} → (Γ₁ ⊢ₑ Γ₂ , b =: BoolTy) → (Γ₂ ⊢ₑ Γ₃ , t =: T) → (Γ₂ ⊢ₑ Γ₄ , f =: T) → (Γ₁ ⊢ₑ Γ₂ , (ifelse b t f) =: T)
