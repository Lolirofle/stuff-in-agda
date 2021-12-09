module Formalization.ImperativePL where

open import Data.Boolean
open import Data.List
open import Data.Option
open import Data.Tuple using (_⨯_)
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
  loop   : Expr → Expr
  stmts  : List(Stmt) → Expr

Ty = Expr

data Stmt where
  expr       : Expr → Stmt
  decl       : Ident → Ty → Stmt
  def        : Ident → Expr → Stmt
  return     : ℕ → Expr → Stmt

record Context where
  inductive
  field
    typing : Ident → Ty → TYPE
    value  : Ident → Lit
    exit   : Option(ℕ ⨯ Lit ⨯ Ty)

-- open import Type.Properties.Decidable
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Operator.Equals

instance
  Lit-equality-decider : EquivDecidable Lit
  Lit-equality-decider = {!!}

instance
  String-equality-decider : EquivDecidable String
  String-equality-decider = {!!}

addTyping : Ident → Ty → Context → Context
Context.typing (addTyping name ty ctx) i t = (Context.typing ctx i t) ∨ ((i ≡ name) ∧ (t ≡ ty))
Context.value  (addTyping name ty ctx)     = Context.value ctx

addValue : Ident → Lit → Context → Context
Context.typing (addValue name val ctx) = Context.typing ctx
Context.value  (addValue name val ctx) i with (name == i)
... | 𝑇 = val
... | 𝐹 = Context.value ctx i

add : Ident → Ty → Lit → Context → Context
add name ty val ctx = addValue name val (addTyping name ty ctx)

pattern UnitTy      = ident "Unit"
pattern BoolTy      = ident "Bool"
pattern NatTy       = ident "Nat"
pattern FnTy A B    = apply (apply (ident "→") A) B
pattern TupleTy A B = apply (apply (ident "⨯") A) B

data _⊢ₛ_,_    : Context → Context → Stmt → TYPE₁
data _⊢ₑ_,_::_ : Context → Context → Expr → Ty → TYPE₁
data _⊢ₑ_,_⇓_  : Context → Context → Expr → Lit → TYPE₁

data _⊢ₛ_,_ where
  expr : ∀{Γ₁ Γ₂}{e}{T} → (Γ₁ ⊢ₑ Γ₂ , e :: T) → (Γ₁ ⊢ₛ Γ₂ , expr e)
  decl : ∀{Γ₁ Γ₂}{name}{T} → Context.typing Γ₂ name T → (Γ₁ ⊢ₛ Γ₂ , decl name T)
  def  : ∀{Γ₁ Γ₂}{name}{e}{T} → Context.typing Γ₁ name T → (Γ₁ ⊢ₑ Γ₂ , e :: T) → (Γ₁ ⊢ₛ Γ₂ , def name e)

data _⊢ₑ_,_::_ where
  unit   : ∀{Γ} → (Γ ⊢ₑ Γ , (lit unit) :: UnitTy)
  bool   : ∀{Γ}{b} → (Γ ⊢ₑ Γ , (lit(bool b)) :: BoolTy)
  nat    : ∀{Γ}{n} → (Γ ⊢ₑ Γ , (lit(nat n)) :: NatTy)
  ident  : ∀{Γ}{i}{ty} → Context.typing Γ i ty → (Γ ⊢ₑ Γ , (ident i) :: ty)
  apply  : ∀{Γ₁ Γ₂ Γ₃}{f x}{A B} → (Γ₁ ⊢ₑ Γ₂ , x :: A) → (Γ₂ ⊢ₑ Γ₃ , f :: FnTy A B) → (Γ₁ ⊢ₑ Γ₃ , (apply f x) :: B)
  func   : ∀{Γ₁ Γ₂}{A B}{var}{body} → ((addTyping var A Γ₁) ⊢ₑ Γ₂ , body :: B) → (Γ₁ ⊢ₑ Γ₁ , (func var A body) :: FnTy A B)
  ifelse : ∀{Γ₁ Γ₂ Γ₃ Γ₄}{b t f}{T} → (Γ₁ ⊢ₑ Γ₂ , b :: BoolTy) → (Γ₂ ⊢ₑ Γ₃ , t :: T) → (Γ₂ ⊢ₑ Γ₄ , f :: T) → (Γ₁ ⊢ₑ Γ₂ , (ifelse b t f) :: T)
  loop   : ∀{Γ₁ Γ₂ Γ₃}{e}{ty} → (Γ₁ ⊢ₑ Γ₂ , e :: ty) → (Γ₂ ⊢ₑ Γ₃ , loop e :: ty) → (Γ₁ ⊢ₑ Γ₃ , loop e :: ty)
  -- TODO stmts  : ∀{Γ}{n} → (Γ ⊢ₑ Γ , (stmts ) :: NatTy)

data _⊢ₑ_,_⇓_ where
  lit    : ∀{Γ}{v} → (Γ ⊢ₑ Γ , (lit v) ⇓ v)
  ident  : ∀{Γ}{i}{v} → (Context.value Γ i ≡ v) → (Γ ⊢ₑ Γ , (ident i) ⇓ v)
  apply  : ∀{Γ₁ Γ₂ Γ₃}{x body ty}{var}{vx vy} → (Γ₁ ⊢ₑ Γ₂ , x ⇓ vx) → ((add var ty vx Γ₂) ⊢ₑ Γ₃ , body ⇓ vy) → (Γ₁ ⊢ₑ Γ₃ , (apply (func var ty body) x) ⇓ vy)

module Syntax where
  <> = Expr.lit Lit.unit
  true = Expr.lit(Lit.bool 𝑇)
  false = Expr.lit(Lit.bool 𝐹)
  # = \n → Expr.lit(Lit.nat n)
  &_ = Expr.ident
  _$_ = Expr.apply
  _::_↦_ = Expr.func
  if_::_else_ = Expr.ifelse
  _,_ = List._⊰_ {T = Stmt}
  _::_ = Stmt.decl
  _≔_ = Stmt.def

  
