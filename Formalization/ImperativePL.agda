module Formalization.ImperativePL where

open import Data.Boolean as Bool using (Bool ; 𝑇 ; 𝐹)
open import Data.Boolean.Operators using () renaming (module Programming to Bool)
open import Data.List
open import Data.Option
import      Data.Option.Functions as Option
open import Data.Tuple using (_⨯_)
open import Functional.Instance
import      Lvl
open import Numeral.Natural
open import String
import      String.Functions as String
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓᵢ ℓₑ ℓₜ ℓₜₑ ℓᵣₜ ℓₗ : Lvl.Level

record Operators (Expr : Type{ℓₑ}) : Type{ℓₑ} where
  constructor intro
  field
    ! : Expr → Expr
    _||_ : Expr → Expr → Expr
    _&&_ : Expr → Expr → Expr
    _=>_ : Expr → Expr → Expr
    _<=_ : Expr → Expr → Expr
    _==_ : Expr → Expr → Expr
    _!=_ : Expr → Expr → Expr
    _≤_ : Expr → Expr → Expr
    _≥_ : Expr → Expr → Expr
    _<_ : Expr → Expr → Expr
    _>_ : Expr → Expr → Expr
    _+_ : Expr → Expr → Expr
    _−_ : Expr → Expr → Expr
    _*_ : Expr → Expr → Expr
    _/_ : Expr → Expr → Expr
    _%_ : Expr → Expr → Expr
  infixl 9 _*_ _/_ _%_
  infixl 8 _+_ _−_
  infixl 7 _=>_ _<=_ _==_ _!=_
  infixl 6 _≤_ _≥_ _<_ _>_
  infixl 5 _&&_
  infixl 4 _||_
open Operators ⦃ … ⦄ public

module _ (Ident : Type{ℓᵢ}) (Expr : Type{ℓₑ}) where
  record Substitution(T : Type{ℓ}) : Type{ℓᵢ Lvl.⊔ ℓₑ Lvl.⊔ ℓ} where
    constructor intro
    field subst : Ident → Expr → T → T
  open Substitution ⦃ … ⦄ public

  data Stmt : Type{ℓᵢ Lvl.⊔ ℓₑ} where
    empty  : Stmt
    assign : Ident → Expr → Stmt
    seq    : Stmt → Stmt → Stmt
    assert : Expr → Stmt
    ifelse : Expr → Stmt → Stmt → Stmt
    while  : Expr → Expr → Expr → Stmt → Stmt

  pattern if b s = ifelse b s empty

module _ {Ident : Type{ℓᵢ}} {Expr : Type{ℓₑ}} where
  module _ ⦃ substExpr : Substitution Ident Expr Expr ⦄ where
    instance
      substStmt : Substitution Ident Expr (Stmt Ident Expr)
      substStmt = intro f where
        f : Ident → Expr → (Stmt Ident Expr → Stmt Ident Expr)
        f i e empty               = empty
        f i e (assign var val)    = assign var (subst i e val)
        f i e (seq s₁ s₂)         = seq (f i e s₁) (f i e s₂)
        f i e (assert b)          = assert(subst i e b)
        f i e (ifelse b s₁ s₂)    = ifelse (subst i e b) (f i e s₁) (f i e s₂)
        f i e (while b inv dec s) = while (subst i e b) (subst i e inv) (subst i e dec) (f i e s)

    module _ ⦃ exprOps : Operators(Expr) ⦄  where
      -- Weakest pre-condition.
      -- (wp s R) is a boolean expression which decides whther after evaluating the statement s, R will be satisfied.
      wp : Stmt Ident Expr → Expr → Expr
      wp empty               R = R
      wp (assign var val)    R = subst var val R
      wp (seq s₁ s₂)         R = wp s₁ (wp s₂ R)
      wp (assert b)          R = b && R
      wp (ifelse b s₁ s₂)    R = (b => wp s₁ R) && (b => wp s₂ R)
      wp (while b inv dec s) R = inv && (b => wp s inv) && ((! b) => R)

module _ (Ident : Type{ℓᵢ}) (Lit : Type{ℓₗ}) where
  data Expr : Type{ℓᵢ Lvl.⊔ ℓₗ} where
    lit   : Lit → Expr
    ident : Ident → Expr
    apply : Expr → Expr → Expr
    tuple : Expr → Expr → Expr

open import Operator.Equals using (EquivDecidable) renaming (_==_ to _≡?_)
open import Relator.Equals.Proofs

module _ {Ident : Type{ℓᵢ}} ⦃ Ident-eq : EquivDecidable(Ident) ⦄ {Lit : Type{ℓₗ}} where
  instance
    substExpr : Substitution Ident (Expr Ident Lit) (Expr Ident Lit)
    substExpr = intro f where
      f : Ident → (Expr Ident Lit) → (Expr Ident Lit → Expr Ident Lit)
      f i e (lit l)       = lit l
      f i e (ident vi)    = Bool.if(i ≡? vi) then e else (ident vi)
      f i e (apply fn x)  = apply (f i e fn) (f i e x)
      f i e (tuple e₁ e₂) = tuple (f i e e₁) (f i e e₂)

data Lit : Type{Lvl.𝟎} where
  unit  : Lit
  bool  : Bool → Lit
  nat   : ℕ → Lit
  tuple : Lit → Lit → Lit

-- data _⊢ₛ_,_    : Context → Context → Stmt → TYPE₁
-- data _⊢ₑ_,_::_ : Context → Expr → Ty → TYPE₁

module _ (Ident : Type{ℓᵢ}) where
  record Context : Type{ℓᵢ} where
    field
      function : Ident → (Lit → Option Lit)
      value    : Ident → Option Lit

module _ {Ident : Type{ℓᵢ}} where
  private variable ctx : Context Ident
  private variable l l₁ l₂ : Lit
  private variable i : Ident
  private variable e e₁ e₂ : Expr Ident Lit

  open import Relator.Equals

  data _⊢ₑ_⇓_  : Context(Ident) → Expr Ident Lit → Lit → Type{ℓᵢ} where
    lit   : ctx ⊢ₑ (lit l) ⇓ l
    ident : (Context.value ctx i ≡ Some l) → (ctx ⊢ₑ (ident i) ⇓ l)
    apply : (Context.function ctx i l₁ ≡ Some l₂) → (ctx ⊢ₑ e ⇓ l₁) → (ctx ⊢ₑ (apply (ident i) e) ⇓ l₂)
    tuple : (ctx ⊢ₑ e₁ ⇓ l₁) → (ctx ⊢ₑ e₂ ⇓ l₂) → (ctx ⊢ₑ (tuple e₁ e₂) ⇓ (tuple l₁ l₂))

  eval : Context(Ident) → Expr Ident Lit → Option Lit
  eval ctx (lit l) = Some l
  eval ctx (ident i) = Context.value ctx i
  eval ctx (apply(ident f) x) = (eval ctx x) Option.andThen (Context.function ctx f)
  {-# CATCHALL #-}
  eval ctx (apply _        x) = None
  eval ctx (tuple e₁ e₂) = (eval ctx e₁) Option.andThen \l₁ → (eval ctx e₂) Option.andThen \l₂ → Some(tuple l₁ l₂)

open import Logic.Predicate
open import String.Decidable

module Test where
  open import Functional using (_∘_ ; _∘₂_)

  Ident = String

  instance
    opers : Operators(Expr Ident Lit)
    Operators.!    opers = apply(ident "!")
    Operators._||_ opers = apply(ident "||") ∘₂ tuple
    Operators._&&_ opers = apply(ident "&&") ∘₂ tuple
    Operators._=>_ opers = apply(ident "=>") ∘₂ tuple
    Operators._<=_ opers = apply(ident "<=") ∘₂ tuple
    Operators._==_ opers = apply(ident "==") ∘₂ tuple
    Operators._!=_ opers = apply(ident "!=") ∘₂ tuple
    Operators._≤_  opers = apply(ident "≤") ∘₂ tuple
    Operators._≥_  opers = apply(ident "≥") ∘₂ tuple
    Operators._<_  opers = apply(ident "<") ∘₂ tuple
    Operators._>_  opers = apply(ident ">") ∘₂ tuple
    Operators._+_  opers = apply(ident "+") ∘₂ tuple
    Operators._−_  opers = apply(ident "−") ∘₂ tuple
    Operators._*_  opers = apply(ident "*") ∘₂ tuple
    Operators._/_  opers = apply(ident "/") ∘₂ tuple
    Operators._%_  opers = apply(ident "%") ∘₂ tuple

  module Syntax where
    pattern <> = Expr.lit Lit.unit
    pattern true = Expr.lit(Lit.bool 𝑇)
    pattern false = Expr.lit(Lit.bool 𝐹)
    pattern # n = Expr.lit(Lit.nat n)
    pattern & i = Expr.ident i
    pattern _$_ f x = Expr.apply f x
    pattern _,_ a b = tuple a b
    pattern if_then_else_ b s₁ s₂ = Stmt.ifelse b s₁ s₂
    pattern _≔_ v e = Stmt.assign v e
    pattern _﹔_ s₁ s₂ = Stmt.seq s₁ s₂
    pattern while_invariant_decreasing_then_ b inv d s = Stmt.while b inv d s
    infixl 10 _$_
    infixl 3 _,_
    infixl 2 _≔_
    infixl 1 while_invariant_decreasing_then_ if_then_else_
    infixl 0 _﹔_
  open Syntax

  import Numeral.Natural.Oper.Comparisons as ℕ
  import Numeral.Natural.Oper.FlooredDivision as ℕ
  import Numeral.Natural.Oper.Modulo as ℕ
  import Numeral.Natural.Oper as ℕ

  context : Context Ident
  Context.value    context _  = None
  Context.function context "!"  (bool b)            = Some(bool(Bool.! b))
  Context.function context "||" (bool b₁ , bool b₂) = Some(bool(b₁ Bool.|| b₂))
  Context.function context "&&" (bool b₁ , bool b₂) = Some(bool(b₁ Bool.&& b₂))
  Context.function context "=>" (bool b₁ , bool b₂) = Some(bool(b₁ Bool.→? b₂))
  Context.function context "<=" (bool b₁ , bool b₂) = Some(bool(b₁ Bool.←? b₂))
  Context.function context "==" (bool b₁ , bool b₂) = Some(bool(b₁ Bool.== b₂))
  Context.function context "!=" (bool b₁ , bool b₂) = Some(bool(b₁ Bool.!= b₂))
  Context.function context "≤"  (nat a , nat b)     = Some(bool(a ℕ.≤? b))
  Context.function context "≥"  (nat a , nat b)     = Some(bool(a ℕ.≥? b))
  Context.function context "<"  (nat a , nat b)     = Some(bool(a ℕ.<? b))
  Context.function context ">"  (nat a , nat b)     = Some(bool(a ℕ.>? b))
  Context.function context "+"  (nat a , nat b)     = Some(nat(a ℕ.+ b))
  Context.function context "−"  (nat a , nat b)     = Some(nat(a ℕ.−₀ b))
  Context.function context "*"  (nat a , nat b)     = Some(nat(a ℕ.⋅ b))
  Context.function context "/"  (nat a , nat b)     = Some(nat(a ℕ.⌊/⌋₀ b))
  Context.function context "%"  (nat a , nat b)     = Some(nat(a ℕ.mod₀ b))
  {-# CATCHALL #-}
  Context.function context _ _  = None

  I : Expr Ident Lit
  I = ((& "n") ≤ (& "x"))
    && (((& "x") % (# 2) == (# 𝟎)) => ((& "n") % (# 2) == (# 𝟎)))
    && (((& "x") % (# 2) != (# 𝟎)) => ((& "n") % (# 2) != (# 𝟎)))

  doubleIfEvenBody : Stmt Ident (Expr Ident Lit)
  doubleIfEvenBody =
    "n" ≔ (& "x") ﹔
    while((& "n") ≥ (# 2))
      invariant I
      decreasing (& "n")
    then(
      "n" ≔ (& "n") − (# 2)
    ) ﹔
    if((& "n") == (# 0))
    then ("n" ≔ (# 2) * (& "x"))
    else ("n" ≔ (& "x"))

  R : Expr Ident Lit
  R =  (((& "x") % (# 2) == (# 𝟎)) => ((& "n") == (# 2) * (& "x")))
    && (((& "x") % (# 2) != (# 𝟎)) => ((& "n") == (& "x")))

  {-
  open import Relator.Equals
  open import Syntax.Transitivity
  doubleIfEvenBody-proof : context ⊢ₑ (wp doubleIfEvenBody R) ⇓ (bool 𝑇)
  doubleIfEvenBody-proof = {!eval context (wp doubleIfEvenBody R)!} where
    test =
      wp("n" ≔ (& "x") ﹔ while((& "n") ≥ (# 2)) invariant I decreasing(& "n") then("n" ≔ (& "n") − (# 2)) ﹔ if((& "n") == (# 0)) then ("n" ≔ (# 2) * (& "x")) else ("n" ≔ (& "x"))) R 🝖[ _≡_ ]-[ {!!} ]
      {!!} 🝖-end
  -}
    

{-
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

  
-}
