module Formalization.LambdaCalculus.ByVarIndex where

import      Lvl
open import Data
open import Data.Boolean as Bool using (Bool ; 𝑇 ; 𝐹)
open import Data.Option as Option using (Option ; Some ; None)
import      Data.Option.Functions as Option
open import Function.Names using (_⊜_)
open import Functional
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type

record Indexing : Typeω where
  field
    {ℓₛ}  : Lvl.Level
    Scope : Type{ℓₛ}
    𝟎ₛ    : Scope
    𝐒ₛ    : Scope → Scope
    -- {ℓₛₒ} : Lvl.Level
    -- _≤_   : Scope → Scope → Type{ℓₛₒ}

    {ℓₙ}  : Lvl.Level
    Name  : Scope → Type{ℓₙ}
    𝟎ₙ    : ∀{s} → Name(𝐒ₛ(s))
    𝐒ₙ    : ∀{s} → Name(s) → Name(𝐒ₛ(s))
    𝐏ₙ    : ∀{s} → Name(𝐒ₛ(s)) → Option(Name(s))

    𝐏ₙ-𝐒ₙ-inverse : ∀{s} → (𝐏ₙ ∘ 𝐒ₙ ⊜ Some{T = Name(s)})
    -- 𝐏ₙ-𝟎ₙ         : ∀{s} → (𝐏ₙ(𝟎ₙ)  ≡ None{T = Name(s)})
    𝐒ₙ-𝐏ₙ-inverse : ∀{s} → (Option.partialMap 𝟎ₙ 𝐒ₙ ∘ 𝐏ₙ ⊜ id{T = Name(𝐒ₛ(s))})

{-
    _==ₙ_ : ∀{s} → Name(s) → Name(s) → Bool    
    coerce  : ∀{s₁ s₂} → (s₁ ≤ s₂) → Name(s₁) → Name(s₂)
    ¬Name∅  : ¬(Name ∅)
-}

  _+ₛ_ : Scope → ℕ → Scope
  s +ₛ 𝟎    = s
  s +ₛ 𝐒(n) = 𝐒ₛ(s +ₛ n)

module _ ⦃ indexing : Indexing ⦄ where
  open Indexing(indexing)

  data Term : Scope → Type{ℓₛ Lvl.⊔ ℓₙ} where
    Apply    : ∀{s} → Term(s) → Term(s) → Term(s)
    Abstract : ∀{s} → Term(𝐒ₛ(s)) → Term(s)
    Var      : ∀{s} → Name(s) → Term(s)
  Expr = Term(𝟎ₛ)

  data Value : ∀{s} → Term(s) → Type{ℓₛ Lvl.⊔ ℓₙ} where
    val : ∀{body} → Value{𝟎ₛ}(Abstract body)

  module _
    {ℓ}
    (P : ∀{s} → Term(s) → Type{ℓ})
    (papp : ∀{s}(f)(x) → P(f) → P(x) → P{s}(Apply f x))
    (pabs : ∀{s}(body) → P(body) → P{s}(Abstract body))
    (pvar : ∀{s}(name) → P{s}(Var name))
    where

    elim : ∀{s} → (t : Term(s)) → P(t)
    elim(Apply f x)     = papp f x (elim f) (elim x)
    elim(Abstract body) = pabs body (elim body)
    elim(Var v)         = pvar v

  𝐒ᵥₐᵣ : ∀{s} → Term(s) → Term(𝐒ₛ(s))
  𝐒ᵥₐᵣ = elim(\{s} _ → Term(𝐒ₛ(s)))
    (\_ _ → Apply)
    (\_ → Abstract)
    (Var ∘ 𝐒ₙ)

  substitute : ∀{s₁ s₂} → (Name(s₁) → Term(s₂)) → (Term(s₁) → Term(s₂))
  substitute F (Apply f x)     = Apply (substitute F f) (substitute F x)
  substitute F (Abstract body) = Abstract (substitute (Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ F) ∘ 𝐏ₙ) body)
  substitute F (Var v)         = F(v)

  substituteOuter : ∀{s} → Term(s) → Term(𝐒ₛ(s)) → Term(s)
  -- substituteOuter t = substitute(Option.partialMap t Var ∘ 𝐏ₙ)
  substituteOuter t (Apply f x)     = Apply (substituteOuter t f) (substituteOuter t x)
  substituteOuter t (Abstract body) = Abstract (substituteOuter (𝐒ᵥₐᵣ(t)) body)
  substituteOuter t (Var v)         = Option.partialMap t Var (𝐏ₙ(v))

  substitute' : ∀{s₁ s₂} → (Name(s₁) → Term(s₂)) → (Term(s₁) → Term(s₂))
  substitute' F (Apply f x)     = Apply (substitute' F f) (substitute' F x)
  substitute' F (Abstract body) = Abstract (substitute' (Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ F) ∘ 𝐏ₙ) body)
  substitute' F (Var v)         = F(v)

{-
Option.partialMap (𝐒ᵥₐᵣ t) Var ∘ 𝐏ₙ

Option.partialMap (𝐒ᵥₐᵣ t) (Var ∘ 𝐒ₙ) ∘ 𝐏ₙ ∘ ?
Option.partialMap (𝐒ᵥₐᵣ t) (𝐒ᵥₐᵣ ∘ Var) ∘ 𝐏ₙ ∘ ?
= 𝐒ᵥₐᵣ ∘ Option.partialMap t Var ∘ 𝐏ₙ ∘ ?
-}

  substituteOuter' : ∀{s} → Term(s) → Term(𝐒ₛ(s)) → Term(s)
  substituteOuter' t = substitute' (Option.partialMap t Var ∘ 𝐏ₙ)

  data _β⟶_ : ∀{s} → Term(s) → Term(s) → Type{ℓₛ Lvl.⊔ ℓₙ} where
    applyₗ : ∀{s}{f₁ f₂ x : Term(s)} → (f₁ β⟶ f₂) → (Apply f₁ x β⟶ Apply f₂ x)
    applyᵣ : ∀{s}{f x₁ x₂ : Term(s)} → (x₁ β⟶ x₂) → (Apply f x₁ β⟶ Apply f x₂)
    β : ∀{s}{body : Term(𝐒ₛ(s))}{x : Term(s)} → (Apply(Abstract body) x β⟶ substituteOuter x body)

  open import Data.Option.Proofs hiding (partialMap-apply-compose)
  open import Functional
  open import Logic.Predicate
  open import Structure.Function
  open import Structure.Operator
  open import Structure.Relator.Properties
  open import Structure.Setoid using (Equiv ; intro)
  open import Syntax.Transitivity

  private variable ℓ : Lvl.Level
  private variable T A X Y Z : Type{ℓ}
  private variable B : A → Type{ℓ}

  partialMap-apply-compose : ∀{f : Y → Z}{n}{s : X → Y} → (Option.partialMap (f(n)) (f ∘ s) ⊜ f ∘ Option.partialMap n s)
  partialMap-apply-compose {x = None}   = reflexivity(_≡_)
  partialMap-apply-compose {x = Some x} = reflexivity(_≡_)

  substitute-function : ∀{s₁ s₂}{F G : Name(s₁) → Term(s₂)} → (F ⊜ G) → (substitute F ⊜ substitute G)
  substitute-function fg {Apply f g}     = congruence₂(Apply) (substitute-function fg {f}) (substitute-function fg {g})
  substitute-function fg {Abstract body} = congruence₁(Abstract) $ (substitute-function {!partialMap-function(reflexivity(_≡_)) ? (reflexivity(_≡_))!} {body})
  substitute-function fg {Var name     } = fg

  substitute-Var-inverse : ∀{s} → (substitute{s} Var ⊜ id)
  substitute-Var-inverse{x = Apply f x}     = congruence₂(Apply) (substitute-Var-inverse{x = f}) (substitute-Var-inverse{x = x})
  substitute-Var-inverse{x = Abstract body} = congruence₁(Abstract) (substitute-function (\{x} → partialMap-apply-compose{f = Var}{x = 𝐏ₙ(x)} 🝖 congruence₁(Var) (𝐒ₙ-𝐏ₙ-inverse{x = x})) {body} 🝖 substitute-Var-inverse{x = body})
  substitute-Var-inverse{x = Var name}      = reflexivity(_≡_)

  {-
  instance
    [⊜]-reflexivity : Reflexivity(_⊜_ {A = A}{B = B})
    [⊜]-reflexivity = {!!}

  instance
    [⊜]-transitivity : Transitivity(_⊜_ {A = A}{B = B})
    [⊜]-transitivity = {!!}

  instance
    [→]-equiv : Equiv(X →ᶠ Y)
    [→]-equiv = intro(_⊜_) ⦃ {!!} ⦄

  instance
    [∘]-function : BinaryOperator {A₁ = Y → Z}{A₂ = X → Y} ⦃ [→]-equiv ⦄ ⦃ [→]-equiv ⦄ ⦃ [→]-equiv ⦄ (_∘_)

  partialMap-Some : ∀{n}{s : X → Y} → (Option.partialMap n s ∘ Some ⊜ s)

{-    substitute(Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f) ∘ 𝐏ₙ ∘ 𝐒ₙ) body    🝖[ _≡_ ]-[ substitute-function(
      Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f) ∘ 𝐏ₙ ∘ 𝐒ₙ 🝖[ _⊜_ ]-[ {!congruence₂-₂ ⦃ [→]-equiv ⦄ ⦃ [→]-equiv ⦄ (_∘_)(Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f)) ?!} ]
      Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f) ∘ Some    🝖[ _⊜_ ]-[ partialMap-Some ]
      𝐒ᵥₐᵣ ∘ f                                        🝖[ _⊜_ ]-[ {!!} ]
      Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f ∘ 𝐒ₙ) ∘ 𝐏ₙ 🝖[ _⊜_ ]-end
    ) {body}]-}

  testss : ∀{s₁ s₂}{f : Name(𝐒ₛ(s₁)) → Term(s₂)}{t} → (𝐒ᵥₐᵣ(f(𝟎ₙ)) ≡ Var(𝟎ₙ)) → (substitute f(𝐒ᵥₐᵣ(t)) ≡ substitute(f ∘ 𝐒ₙ) t)
  testss{f = _}{t = Apply f x}     f-inv = congruence₂(Apply) (testss{t = f} f-inv) (testss{t = x} f-inv)
  testss{f = f}{t = Abstract body} f-inv = congruence₁(Abstract) $
    substitute(Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f) ∘ 𝐏ₙ) (𝐒ᵥₐᵣ(body)) 🝖[ _≡_ ]-[ testss{t = body} {!!} ]
    substitute(Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f) ∘ 𝐏ₙ ∘ 𝐒ₙ) body    🝖[ _≡_ ]-[ substitute-function (\{x} →
      Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f) (𝐏ₙ(𝐒ₙ(x)))       🝖[ _≡_ ]-[ congruence₁(Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f)) 𝐏ₙ-𝐒ₙ-inverse ]
      Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f) (Some x)          🝖[ _≡_ ]-[]
      𝐒ᵥₐᵣ(f(x))                                              🝖[ _≡_ ]-[ congruence₁(𝐒ᵥₐᵣ) (congruence₁(f) 𝐒ₙ-𝐏ₙ-inverse) ]-sym
      𝐒ᵥₐᵣ(f(Option.partialMap 𝟎ₙ 𝐒ₙ (𝐏ₙ(x))))                🝖[ _≡_ ]-[ partialMap-apply-compose{f = 𝐒ᵥₐᵣ ∘ f}{x = 𝐏ₙ(x)} ]-sym
      Option.partialMap (𝐒ᵥₐᵣ(f(𝟎ₙ))) (𝐒ᵥₐᵣ ∘ f ∘ 𝐒ₙ) (𝐏ₙ(x)) 🝖[ _≡_ ]-[ {!partialMap-function ? (reflexivity(_≡_)) (reflexivity(_≡_))!} ]
      Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f ∘ 𝐒ₙ) (𝐏ₙ(x))      🝖[ _≡_ ]-end
    ) {body}]
    substitute(Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ f ∘ 𝐒ₙ) ∘ 𝐏ₙ) body    🝖-end
  testss{t = Var name} _ = reflexivity(_≡_)

  substituteOuter-𝐒ᵥₐᵣ-inverse : ∀{s}{t}{x} → substituteOuter{s} t (𝐒ᵥₐᵣ(x)) ≡ x
  substituteOuter-𝐒ᵥₐᵣ-inverse {s}{t}{Apply f x} =
    substituteOuter t (𝐒ᵥₐᵣ(Apply f x))                               🝖[ _≡_ ]-[]
    Apply (substituteOuter t (𝐒ᵥₐᵣ(f))) (substituteOuter t (𝐒ᵥₐᵣ(x))) 🝖[ _≡_ ]-[ congruence₂(Apply) (substituteOuter-𝐒ᵥₐᵣ-inverse {x = f}) (substituteOuter-𝐒ᵥₐᵣ-inverse {x = x}) ]
    Apply f x                                                         🝖-end
  substituteOuter-𝐒ᵥₐᵣ-inverse {s}{t}{Abstract body} =
    substituteOuter t (𝐒ᵥₐᵣ(Abstract body))  🝖[ _≡_ ]-[]
    substituteOuter t (Abstract(𝐒ᵥₐᵣ(body))) 🝖[ _≡_ ]-[]
    Abstract(substitute(Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ Option.partialMap t Var ∘ 𝐏ₙ) ∘ 𝐏ₙ) (𝐒ᵥₐᵣ(body))) 🝖[ _≡_ ]-[ congruence₁(Abstract) (substitute-function outer-equality {𝐒ᵥₐᵣ body}) ]
    Abstract(substituteOuter(𝐒ᵥₐᵣ(t)) (𝐒ᵥₐᵣ(body))) 🝖[ _≡_ ]-[ congruence₁(Abstract) (substituteOuter-𝐒ᵥₐᵣ-inverse{𝐒ₛ(s)}{𝐒ᵥₐᵣ(t)}{body}) ]
    Abstract body                            🝖-end
    where
      outer-equality : Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ Option.partialMap t Var ∘ 𝐏ₙ) ∘ 𝐏ₙ ⊜ Option.partialMap (𝐒ᵥₐᵣ t) Var ∘ 𝐏ₙ
      outer-equality {x} = {!!}

      outer-equality' : Option.partialMap (Var 𝟎ₙ) (𝐒ᵥₐᵣ ∘ Option.partialMap t Var ∘ 𝐏ₙ) ⊜ Option.partialMap (𝐒ᵥₐᵣ t) Var
      outer-equality' {None} = {!!}
      outer-equality' {Some x} = {!!}
  substituteOuter-𝐒ᵥₐᵣ-inverse {s}{t}{Var name} =
    substituteOuter t (𝐒ᵥₐᵣ(Var name))     🝖[ _≡_ ]-[]
    substituteOuter t (Var(𝐒ₙ(name)))      🝖[ _≡_ ]-[]
    Option.partialMap t Var (𝐏ₙ(𝐒ₙ(name))) 🝖[ _≡_ ]-[ congruence₁(Option.partialMap t Var) 𝐏ₙ-𝐒ₙ-inverse ]
    Var name                               🝖-end
  -}

open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Syntax.Number

open import Logic.Propositional
⊤-indexing : Indexing -- TODO: Cannot distinguish cases when using 𝐏ₙ, but correct? Limits the number of variables?
⊤-indexing = record
  { Scope = ⊤
  ; 𝟎ₛ    = <>
  ; 𝐒ₛ    = id
  ; Name  = const ⊤
  ; 𝟎ₙ    = <>
  ; 𝐒ₙ    = id
  ; 𝐏ₙ    = Some
  ; 𝐏ₙ-𝐒ₙ-inverse = [≡]-intro
  ; 𝐒ₙ-𝐏ₙ-inverse = \{ {_}{<>} → [≡]-intro }
  }

ℕ-𝐏? : ℕ → Option(ℕ)
ℕ-𝐏? 𝟎      = None
ℕ-𝐏? (𝐒(x)) = Some x

ℕ-indexing : Indexing
ℕ-indexing = record
  { Scope = ⊤
  ; 𝟎ₛ    = <>
  ; 𝐒ₛ    = id
  ; Name  = const ℕ
  ; 𝟎ₙ    = 𝟎
  ; 𝐒ₙ    = 𝐒
  ; 𝐏ₙ    = ℕ-𝐏?
  ; 𝐏ₙ-𝐒ₙ-inverse = [≡]-intro
  ; 𝐒ₙ-𝐏ₙ-inverse = \{ {_}{𝟎} → [≡]-intro ; {_}{𝐒 _} → [≡]-intro }
  }

Option-indexing : Indexing
Option-indexing = record
  { Scope = Type
  ; 𝟎ₛ    = ⊥
  ; 𝐒ₛ    = Option
  ; Name  = id
  ; 𝟎ₙ    = None
  ; 𝐒ₙ    = Some
  ; 𝐏ₙ    = id
  ; 𝐏ₙ-𝐒ₙ-inverse = [≡]-intro
  ; 𝐒ₙ-𝐏ₙ-inverse = \{ {_}{None} → [≡]-intro ; {_}{Some _} → [≡]-intro }
  }

instance
  𝕟-indexing : Indexing
  𝕟-indexing = record
    { Scope = ℕ
    ; 𝟎ₛ    = 𝟎
    ; 𝐒ₛ    = 𝐒
    ; Name  = 𝕟
    ; 𝟎ₙ    = 𝟎
    ; 𝐒ₙ    = 𝐒
    ; 𝐏ₙ    = Optional.𝐏
    -- ; _==ₙ_ = _≡?_
    ; 𝐏ₙ-𝐒ₙ-inverse = [≡]-intro
    ; 𝐒ₙ-𝐏ₙ-inverse = \{ {_}{𝟎} → [≡]-intro ; {_}{𝐒 _} → [≡]-intro }
    }

open import Data
open import Syntax.Number

testTerm1 : Term(2)
testTerm1 = Apply(Var 0) (Var 1)

testTerm2 : Term(3)
testTerm2 = Apply(Var 0) (Apply(Var 1) (Var 2))

testTerm3 : Term(2)
testTerm3 = Apply(Apply (Var 0) (Var 1)) (Abstract(Apply (Var 0) (Apply (Var 1) (Var 2))))

pattern λₜ_ {d} expr = Term.Abstract{d} expr
infixl 100 λₜ_
{-# DISPLAY Term.Abstract body = λₜ body #-}

pattern _$ₜ_ a b  = Term.Apply a b
infixl 101 _$ₜ_
{-# DISPLAY Term.Apply a b = a $ₜ b #-}

instance
  Term-from-ℕ : ⦃ indexing : Indexing ⦄ → ∀{ℓᵣ}{N}{R : ℕ → Type{ℓᵣ}} → ⦃ Numeral(Indexing.Name indexing N) R ⦄ → Numeral(Term(N)) R
  num ⦃ Term-from-ℕ ⦄ (n) = Var(num n)
{-# DISPLAY Term.Var n = n #-}

testTerm4af : Term 5
testTerm4af = λₜ 3 $ₜ 1 $ₜ (λₜ 0 $ₜ 2)

testTerm4ax : Term 4
testTerm4ax = λₜ 4 $ₜ 0

testTerm4a : Term 4
testTerm4a = (λₜ testTerm4af) $ₜ testTerm4ax

testTerm4b : Term 4
testTerm4b = λₜ 2 $ₜ (λₜ 5 $ₜ 0) $ₜ (λₜ 0 $ₜ (λₜ 6 $ₜ 0))
--           λₜ 2 $ₜ (λₜ 5 $ₜ 1) $ₜ (λₜ 0 $ₜ (λₜ 6 $ₜ 2))

testTermIndex1af : Term 2
testTermIndex1af = 0 $ₜ 1 $ₜ (λₜ 0 $ₜ (1 $ₜ 0))

testTermIndex1ax : Term 1
testTermIndex1ax = 0 $ₜ (λₜ 0)

testTermIndex1a : Term 1
testTermIndex1a = (λₜ testTermIndex1af) $ₜ testTermIndex1ax

testTermIndex1b : Term 1
testTermIndex1b = (0 $ₜ (λₜ 0)) $ₜ 0 $ₜ (λₜ 0 $ₜ ((1 $ₜ (λₜ 0)) $ₜ 0))

testReduct4 : testTerm4a β⟶ testTerm4b
testReduct4 = {!substituteOuter testTerm4ax testTerm4af!}

testReduct1 : testTermIndex1a β⟶ testTermIndex1b
testReduct1 = {!β!}

testTerm5 : Term(3)
testTerm5 = 0 $ₜ 1 $ₜ 2 $ₜ (λₜ 0 $ₜ 1 $ₜ 2 $ₜ 3 $ₜ (λₜ 0 $ₜ 1 $ₜ 2 $ₜ 3 $ₜ 4))

a : Term(2)
test = {!substituteOuter a testTerm5!}

{-
  substitute : ∀{s₁ s₂} → (Name(s₁) → Term(s₂)) → (Term(s₁) → Term(s₂))
  substitute{s₁}{s₂} map = func 𝟎 where
    var : (n : ℕ) → Name(s₁ +ₛ n) → Term(s₂ +ₛ n)
    var 𝟎 = map
    var (𝐒 n) name with 𝐏ₙ(name)
    ... | Some name' = {!(var n name')!}
    ... | None       = {!!}

    func : (n : ℕ) → Term(s₁ +ₛ n) → Term(s₂ +ₛ n)
    func n (Apply f x)     = Apply (func n f) (func n x)
    func n (Abstract body) = Abstract (func (𝐒(n)) body)
    func n (Var name)      = var n name

  substitute map (Apply f x)     = Apply (substitute map f) (substitute map x)
  substitute map (Abstract body) = Abstract (substitute {!!} body)
  substitute map (Var name)      = {!!}
-}
