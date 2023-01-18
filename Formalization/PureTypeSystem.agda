--{-# OPTIONS --with-K #-}

open import Data
open import Data.Tuple using (_⨯_ ; _,_)
open import Logic.Predicate
import      Lvl
open import Syntax.Number
import      Type as Meta

-- `Constants` is the type of all possible constant terms.
-- `Sort` is a subset of `Constants` that indicate the sorts of the type system (the types of types).
-- `Axioms` pairs constant terms with types.
-- `Rules` pairs product terms with types.
module Formalization.PureTypeSystem (Constants : Meta.Type{0}) where -- TODO: I don't really have a reference for any of the definitions so they may be incorrect

open import Numeral.Natural
open import Numeral.Finite

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level
private variable d d₁ d₂ d₃ : ℕ

data Term : ℕ → Meta.Type{0} where
  Apply    : Term(d) → Term(d) → Term(d)
  Abstract : Term(d) → Term(𝐒(d)) → Term(d)
  Var      : 𝕟(d) → Term(d)
  Constant : Constants → Term(d)
  Product  : Term(d) → Term(𝐒(d)) → Term(d)

Expression : Meta.Type{0}
Expression = Term(0)

module VarNumeralSyntax where
  -- Syntax for writing Var as a numeral.
  instance
    Term-from-ℕ : ∀{N} → Numeral(Term(N)) (Numeral.Restriction(𝕟-numeral{N}))
    num ⦃ Term-from-ℕ ⦄ n = Var(num n)

module ExplicitLambdaSyntax where
  open VarNumeralSyntax public

  infixr 100 𝜆[_::_] Π[_::_]
  infixl 101 _←_

  pattern 𝜆[_::_] d type expr = Term.Abstract{d} type expr
  pattern Π[_::_] d type expr = Term.Product{d} type expr
  pattern _←_ a b  = Term.Apply a b

module _ where
  var-𝐒 : Term(d) → Term(𝐒(d))
  var-𝐒 (Apply f x)             = Apply (var-𝐒(f)) (var-𝐒(x))
  var-𝐒 (Abstract{d} type body) = Abstract{𝐒(d)} (var-𝐒 type) (var-𝐒(body))
  var-𝐒 (Var{𝐒(d)} n)           = Var{𝐒(𝐒(d))} (𝐒(n))
  var-𝐒 (Constant c)            = Constant c
  var-𝐒 (Product a b)           = Product (var-𝐒 a) (var-𝐒 b)

  substituteVar0 : Term(d) → Term(𝐒(d)) → Term(d)
  substituteVar0 val (Apply f x)          = Apply (substituteVar0 val f) (substituteVar0 val x)
  substituteVar0 val (Abstract type body) = Abstract (substituteVar0 val type) (substituteVar0 (var-𝐒 val) body)
  substituteVar0 val (Var 𝟎)              = val
  substituteVar0 val (Var(𝐒 i))           = Var i
  substituteVar0 val (Constant c)         = Constant c
  substituteVar0 val (Product a b)        = Product (substituteVar0 val a) (substituteVar0 (var-𝐒 val) b)

  open import Relator.Equals

  private variable x y : Term(d)

  substituteVar0-var-𝐒 : (substituteVar0 y (var-𝐒 x) ≡ x)
  substituteVar0-var-𝐒 {d}{y}{Apply f x}
    rewrite substituteVar0-var-𝐒 {d}{y}{f}
    rewrite substituteVar0-var-𝐒 {d}{y}{x}
    = [≡]-intro
  substituteVar0-var-𝐒 {d}{y}{Abstract t x}
    rewrite substituteVar0-var-𝐒 {d}{y}{t}
    rewrite substituteVar0-var-𝐒 {𝐒 d}{var-𝐒 y}{x}
    = [≡]-intro
  substituteVar0-var-𝐒 {_}{_}{Var 𝟎}      = [≡]-intro
  substituteVar0-var-𝐒 {_}{_}{Var(𝐒 _)}   = [≡]-intro
  substituteVar0-var-𝐒 {_}{_}{Constant c} = [≡]-intro
  substituteVar0-var-𝐒 {d}{y}{Product t x}
    rewrite substituteVar0-var-𝐒 {d}{y}{t}
    rewrite substituteVar0-var-𝐒 {𝐒 d}{var-𝐒 y}{x}
    = [≡]-intro
  {-# REWRITE substituteVar0-var-𝐒 #-}

module _ where
  -- postulate _β⥈*_ : Term(d) → Term(d) → Meta.Type{0}
  open import Relator.ReflexiveTransitiveClosure

  private variable f g x y : Term(d)

  -- β-reduction (beta) with its compatible closure over `Apply`.
  -- Reduces a term of form `f(x)` to `f[0 ≔ x]`.
  data _β⇴_ : Term(d₁) → Term(d₂) → Meta.Type{1} where
    β : ∀{f : Term(𝐒(d))}{x ty : Term(d)} → (Apply(Abstract ty (f))(x) β⇴ substituteVar0(x)(f))
    cong-applyₗ : (f β⇴ g) → (Apply f(x) β⇴ Apply g(x))
    cong-applyᵣ : (x β⇴ y) → (Apply f(x) β⇴ Apply f(y))

  _β⇴*_ : Term(d) → Term(d) → Meta.Type
  _β⇴*_ = ReflexiveTransitiveClosure(_β⇴_)

  _β⥈_ : Term(d) → Term(d) → Meta.Type
  _β⥈_ = SymmetricClosure(_β⇴_)

  _β⥈*_ : Term(d) → Term(d) → Meta.Type
  _β⥈*_ = ReflexiveTransitiveClosure(_β⥈_)

{-
module _ where
  open import Data.Boolean
  open import Data.Boolean.Stmt
  open import Data.Option
  import      Data.Option.Functions as Option
  open import Logic.Propositional
  open import Functional

  private variable T A B : Meta.Type{ℓ}
  private variable x : A
  private variable y : B
  private variable m m₁ m₂ : T
  private variable f : A → B

  open import Relator.Equals
  record MapContainer (A : Meta.Type{ℓ₁}) (B : A → Meta.Type{ℓ₂}) (Map : Meta.Type{ℓ₃}) : Meta.Type{Lvl.𝐒(ℓ₁) Lvl.⊔ Lvl.𝐒(ℓ₂) Lvl.⊔ ℓ₃} where
    field
      ∅     : Map
      has   : A → Map → Bool
      get   : (a : A) → Map → Option(B(a))
      set   : (a : A) → B(a) → Map → Map
      unset : A → Map → Map
      union : Map → Map → Map
      -- map   : (B → B) → (Map → Map)
      _⊆_   : Map → Map → Meta.Type{0}
      _≡ₘ_  : Map → Map → Meta.Type{0}

    field
      get-of-∅     : (get x ∅ ≡ None)
      get-has      : (Option.isSome(get x m) ≡ has x m)
      get-of-set   : (get x (set x y m) ≡ Some(y))
      get-of-unset : (get x (unset x m) ≡ None)
      get-of-union : (get x (union m₁ m₂) ≡ (get x m₁) Option.Same.orᵣ (get x m₂))
      -- get-of-map   : (get x (map f m) ≡ Option.map f(get x m))
      submap-get   : (m₁ ⊆ m₂) ↔ (∀{x} → (IsFalse(has x m₁) ∨ (get x m₁ ≡ get x m₂)))
      equiv-get    : (m₁ ≡ₘ m₂) ↔ (∀{x} → (get x m₁ ≡ get x m₂))
-}

open import Numeral.CoordinateVector
open import Type.Dependent.Sigma
module Typing
  (Sort : ∀{d} → Term(d) → Meta.Type{0})
  (Axioms : Constants → Expression → Meta.Type{0})
  (Rules : ∀{d₁ d₂ d₃} → ∃(Sort{d₁}) → ∃(Sort{d₂}) → ∃(Sort{d₃}) → Meta.Type{0})
  where

  data Context : ℕ → Meta.Type{0} where
    ∅   : Context(𝟎)
    _⊱_ : Context(d) → Term(d) → Context(𝐒(d))

  get : (i : 𝕟(𝐒(d))) → Context(𝐒(d)) → Term(d)
  get       𝟎     (_ ⊱ x) = x
  get {𝐒 _} (𝐒 i) (l ⊱ _) = var-𝐒(get i l)

  private variable A A₁ A₂ B B₁ B₂ F F₁ F₂ X X₁ X₂ BX T T₁ T₂ : Term(d)
  private variable c : Constants
  private variable i i₁ i₂ : 𝕟(d)
  private variable s s₁ s₂ s₃ : ∃(Sort)
  private variable Γ Δ : Context(d)

  -- Subtyping rules.
  _<:_ = _β⥈*_

  open import Data.Option
  open import Relator.Equals

  -- Typing rules. (TODO: I think there are some issues with the depth indexing)
  data _⊢_::_ : Context(d₁) → Term(d₂) → Term(d₃) → Meta.Type{1} where
    constants   : (Axioms c A) → (Γ ⊢ (Constant{d₂} c) :: A)
    variables   : (Γ ⊢ (get i Γ) :: ([∃]-witness s)) → (Γ ⊢ (Var i) :: (get i Γ))
    weakening   : (Γ ⊢ B :: ([∃]-witness s)) → (Γ ⊢ X :: A) → ((Γ ⊱ B) ⊢ X :: A)
    product     : (Rules s₁ s₂ s₃) → (Γ ⊢ A :: ([∃]-witness s₁)) → ((Γ ⊱ A) ⊢ B :: ([∃]-witness s₂)) → (Γ ⊢ (Product A B) :: ([∃]-witness s₃))
    application : (Γ ⊢ F :: Product A B) → (Γ ⊢ X :: A) → (Γ ⊢ Apply F X :: substituteVar0 X B)
    abstraction : (Γ ⊢ (Product A B) :: ([∃]-witness s)) → ((Γ ⊱ A) ⊢ F :: B) → (Γ ⊢ (Abstract A F) :: (Product A B))
    -- conversion  : (Γ ⊢ B :: Constant([∃]-witness s)) → (A <: B) → (Γ ⊢ X :: A) → (Γ ⊢ X :: B)

{-
3: 6
4: 7

0: 3
1: 4

toℕ (Wrapping.[−] i₁) ≡ toℕ (Wrapping.[−] i₂)
-}
  data _≡d_ : Term(d₁) → Term(d₂) → Meta.Type{0} where
    application : (F₁ ≡d F₂) → (X₁ ≡d X₂) → (Apply F₁ X₁ ≡d Apply F₂ X₂)
    abstraction : (T₁ ≡d T₂) → (B₁ ≡d B₂) → Abstract T₁ B₁ ≡d Abstract T₂ B₂
    var-left    : (Var{𝐒(d₁)} {!d₁ −₀ d₂!} ≡d Var{𝐒(d₂)} 𝟎)
    var-right   : (Var{𝐒(d₁)} 𝟎 ≡d Var{𝐒(d₂)} {!d₁ −₀ d₂!})
    var-step    : (Var i₁ ≡d Var i₂) → (Var(𝐒(i₁)) ≡d Var(𝐒(i₂)))
    constant    : Constant{d₁} c ≡d Constant{d₂} c
    product     : (A₁ ≡d A₂) → (B₁ ≡d B₂) → Product A₁ B₁ ≡d Product A₂ B₂

  open import Logic.Propositional
  open import Syntax.Function
  open import Type.Dependent.Functions

  -- typing-substitution : ((set Var0 B (Γ ∪ Δ)) ⊢ A :: B) → ((Γ ∪ map(\(intro e p) → {!substituteVar0 X p!}) Δ) ⊢ (substituteVar0 X A) :: (substituteVar0 X B))

  import      Data.Either as Either
  open import Logic.Classical
  module _
    ⦃ classical-sort : ∀{d}{c} → Classical(Sort{d} c) ⦄
    -- (axioms-term-or-sort : ∀{A B} → (Axioms A B) → (Sort(B) ∨ ∃(d ↦ ∃{Obj = ∃(Sort{d})}(s ↦ Γ ⊢ B :: ([∃]-witness s)))))
    where

    sort-substituteVar0 : Sort(X) → Sort(A) → Sort(substituteVar0 X A)
    sort-substituteVar0 {A = Apply F X}    _      sort-A = {!!}
    sort-substituteVar0 {A = Abstract T B} _      sort-A = {!!}
    sort-substituteVar0 {A = Var 𝟎}        sort-X sort-A = sort-X
    sort-substituteVar0 {A = Var (𝐒 i)}    _      sort-A = {!!}
    sort-substituteVar0 {A = Constant c}   _      sort-A = {!sort-A!}
    sort-substituteVar0 {A = Product A B}  _      sort-A = {!!}

    -- When a term has a type, the type is either a sort or its type is a sort.
    type-is-term-or-sort : (Γ ⊢ A :: B) → (Sort(B) ∨ ∃{Obj = ∃(d ↦ ∃(Sort{d}))}(s ↦ Γ ⊢ B :: ([∃]-witness([∃]-proof s))))
    type-is-term-or-sort (constants {c} axiom) = {!!}
    type-is-term-or-sort (variables {s = s} ty) = [∨]-introᵣ ([∃]-intro ([∃]-intro _ ⦃ s ⦄) ⦃ ty ⦄)
    type-is-term-or-sort (weakening{s = s} pre post) = Either.mapRight ([∃]-map-proof (weakening{s = s} pre)) (type-is-term-or-sort post)
    type-is-term-or-sort (product{s₃ = s₃} r a b) = [∨]-introₗ ([∃]-proof s₃)
    type-is-term-or-sort (application {F = F} ab a) = {!!}
    type-is-term-or-sort (abstraction{s = s} ab f) = [∨]-introᵣ ([∃]-intro ([∃]-intro _ ⦃ s ⦄) ⦃ ab ⦄)
    {-type-is-term-or-sort (constants {c} axiom) = ? -- axioms-term-or-sort axiom
    type-is-term-or-sort (variables {s = s} ty) = [∨]-introᵣ {!!}
    type-is-term-or-sort (product{s₃ = s₃} r a b) = [∨]-introₗ ([∃]-proof s₃)
    type-is-term-or-sort (application {F = Apply F F₁} ab a) = {!!}
    type-is-term-or-sort (application {F = Abstract F F₁} (abstraction ab ab₁) a) = {!!}
    type-is-term-or-sort (application {F = Constant x} ab a) = {!!}
    type-is-term-or-sort (application {F = Product F F₁} ab a) = {!!}
    type-is-term-or-sort (abstraction{s = s} ab f) = [∨]-introᵣ ([∃]-intro s ⦃ ab ⦄)
    -}

  -- A supermap of the context have the same typings.
  -- typing-supercontext : (Γ ⊆ Δ) → ((Γ ⊢ A :: B) → (Δ ⊢ A :: B))

  -- TODO: Confluence, subject reduction

  open import Data.Option.Equiv.Id
  open import Data.Option.Proofs
  open import Relator.Equals.Proofs
  open import Structure.Function
  open import Structure.Function.Domain hiding (Constant)
  open import Structure.Relator.Properties
  open import Structure.Setoid.Uniqueness
  open import Syntax.Transitivity

  instance
    Constant-injective : Injective(Constant{d})
    Injective.proof Constant-injective [≡]-intro = [≡]-intro

  instance
    Var-injective : Injective(Var{d})
    Injective.proof Var-injective [≡]-intro = [≡]-intro

  Productₗ-injective : ∀{ty₁ ty₂}{f₁ f₂} → (Product{d} ty₁ f₁ ≡ Product{d} ty₂ f₂) → (ty₁ ≡ ty₂)
  Productₗ-injective [≡]-intro = [≡]-intro

  Productᵣ-injective : ∀{ty₁ ty₂}{f₁ f₂} → (Product{d} ty₁ f₁ ≡ Product{d} ty₂ f₂) → (f₁ ≡ f₂) -- TODO: Here is an example of what axiom K does. If one had `Product ty f₁ ≡ Product ty f₂` instead, then it cannot pattern match on the identity because of `ty` being the same on both sides.
  Productᵣ-injective [≡]-intro = [≡]-intro

  Applyₗ-injective : ∀{f₁ f₂}{x₁ x₂} → (Apply{d} f₁ x₁ ≡ Apply{d} f₂ x₂) → (f₁ ≡ f₂)
  Applyₗ-injective [≡]-intro = [≡]-intro

  Applyᵣ-injective : ∀{f₁ f₂}{x₁ x₂} → (Apply{d} f₁ x₁ ≡ Apply{d} f₂ x₂) → (x₁ ≡ x₂)
  Applyᵣ-injective [≡]-intro = [≡]-intro

  Abstractₗ-injective : ∀{T₁ T₂}{body₁ body₂} → (Abstract{d} T₁ body₁ ≡ Abstract{d} T₂ body₂) → (T₁ ≡ T₂)
  Abstractₗ-injective [≡]-intro = [≡]-intro

  Abstractᵣ-injective : ∀{T₁ T₂}{body₁ body₂} → (Abstract{d} T₁ body₁ ≡ Abstract{d} T₂ body₂) → (body₁ ≡ body₂)
  Abstractᵣ-injective [≡]-intro = [≡]-intro

  open import Functional
  open import Logic.Predicate.Equiv
  import      Structure.Relator.Function.Multi as Relator
  open import Structure.Operator

  -- Every typable term have an unique type when all constants and products also have an unique type.
  {-typing-uniqueness : Relator.Names.Function(1)(Axioms) → (∀{d₁ d₂ d₃ : ℕ} → Relator.Names.Function(2) ⦃ [≡∃]-equiv ⦄ ⦃ [≡∃]-equiv ⦄ ⦃ [≡∃]-equiv ⦄ (Rules{d₁}{d₂}{d₃})) → Unique(Γ ⊢ X ::_)
  typing-uniqueness ax rul (constants px)       (constants py)       = ax [≡]-intro px py
  typing-uniqueness ax rul (variables _ pix)    (variables _ piy)    = injective(Some) (transitivity(_≡_) (symmetry(_≡_) pix) piy)
  typing-uniqueness ax rul (product rx px px₁)  (product ry py py₁)
    rewrite typing-uniqueness ax rul px py
    = rul (typing-uniqueness ax rul px py) (typing-uniqueness ax rul px₁ py₁) rx ry
  typing-uniqueness ax rul (application px px₁) (application py py₁) = congruence₁(substituteVar0 _) (Productᵣ-injective (typing-uniqueness ax rul px py))
  typing-uniqueness ax rul (abstraction px px₁) (abstraction py py₁)
    
    = congruence₁(Product _) {!!}  -- (typing-uniqueness ax rul px₁ {!!})
  -- typing-uniqueness {𝐒 d} ax rul {x}{y} px (conversion py x₁ py₁) rewrite typing-uniqueness ax rul px py₁ = {!x!}
  -- typing-uniqueness {𝐒 d} ax rul (conversion px x px₁) py = {!!}
  -}

  {-
  typing-uniqueness : Relator.Names.Function(1)(Axioms) → (∀{d₁ d₂ d₃ : ℕ} → Relator.Names.Function(2) ⦃ [≡∃]-equiv ⦄ ⦃ [≡∃]-equiv ⦄ ⦃ [≡∃]-equiv ⦄ (Rules{d₁}{d₂}{d₃})) → (∀{d : ℕ} → Relator.Names.Function(2)(_⊢_::_ {d = d}))
  typing-uniqueness ax rul                  gam exp           (constants px)       (constants py)       = ax (injective(Constant) exp) px py
  typing-uniqueness ax rul {x = Γ₁}{y = Γ₂} gam exp {y₁} {y₂} (variables _ pix)    (variables _ piy)    = injective(Some) $
    Some y₁  🝖[ _≡_ ]-[ pix ]-sym
    get _ Γ₁ 🝖[ _≡_ ]-[ congruence₂(get) (injective(Var) exp) gam ]
    get _ Γ₂ 🝖[ _≡_ ]-[ piy ]
    Some y₂ 🝖-end
  typing-uniqueness ax rul gam exp (product rx px px₁)  (product ry py py₁)  = rul XY AB rx ry where
    XY = typing-uniqueness ax rul gam (Productₗ-injective exp) px py
    AB = typing-uniqueness ax rul (congruence₃(push) (Productₗ-injective exp) XY gam) (Productᵣ-injective exp) px₁ py₁
  typing-uniqueness ax rul gam exp (application px px₁) (application py py₁) = congruence₂(substituteVar0) (Applyᵣ-injective exp) (Productᵣ-injective (typing-uniqueness ax rul gam (Applyₗ-injective exp) px py))
  typing-uniqueness ax rul gam exp (abstraction px px₁) (abstraction py py₁) = congruence₂(Product) {!!} {!!} where
    X₁X₂ = Abstractₗ-injective exp
    AB : _
    Y₁Y₂ : _
    Y₁Y₂ = typing-uniqueness ax rul (congruence₃(push) X₁X₂ AB gam) (Abstractᵣ-injective exp) px₁ py₁
    AB = typing-uniqueness ax rul gam (congruence₂(Product) X₁X₂ Y₁Y₂) px py
  -- congruence₂(Product) (Abstractₗ-injective exp) (typing-uniqueness ax rul (congruence₃(push) (Abstractₗ-injective exp) (typing-uniqueness ax rul gam {!!} px py) gam) (Abstractᵣ-injective exp) px₁ py₁)
  -}
