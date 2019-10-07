module SimplyTypedLambdaCalculus where

open import Numeral.Natural

data Type (B : Set) : Set₁ where
  Base : B → Type(B)
  Function : Type(B) → Type(B) → Type(B)

data Term (B : Set) : Set₁ where
  Apply : Term(B) → Term(B) → Term(B)
  Abstract : Type(B) → Term(B) → Term(B)
  Var : ℕ → Term(B)
  Const : B → Term(B)

module _ {B} where
  data _⊢_::_ (Γ : Term(B) → Type(B) → Set) : Term(B) → Type(B) → Set₁ where
    intro : ∀{a}{T} → Γ(a)(T) → (Γ ⊢ a :: T)
    -- const : ∀{a}{T} → Γ(a)(T) → (Γ ⊢ a :: T)
    abstr : ∀{body}{A B} → (Γ ⊢ body :: B) → (Γ ⊢ Abstract A body :: Function A B)
    apply : ∀{f x}{A B} → (Γ ⊢ f :: Function A B) → (Γ ⊢ x :: A) → (Γ ⊢ Apply f x :: B)

{-
A,B ::= Base | A ⟶ B
t ::= k | t t | λ t | Const b
b = true | false

Γ ⊢ Const b : Base
v ::= Const b | λ t
(⊢ t : Base) → ∃ v t ⟶* v
(⊢ t : A) → ∃ v t ⟶* v

Red(A)(t) definition "to be reducible"
Red(Base)(t) = ∃v(t ⟶* v)
Red(A→B)(t) = ∀u. Red(A)(u) → Red(B)(t u)

(t ⟶ t') → Red(A)(t') → Red(A)(t)
  • A = Base:
    ∃v(t* ⟶* v) → ∃v(t ⟶* v)
    t → t' ⟶* v
  • A = B→C:
    ∀u. Red(B)(u) → Red(C)(t' u)
    to show ∀u. Red(B)(u) → Red(C)(t u)
    and just use induction on the first thing mentioned
    Red(C)(t' u)
    to get
    Red(C)(t u)


data ⟶β : Set where
  red1 : t ⟶β u
  red2 : (λ t) u ⟶β substitute t u
  red3 : (t ⟶β t') → ((t u) ⟶β (t' u))
  red4 : (u ⟶β u') → (t u ⟶β t u')

⟶β-confluent : Confluent (_⟶β_)

module CallByName where
  data ⟶β : Set where
    red2 : (λ t) u ⟶β substitute t u
    red3 : (t ⟶β t') → ((t u) ⟶β (t' u))

substitute-preservation : (Γ ⊢ ((λ u) u' : A)) → (Γ ⊢ (substitute u u' : A))
β⟶-preservation : (Γ ⊢ (t : A)) → (t ⟶β t') → (Γ ⊢ (t' : A))

Red(Γ)(σ)
Γ = () | Γ.A -- context
σ : ℕ → Term
∀k. Γ ⊢ k : A
Represent variable as a context
σ is a formal definition of "reducible" substitution
Example:
Γ.A ⊢ 0 : A
Γ.A.B ⊢ 1 : A

σ-substitution?:

Red(Γ)(σ) ∧ (Γ ⊢ t:A) → Red(A)(t σ)
  Proof by induction on t
  • t = Ref k
    Red(A)(k σ) = Red(A)(σ(k))
  • t = t₀ t₁
    t_σ = (t₀ σ) (t₁ σ)
    Γ ⊢ t₀ : B → A
    Γ ⊢ t₁ : B
    by induction hypothesis:
    Red(B→A)(t₀ σ)
    Red(B)(t₁ σ)
    so Red(A)(t₀ σ)(t₁ σ)
  • t = λ u
    A = B → C
    Γ.B ⊢ u : C
    To show: Red(B→C)((λ u) σ)
    it means: ∀ u',Red(B)(u'), show Red(C)((λv) σ u')
    Define:
      (_,_) : (σ : ℕ → Term) (u' : Term) : ℕ → Term
      (σ,u')(0) = u'
      (σ,u')(𝐒 n) = σ(n)
    Claim: (λu) σ u' ⟶ u(σ,u')
    Γ.B ⊢ (k : T) → Red(T)((σ,u') k)
      k=0: Γ.B ⊢ 0
      k=n+1 (Γ ⊢ u : T) → (Γ ,B ⊢ n+1 : T)
    Summary:
      This is all to prove ∃v(t ⟶* v) if ⊢ t : Base, which is Red(A)(t)?
      Direct proof for application.
      Generalize the statement to: (⊢ t : A) → Red(A)(t)
      and then to: (Γ ⊢ t:A) → Red(Γ)(σ) → Red(A)(t σ)


  Something else: Krivine abstract machine
  How to evaluate λ-terms without substitution (defined before LISP eval with substitution)
  Term: k | tt | λ t
  Closure: t, ρ -- note: first mention of closure in this field? (denoted u v,‥)
  Environment: list of closures
  Stack: list of closures in stack order (denoted S)
  3 components: Term t,ENv ρ, Stack S → Term Env STack
  t₁ | ρ₁ | S₁ | t₂ | ρ₂ | S₂
  λ t | ρ | u : S | t | (ρ,u) | S
  t₀t1 | ρ | S | t₀ | ρ | (t₁,ρ) : S
  0 | ρ,(t,ρ') | S | t | ρ' | S
  k+1 | ρ,(t,p') | S | k | ρ | S
  Those are the transformations/reductions of the machine.
  Simplified description of how functional programs are evaluated.
  
-}
