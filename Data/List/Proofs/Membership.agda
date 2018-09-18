-- Finite sets represented by lists
module Data.List.Proofs.Membership {ℓ₁} {ℓ₂} {T : Set(ℓ₂)} where

import Lvl
open import Functional
open import Data.List
open import Data.List.Proofs{ℓ₁ Lvl.⊔ ℓ₂}
open import Data.List.Relation.Membership{ℓ₁} {ℓ₂} {T}
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Propositional.Theorems{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Numeral.Natural
open import Numeral.Natural.Oper.Properties
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂} renaming (_≡_ to _[≡]_ ; _≢_ to _[≢]_)
open import Relator.Equals.Proofs{ℓ₁} hiding ([≡]-substitutionₗ ; [≡]-substitutionᵣ ; [≡]-reflexivity ; [≡]-transitivity ; [≡]-symmetry)
open import Type{ℓ₂}


pattern [∈]-id        {a}{L}          = [∈]-use  {a}{L}
pattern [∈][⊰]-expand {a}{x}{L} proof = [∈]-skip {a}{x}{L} (proof)

instance
  [∉]-empty : ∀{a} → (a ∉ ∅)
  [∉]-empty ()

instance
  [∈]-singleton : ∀{a} → (a ∈ singleton(a))
  [∈]-singleton = [∈]-id

instance
  [∈]-singleton-[≡] : ∀{a b} → (a ∈ singleton(b)) → (a [≡] b)
  [∈]-singleton-[≡] ([∈]-id)  = [≡]-intro
  [∈]-singleton-[≡] ([∈][⊰]-expand ())

instance
  [∉]-singleton-[≢] : ∀{a b} → (a [≢] b) → (a ∉ singleton(b))
  [∉]-singleton-[≢] = contrapositiveᵣ [∈]-singleton-[≡]

instance
  [∈]-of-[++]ᵣ : ∀{a}{L₁ L₂} → (a ∈ (L₁ ++ L₂)) → ((a ∈ L₁)∨(a ∈ L₂))
  [∈]-of-[++]ᵣ {a}{_}{∅} a∈L₁ = [∨]-introₗ([≡]-elimᵣ [++]-identityᵣ {expr ↦ (a ∈ expr)} (a∈L₁))
  [∈]-of-[++]ᵣ {_}{∅}{_} a∈L₂ = [∨]-introᵣ(a∈L₂)
  [∈]-of-[++]ᵣ {_}{_ ⊰ L₁}{L₂} ([∈]-id) = [∨]-introₗ([∈]-id)
  [∈]-of-[++]ᵣ {a}{x ⊰ L₁}{L₂} ([∈][⊰]-expand a∈L₁) with [∈]-of-[++]ᵣ {a}{L₁}{L₂} (a∈L₁)
  ... | [∨]-introₗ(a∈L₁∖a) = [∨]-introₗ([∈][⊰]-expand(a∈L₁∖a))
  ... | [∨]-introᵣ(a∈L₂) = [∨]-introᵣ(a∈L₂)

instance
  [∈]-of-[++]ₗ : ∀{a}{L₁ L₂} → (a ∈ (L₁ ++ L₂)) ← ((a ∈ L₁)∨(a ∈ L₂))
  [∈]-of-[++]ₗ {_}{∅}{_} ([∨]-introₗ ())
  -- [∈]-of-[++]ₗ {_}{_}{∅} ([∨]-introᵣ ())
  -- [∈]-of-[++]ₗ {a}{_}{∅} ([∨]-introₗ a∈L₁) = [≡]-elimₗ [++]-identityᵣ {expr ↦ (a ∈ expr)} (a∈L₁)
  [∈]-of-[++]ₗ {_}{∅}{_} ([∨]-introᵣ(a∈L₂)) = (a∈L₂)
  [∈]-of-[++]ₗ {_}{_ ⊰ L₁}{L₂} ([∨]-introₗ([∈]-id)) = [∈]-id
  [∈]-of-[++]ₗ {a}{x ⊰ L₁}{L₂} ([∨]-introₗ([∈][⊰]-expand a∈L₁)) = [∈][⊰]-expand([∈]-of-[++]ₗ {a}{L₁}{L₂} ([∨]-introₗ(a∈L₁)))
  [∈]-of-[++]ₗ {a}{x ⊰ L₁}{L₂} ([∨]-introᵣ(a∈L₂)) = [∈][⊰]-expand{a}{x}([∈]-of-[++]ₗ {a}{L₁}{L₂} ([∨]-introᵣ(a∈L₂)))

instance
  [∈]-of-[++] : ∀{a}{L₁ L₂} → (a ∈ (L₁ ++ L₂)) ↔ ((a ∈ L₁)∨(a ∈ L₂))
  [∈]-of-[++] = [↔]-intro [∈]-of-[++]ₗ [∈]-of-[++]ᵣ

instance
  [∈][++]-commute : ∀{a}{L₁ L₂} → (a ∈ (L₁ ++ L₂)) → (a ∈ (L₂ ++ L₁))
  [∈][++]-commute {a}{L₁}{L₂} (a∈L₁++L₂) = [∈]-of-[++]ₗ {a} {L₂}{L₁} ([∨]-symmetry([∈]-of-[++]ᵣ (a∈L₁++L₂)))

instance
  [∈][++]-duplicate : ∀{a}{L} → (a ∈ (L ++ L)) → (a ∈ L)
  [∈][++]-duplicate {a}{L} (a∈LL) = [∨]-elim id id ([∈]-of-[++]ᵣ {a} {L}{L} (a∈LL))

instance
  [∈][++]-expandₗ : ∀{a}{L₁ L₂} → (a ∈ L₂) → (a ∈ (L₁ ++ L₂))
  [∈][++]-expandₗ {a}{L₁}{L₂} (a∈L₂) = [∈]-of-[++]ₗ {a}{L₁}{L₂} ([∨]-introᵣ (a∈L₂))

instance
  [∈][++]-expandᵣ : ∀{a}{L₁ L₂} → (a ∈ L₁) → (a ∈ (L₁ ++ L₂))
  [∈][++]-expandᵣ {a}{L₁}{L₂} (a∈L₁) = [∈]-of-[++]ₗ {a}{L₁}{L₂} ([∨]-introₗ (a∈L₁))

instance
  [∈][⊰]-reorderₗ : ∀{a x}{L₁ L₂} → (a ∈ (L₁ ++ (x ⊰ L₂))) → (a ∈ (x ⊰ (L₁ ++ L₂)))
  [∈][⊰]-reorderₗ {a}{x}{L₁}{L₂} (a∈L₁++xL₂) = [∨]-elim left right ([∈]-of-[++]ᵣ (a∈L₁++xL₂)) where
    left : (a ∈ L₁) → (a ∈ (x ⊰ (L₁ ++ L₂)))
    left (a∈L₁) = [∈][⊰]-expand ([∈][++]-expandᵣ {a}{L₁}{L₂} (a∈L₁))

    right : ∀{a} → (a ∈ (x ⊰ L₂)) → (a ∈ (x ⊰ (L₁ ++ L₂)))
    right ([∈]-use)              = [∈]-use
    right ([∈][⊰]-expand (a∈L₂)) = [∈][⊰]-expand ([∈][++]-expandₗ {_}{L₁}{L₂} (a∈L₂))

-- [∈][⊰]-reorderᵣ : ∀{a x}{L₁ L₂} → (a ∈ (x ⊰ (L₁ ++ L₂))) → (a ∈ (L₁ ++ (x ⊰ L₂)))
-- [∈][⊰]-reorderᵣ {a}{x}{L₁}{L₂} ([∈]-id) = 
-- [∈][⊰]-reorderᵣ {a}{x}{L₁}{L₂} ([∈][⊰]-expand (a∈L₁++L₂)) = 

construct : ∀{a}{L} → (a ∈ L) → T
construct{a}(_) = a

instance
  [∈]-apply : ∀{a}{L} → (a ∈ L) → ∀{f} → (f(a) ∈ (map f(L)))
  [∈]-apply ([∈]-id)               = [∈]-id
  [∈]-apply ([∈][⊰]-expand(proof)) = [∈][⊰]-expand([∈]-apply(proof))

instance
  [∈]-at-last : ∀{L} → ∀{a} → (a ∈ (L ++ singleton(a)))
  [∈]-at-last{∅}        = [∈]-id
  [∈]-at-last{_ ⊰ rest} = [∈][⊰]-expand ([∈]-at-last{rest})

instance
  [∈]-in-middle : ∀{L₁ L₂} → ∀{a} → (a ∈ (L₁ ++ singleton(a) ++ L₂))
  [∈]-in-middle{L₁}{L₂}{a} = [∈]-of-[++]ₗ {a}{L₁ ++ singleton(a)}{L₂} ([∨]-introₗ ([∈]-at-last{L₁}))

[⊆]-substitution : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ⊆ L₂) → ∀{P : T → Stmt} → (∀{a} → (a ∈ L₂) → P(a)) → (∀{a} → (a ∈ L₁) → P(a))
[⊆]-substitution (L₁⊆L₂) proof = proof ∘ (L₁⊆L₂)

[⊇]-substitution : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ⊇ L₂) → ∀{P : T → Stmt} → (∀{a} → (a ∈ L₁) → P(a)) → (∀{a} → (a ∈ L₂) → P(a))
[⊇]-substitution (L₁⊇L₂) proof = proof ∘ (L₁⊇L₂)

[≡]-substitutionₗ : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ≡ L₂) → ∀{P : T → Stmt} → (∀{a} → (a ∈ L₁) → P(a)) → (∀{a} → (a ∈ L₂) → P(a))
[≡]-substitutionₗ (L₁≡L₂) = [⊆]-substitution ([↔]-elimₗ (L₁≡L₂))

[≡]-substitutionᵣ : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ≡ L₂) → ∀{P : T → Stmt} → (∀{a} → (a ∈ L₂) → P(a)) → (∀{a} → (a ∈ L₁) → P(a))
[≡]-substitutionᵣ (L₁≡L₂) = [⊆]-substitution ([↔]-elimᵣ (L₁≡L₂))

-- [⊆]-application : ∀{L₁ L₂} → (L₁ ⊆ L₂) → ∀{f} → (map f(L₁))⊆(map f(L₂))
-- [⊆]-application proof fL₁ = [∈]-proof.application ∘ proof
-- (∀{x} → (x ∈ L₂) → (x ∈ L₁)) → ∀{f} → (∀{x} → (x ∈ map f(L₂)) → (x ∈ map f(L₁)))

postulate [≡]-included-in : ∀{L : List{ℓ₂}(T)}{x} → (x ∈ L) → ((x ⊰ L) ≡ L)
-- [≡]-included-in (x-in) {a} = 

postulate [≡]-included-subset : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ⊆ L₂) → ((L₁ ++ L₂) ≡ L₂)

postulate [≡]-subset-[++] : ∀{L L₁ L₂ : List{ℓ₂}(T)} → (L₁ ⊆ L) → (L₂ ⊆ L) → (L₁ ++ L₂ ⊆ L)

instance
  [⊆]-reflexivity : ∀{L} → (L ⊆ L)
  [⊆]-reflexivity = id

instance
  [⊆]-antisymmetry : ∀{L₁ L₂} → (L₁ ⊆ L₂) → (L₂ ⊆ L₁) → (L₁ ≡ L₂)
  [⊆]-antisymmetry a b = (swap [↔]-intro) a b

instance
  [⊆]-transitivity : ∀{L₁ L₂ L₃} → (L₁ ⊆ L₂) → (L₂ ⊆ L₃) → (L₁ ⊆ L₃)
  [⊆]-transitivity a b = (swap _∘_) a b

instance
  [≡]-reflexivity : ∀{L} → (L ≡ L)
  [≡]-reflexivity = [↔]-intro [⊆]-reflexivity [⊆]-reflexivity

instance
  [≡]-symmetry : ∀{L₁ L₂} → (L₁ ≡ L₂) → (L₂ ≡ L₁)
  [≡]-symmetry (L₁≡L₂) {x} with (L₁≡L₂){x}
  ... | [↔]-intro l r = [↔]-intro r l

instance
  [≡]-transitivity : ∀{L₁ L₂ L₃} → (L₁ ≡ L₂) → (L₂ ≡ L₃) → (L₁ ≡ L₃)
  [≡]-transitivity (L₁≡L₂) (L₂≡L₃) {x} with [∧]-intro ((L₁≡L₂){x}) ((L₂≡L₃){x})
  ... | ([∧]-intro (lr₁) (lr₂)) = [↔]-transitivity  (lr₁) (lr₂)

instance
  [⊆]-with-[⊰] : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ⊆ L₂) → ∀{b} → (L₁ ⊆ (b ⊰ L₂))
  [⊆]-with-[⊰] (L₁⊆L₂) (x∈L₁) = [∈][⊰]-expand ((L₁⊆L₂) (x∈L₁))

instance
  [⊆]-with-[++]ₗ : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ⊆ L₂) → ∀{L₃} → (L₁ ⊆ (L₃ ++ L₂))
  [⊆]-with-[++]ₗ {L₁}{L₂} (L₁⊆L₂) {L₃} (x∈L₁) = [∈][++]-expandₗ {_}{L₃}{L₂} ((L₁⊆L₂) (x∈L₁))

instance
  [⊆]-with-[++]ᵣ : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ⊆ L₂) → ∀{L₃} → (L₁ ⊆ (L₂ ++ L₃))
  [⊆]-with-[++]ᵣ {L₁}{L₂} (L₁⊆L₂) {L₃} (x∈L₁) = [∈][++]-expandᵣ {_}{L₂}{L₃} ((L₁⊆L₂) (x∈L₁))

-- TODO: Does this work? It would be easier to "port" all (∈)-theorems to (⊆)-theorems then.
-- [∈]-to-[⊆]-property : ∀{L₂}{f : List{ℓ₂}(T) → List{ℓ₂}(T)} → (∀{a} → (a ∈ L₂) → (a ∈ f(L₂))) → (∀{L₁} → (L₁ ⊆ L₂) → (L₁ ⊆ f(L₂)))
