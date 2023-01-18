{-# OPTIONS --guardedness #-}

module FormalLanguage2.Proofs where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.List using (List ; _⊰_) renaming (∅ to [])
open import Data.List.Functions as List using (_++_)
import      Data.Tuple as Tuple
open import FormalLanguage2 hiding (suffix)
open import FormalLanguage2.Oper
open import FormalLanguage2.Equals
open import Logic.Propositional
open import Operator.Equals
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
open import Structure.Setoid
open import Structure.Relator
open import Syntax.Implication
open import Type

-- TODO: Prove all of these: http://www.cse.chalmers.se/~abela/jlamp17.pdf

private variable ℓ : Lvl.Level
private variable Σ Σ₁ Σ₂ : Type{ℓ}

module _ where
  open Language renaming (accepts-ε to accepts ; suffix to suffix)

  open import Logic.IntroInstances
  open import Logic.Propositional.Equiv
  open import Structure.Set.Operators hiding (_∪_ ; _∩_ ; ∁ ; ∅ ; 𝐔)
  open import Structure.Set.Relators hiding (_≡_ ; _⊆_)

  instance
    [≅]-set-equality : SetEqualityRelation{E = Word Σ}(_∈_)(_∈_)(_≅_)
    SetEqualityRelation.membership [≅]-set-equality {A}{B} = [↔]-intro (l{A = A}{B = B}) (r{A = A}{B = B}) where
      l : ∀{A B : Language(Σ)} → (A ≅ B) ← (∀{w} → (w ∈ A) ↔ (w ∈ B))
      _≅_.accepts-ε (l {A = A} {B = B} p) with accepts A | accepts B | p{[]}
      ... | 𝑇 | 𝑇 | _ = [≡]-intro
      ... | 𝑇 | 𝐹 | q with () ← [↔]-to-[→] q <>
      ... | 𝐹 | 𝑇 | q with () ← [↔]-to-[←] q <>
      ... | 𝐹 | 𝐹 | _ = [≡]-intro
      _≅_.suffix (l {A = A} {B = B} p) {c} = l {A = suffix A c}{B = suffix B c} (\{w} → p{c ⊰ w})

      r : ∀{A B : Language(Σ)} → (A ≅ B) → (∀{w} → (w ∈ A) ↔ (w ∈ B))
      Tuple.left (r ab {[]}) wB = substitute₁ₗ(IsTrue) (_≅_.accepts-ε ab) wB
      Tuple.right (r ab {[]}) wA = substitute₁ᵣ(IsTrue) (_≅_.accepts-ε ab) wA
      Tuple.left (r {A} {B} ab {_⊰_ x w}) wB = [↔]-to-[←] (r(_≅_.suffix ab) {w}) wB
      Tuple.right (r {A} {B} ab {_⊰_ x w}) wA = [↔]-to-[→] (r(_≅_.suffix ab) {w}) wA

  instance
    [∪]-operator : UnionOperator{E = Word Σ}(_∈_)(_∈_)(_∈_)(_∪_)
    UnionOperator.membership [∪]-operator {A}{B}{w} = [↔]-intro (l{w = w}{A}{B}) (r{w = w}{A}{B}) where
      l : ∀{w}{A B} → (w ∈ (A ∪ B)) ← ((w ∈ A) ∨ (w ∈ B))
      l {w = []}    = [↔]-to-[←] IsTrue.preserves-[||][∨]
      l {w = c ⊰ w} = l {w = w}

      r : ∀{w}{A B} → (w ∈ (A ∪ B)) → ((w ∈ A) ∨ (w ∈ B))
      r {w = []}    = [↔]-to-[→] IsTrue.preserves-[||][∨]
      r {w = c ⊰ w} = r {w = w}

  instance
    [∩]-operator : IntersectionOperator{E = Word Σ}(_∈_)(_∈_)(_∈_)(_∩_)
    IntersectionOperator.membership [∩]-operator {A}{B}{w} = [↔]-intro (l{w = w}{A}{B}) (r{w = w}{A}{B}) where
      l : ∀{w}{A B} → (w ∈ (A ∩ B)) ← ((w ∈ A) ∧ (w ∈ B))
      l {w = []}    = [↔]-to-[←] IsTrue.preserves-[&&][∧]
      l {w = c ⊰ w} = l {w = w}

      r : ∀{w}{A B} → (w ∈ (A ∩ B)) → ((w ∈ A) ∧ (w ∈ B))
      r {w = []}    = [↔]-to-[→] IsTrue.preserves-[&&][∧]
      r {w = c ⊰ w} = r {w = w}

  instance
    [∁]-operator : ComplementOperator{E = Word Σ}(_∈_)(_∈_)(∁_)
    ComplementOperator.membership [∁]-operator {A}{w} = [↔]-intro (l{w = w}{A}) (r{w = w}{A}) where
      l : ∀{w}{A} → (w ∈ (∁ A)) ← ¬(w ∈ A)
      l {w = []}    = [↔]-to-[←] IsTrue.preserves-[!][¬]
      l {w = c ⊰ w} = l {w = w}

      r : ∀{w}{A} → (w ∈ (∁ A)) → ¬(w ∈ A)
      r {w = []} = [↔]-to-[→] IsTrue.preserves-[!][¬]
      r {w = c ⊰ w} = r {w = w}

  instance
    [∅]-set : EmptySet{E = Word Σ}(_∈_)(∅)
    EmptySet.membership [∅]-set {x = w} = p{w = w} where
      p : ∀{w} → ¬(w ∈ ∅)
      p {w = []} ()
      p {w = x ⊰ w} = p {w = w}

  instance
    [𝐔]-set : UniversalSet{E = Word Σ}(_∈_)(𝐔)
    UniversalSet.membership [𝐔]-set {x = w} = p{w = w} where
      p : ∀{w} → (w ∈ 𝐔)
      p {w = []}    = [⊤]-intro
      p {w = c ⊰ w} = p {w = w}

  [ε]-set : ∀{x : Word Σ} → (x ∈ ε) ↔ (x ≡ [])
  [ε]-set {x = x} = [↔]-intro (l{x}) (r{x}) where
    l : ∀{x} → (x ∈ ε) ← (x ≡ [])
    l {[]} [≡]-intro = [⊤]-intro

    r : ∀{x} → (x ∈ ε) → (x ≡ [])
    r {[]}    _     = [≡]-intro
    r {a ⊰ l} proof with () ← [∅]-membership {x = l} proof

  [𝁼]-membershipₗ : ∀{A B : Language(Σ)}{x y} → (x ∈ A) → (y ∈ B) → ((x ++ y) ∈ (A 𝁼 B))
  [𝁼]-membershipₗ {A = A}{B = B}{x = []}{[]} xA yB with accepts A | accepts B
  ... | 𝑇 | 𝑇 = <>
  [𝁼]-membershipₗ {A = A}{B = B}{x = []}{c ⊰ y} xA yB with accepts A
  ... | 𝑇 = [↔]-to-[←] ([∪]-membership {A = suffix A c 𝁼 B} {B = suffix B c} {x = y}) ([∨]-introᵣ yB)
  [𝁼]-membershipₗ {A = A}{B = B}{x = c ⊰ x}{y} xA yB with accepts A
  ... | 𝑇 = [↔]-to-[←] ([∪]-membership {A = suffix A c 𝁼 B} {B = suffix B c} {x = x ++ y}) ([∨]-introₗ ([𝁼]-membershipₗ {A = suffix A c}{B = B}{x = x}{y} xA yB))
  ... | 𝐹 = [𝁼]-membershipₗ {A = suffix A c}{B = B}{x = x}{y} xA yB

  import      Data.Boolean.Stmt.Logic as Bool
  open import Data.Tuple
  open import Functional
  open import Lang.Inspect
  open import Logic.Predicate
  open import Structure.Operator

  module [𝁼]-membership where
    -- Split up a concatenated word from two languages.
      -- Note: In the case of an ambiguity, the path in the proof `wAB` is used. (e.g. A = {"yes","no"}+ and B = {"no","maybe"}+ and w = "yesnono", (a,b) can be either ("yes","nono") or ("yesno","no"))
    -- Example: unconcat ({"a","b","c"}+) ({"1","2","3"}+) "abbccc321" = ("abbccc" , "321")
    unconcat : (A : Language(Σ)) → (B : Language(Σ)) → (w : Word(Σ)) → ⦃ wAB : w ∈ (A 𝁼 B) ⦄ → (Word(Σ) ⨯ Word(Σ))
    unconcat _ _ [] ⦃ xAB ⦄ = ([] , [])
    unconcat A _ (c ⊰ w) ⦃ xAB ⦄ with accepts A
    ... | 𝐹 = let (a , b) = unconcat _ _ w ⦃ xAB ⦄ in (c ⊰ a , b)
    ... | 𝑇 = [∨]-elim
      (\xsAB → let (a , b) = unconcat _ _ w ⦃ xsAB ⦄ in (c ⊰ a , b))
      (\_ → ([] , c ⊰ w))
      ([↔]-to-[→] ([∪]-membership {x = w}) xAB)

    [++]-unconcat-inverse : ∀{A B : Language(Σ)}{w}{wAB} → let (a , b) = unconcat A B w ⦃ wAB ⦄ in (a ++ b ≡ w)
    [++]-unconcat-inverse {w = []} = [≡]-intro
    [++]-unconcat-inverse {A = A}{w = c ⊰ w} {wAB = wAB} with accepts A
    ... | 𝐹 = congruence₂-₂(_⊰_)(c) ([++]-unconcat-inverse{w = w})
    ... | 𝑇 with [↔]-to-[→] ([∪]-membership {x = w}) wAB
    ... |   [∨]-introₗ wAB' = congruence₂-₂(_⊰_)(c) ([++]-unconcat-inverse{w = w}{wAB = wAB'})
    ... |   [∨]-introᵣ _    = [≡]-intro

    unconcat-membership : ∀{A B : Language(Σ)}{w}{wAB} → let (a , b) = unconcat A B w ⦃ wAB ⦄ in ((a ∈ A) ∧ (b ∈ B))
    unconcat-membership {A = A}{w = []} {wAB = wAB} with Bool.bivalence{accepts A}
    ... | [∨]-introₗ ta = [∧]-intro (Bool.IsTrue.[∧]-elimₗ wAB) (Bool.IsTrue.[∧]-elimᵣ wAB)
    ... | [∨]-introᵣ fa with () ← [↔]-to-[→] Bool.IsTrue.preserves-[!][¬] fa (Bool.IsTrue.[∧]-elimₗ wAB)
    unconcat-membership {A = A}{w = c ⊰ w}{wAB = wAB} with accepts A | inspect accepts A
    ... | 𝐹 | _ = unconcat-membership{w = w}{wAB = wAB}
    ... | 𝑇 | intro ta with [↔]-to-[→] ([∪]-membership {x = w}) wAB
    ... |   [∨]-introₗ wAB' = unconcat-membership{w = w}{wAB = wAB'}
    ... |   [∨]-introᵣ wB   = [∧]-intro ([↔]-to-[←] Bool.IsTrue.is-𝑇 ta) wB

  [𝁼]-membership : ∀{A B : Language(Σ)}{x} → (x ∈ (A 𝁼 B)) ↔ ∃{Obj = Word Σ ⨯ Word Σ}(\(a , b) → (a ++ b ≡ x) ∧ ((a ∈ A) ∧ (b ∈ B)))
  [𝁼]-membership {A = A}{B = B}{x = x} = [↔]-intro
    (\{ ([∃]-intro (a , b) ⦃ [∧]-intro eq ([∧]-intro pa pb) ⦄) → substitute₂-₁ᵣ(_∈_)(_) eq ([𝁼]-membershipₗ {x = a}{y = b} pa pb) })
    (\xAB → [∃]-intro ([𝁼]-membership.unconcat A B x ⦃ xAB ⦄) ⦃ [∧]-intro [𝁼]-membership.[++]-unconcat-inverse ([𝁼]-membership.unconcat-membership{w = x}) ⦄)

  {-
  module _
    {ℓ} (P : (A : Language(Σ)) → (B : Language(Σ)) → (w : Word(Σ)) → ⦃ wAB : w ∈ (A 𝁼 B) ⦄ → (Word(Σ) ⨯ Word(Σ)) → Type{ℓ})
    (pempty : ∀{A B} ⦃ wAB ⦄ → P A B [] ⦃ wAB ⦄ ([] , []))
    
    where

    unconcat-intro : ∀{A B}{w} ⦃ wAB ⦄ → P A B w ⦃ wAB ⦄ (unconcat A B w)
    unconcat-intro {A} {B} {w} ⦃ wAB ⦄ with accepts A | wAB
    unconcat-intro {A} {B} {[]} ⦃ wAB ⦄ | _ | wAB' = pempty{A = A}{B = B} ⦃ wAB' ⦄
    unconcat-intro {A} {B} {x ⊰ w} ⦃ wAB ⦄ | 𝑇 | wAB' = {!!}
    unconcat-intro {A} {B} {x ⊰ w} ⦃ wAB ⦄ | 𝐹 | wAB' = {!!}
  -}

  {-
  module _
    {_□_ : Language(Σ) → Language(Σ) → Language(Σ)}
    {_▫_ : Word Σ → Word Σ → Word Σ}
    (membership : ∀{A B}{x} → (x ∈ (A □ B)) ↔ ∃{Obj = _ ⨯ _}(\(a , b) → (a ▫ b ≡ x) ∧ ((a ∈ A) ∧ (b ∈ B))))
    where

    import      Structure.Operator.Names as Names
    open import Structure.Operator.Properties
    open import Syntax.Implication

    instance
      [□][∪]-distributivityₗ : Distributivityₗ ⦃ [≅]-equiv {Σ = Σ}⦄ (_□_)(_∪_)
      [□][∪]-distributivityₗ = intro p where
        p : Names.Distributivityₗ ⦃ [≅]-equiv {Σ = Σ}⦄ (_□_)(_∪_)
        p{A}{B}{C} = [↔]-to-[←] [≡]-membership \{x} →
          x ∈ (A □ (B ∪ C))       ⇔-[ {!!} ]
          ∃{Obj = _ ⨯ _}(\(a , bc) → (a ▫ bc ≡ x) ∧ ((a ∈ A) ∧ (bc ∈ B ∪ C))) ⇔-[ {!!} ]
          ∃{Obj = _ ⨯ _}(\(a , b) → (a ▫ b ≡ x) ∧ ((a ∈ A) ∧ (b ∈ B))) ∨ ∃{Obj = _ ⨯ _}(\(a , b) → (a ▫ b ≡ x) ∧ ((a ∈ A) ∧ (b ∈ C))) ⇔-[ {!!} ]
          (x ∈ (A □ B)) ∨ (x ∈ (A □ C)) ⇔-[ {!!} ]
          x ∈ (A □ B) ∪ (A □ C)         ⇔-end
  -}

  {-
  x ∈ A 𝁼 (B ∪ C)
  ∃(a , bc). (a ∈ A) ∧ (bc ∈ B ∪ C)
  ∃(a , bc). (a ∈ A) ∧ ((bc ∈ B) ∨ (bc ∈ C))
  ∃(a , bc). ((a ∈ A) ∧ (bc ∈ B)) ∨ ((a ∈ A) ∧ (bc ∈ C))

  (∃(a , b). (a ∈ A) ∧ (b ∈ B)) ∨ (∃(a , c). (a ∈ A) ∧ (c ∈ C))
  (x ∈ A 𝁼 B) ∨ (x ∈ A 𝁼 C)
  x ∈ (A 𝁼 B) ∪ (A 𝁼 C)
  -}

  open import Data.List as List using (List)
  import      Data.List.Relation.Quantification as List
  open import Numeral.Finite
  open import Numeral.Natural
  import      Numeral.CoordinateVector as Vec
  open import Structure.Function
  open import Syntax.Transitivity

  module [^]-set where
    unconcat : (L : Language(Σ)) → (w : Word(Σ)) → (n : ℕ) → ⦃ wL : w ∈ (L ^ n) ⦄ → List(Word(Σ))
    unconcat L w 𝟎     ⦃ wL ⦄ = []
    unconcat L w (𝐒 n) ⦃ wL ⦄ =
      let (a , b) = [𝁼]-membership.unconcat L (L ^ n) w ⦃ wL ⦄
      in a ⊰ unconcat L b n ⦃ [∧]-elimᵣ ([𝁼]-membership.unconcat-membership {w = w}{wAB = wL}) ⦄

    module _ {L : Language(Σ)} where
      unconcat-length : ∀{n}{w}{wL : w ∈ (L ^ n)} → (List.length(unconcat L w n ⦃ wL ⦄) ≡ n)
      unconcat-length {𝟎}   = [≡]-intro
      unconcat-length {𝐒 n} = congruence₁(𝐒) (unconcat-length {n})

      concat-unconcat-inverse : ∀{n}{w}{wL : w ∈ (L ^ n)} → (List.concat(unconcat L w n ⦃ wL ⦄) ≡ w)
      concat-unconcat-inverse {𝟎}{w}{wL} =
        List.concat(unconcat L [] 𝟎) 🝖[ _≡_ ]-[]
        List.concat []               🝖[ _≡_ ]-[]
        []                           🝖[ _≡_ ]-[ [↔]-to-[→] [ε]-set wL ]-sym
        w 🝖-end
      concat-unconcat-inverse {𝐒 n}{w}{wL} = let (a , b) = [𝁼]-membership.unconcat L (L ^ n) w ⦃ _ ⦄ in
        List.concat(unconcat L w (𝐒(n)) ⦃ _ ⦄) 🝖[ _≡_ ]-[]
        List.concat(a ⊰ unconcat L b n ⦃ _ ⦄)  🝖[ _≡_ ]-[]
        a ++ List.concat(unconcat L b n ⦃ _ ⦄) 🝖[ _≡_ ]-[ congruence₂-₂(_++_)(a) (concat-unconcat-inverse {n}{Tuple.right ([𝁼]-membership.unconcat L (L ^ n) w ⦃ _ ⦄)}{_}) ]
        a ++ b                                 🝖[ _≡_ ]-[ [𝁼]-membership.[++]-unconcat-inverse {A = L}{B = L ^ n}{w}{wL} ]
        w 🝖-end

      unconcat-membership : ∀{n}{w}{wL : w ∈ (L ^ n)} → List.AllElements(_∈ L) (unconcat L w n ⦃ wL ⦄)
      unconcat-membership {𝟎}  {w}{wL} = List.∅
      unconcat-membership {𝐒 n}{w}{wL} = [∧]-elimₗ([𝁼]-membership.unconcat-membership {w = w}{wAB = wL}) List.⊰ unconcat-membership{n}

  module _ {L : Language(Σ)} where
    [^]-setₗ : ∀{n}{ws : 𝕟(n) → Word(Σ)} → (∀{i} → (ws(i) ∈ L)) → (Vec.foldᵣ(_++_) [] ws ∈ (L ^ n))
    [^]-setₗ {ℕ.𝟎}       member = [↔]-to-[←] ([ε]-set {Σ = Σ}) [≡]-intro
    [^]-setₗ {ℕ.𝐒 n}{ws} member = [𝁼]-membershipₗ {A = L}{B = L ^ n}{x = Vec.head ws}{y = Vec.foldᵣ(_++_) [] (Vec.tail ws)} (member{𝕟.𝟎}) ([^]-setₗ {n}{Vec.tail ws} (\{i} → member{𝐒(i)}))


    {-
    open import Numeral.Natural.Proofs
    open import Structure.Function.Domain
    index : ∀{ℓ}{T : Type{ℓ}}{n} → (l : List(T)) → .(List.length l ≡ n) → 𝕟(n) → T
    index List.∅       () 𝟎    
    index List.∅       () (𝐒 _)
    index (x List.⊰ l) _  𝟎     = x
    index (x List.⊰ l) p  (𝐒 n) = index l (injective(𝐒) p) n
    -}

    [^]-set : ∀{n}{w} → (w ∈ (L ^ n)) ↔ ∃{Obj = 𝕟(n) → Word(Σ)}(ws ↦ (Vec.foldᵣ(_++_) [] ws ≡ w) ∧ (∀{i} → (ws(i) ∈ L)))
    [^]-set {n = n}{w} = [↔]-intro
      (\{ ([∃]-intro ws ⦃ [∧]-intro eq member ⦄) → substitute₂-₁ᵣ(_∈_)(L ^ n) eq ([^]-setₗ{ws = ws} member) })
      r -- (\wL → [∃]-intro (index([^]-set.unconcat L w n ⦃ wL ⦄) [^]-set.unconcat-length) ⦃ [∧]-intro {!!} {!!} ⦄)
      where
        -- TODO: How to construct
        postulate r : ∀{L : Language(Σ)}{n}{w} → (w ∈ (L ^ n)) → ∃{Obj = 𝕟(n) → Word(Σ)}(ws ↦ (Vec.foldᵣ(_++_) [] ws ≡ w) ∧ (∀{i} → (ws(i) ∈ L)))

  module [*]-set where
    -- TODO: How to construct    
    postulate unconcat : (L : Language(Σ)) → (w : Word(Σ)) → ⦃ wL : w ∈ (L *) ⦄ → List(Word(Σ))
    -- unconcat []      ⦃ wL ⦄ = []
    -- unconcat (c ⊰ w) ⦃ wL ⦄ =
    --   let (a , b) = unconcat(suffix L c) (L *) w ⦃ wL ⦄
    --  in a ⊰ unconcat* b ⦃ {!!} ⦄

    module _ {L : Language(Σ)} where
      postulate concat-unconcat-inverse : ∀{w}{wL : w ∈ (L *)} → (List.concat(unconcat L w ⦃ wL ⦄) ≡ w)
      postulate unconcat-membership : ∀{w}{wL : w ∈ (L *)} → List.AllElements(_∈ L) (unconcat L w ⦃ wL ⦄)

  module _ {L : Language(Σ)} where
    [*]-setₗ : ∀{ws : List(Word(Σ))} → (List.AllElements(_∈ L) ws) → (List.concat ws ∈ (L *))
    [*]-setₗ {[]}           List.∅           = <>
    [*]-setₗ {[] ⊰ ws}      (wL List.⊰ perm) = [*]-setₗ {ws} perm
    [*]-setₗ {(c ⊰ w) ⊰ ws} (wL List.⊰ perm) = [𝁼]-membershipₗ {A = suffix L c}{B = L *}{x = w}{y = List.concat ws} wL ([*]-setₗ {ws} perm)

    [*]-set : ∀{w} → (w ∈ (L *)) ↔ ∃{Obj = List(Word(Σ))}(ws ↦ (List.concat ws ≡ w) ∧ (List.AllElements(_∈ L) ws))
    [*]-set = [↔]-intro
      (\{ ([∃]-intro ws ⦃ [∧]-intro eq member ⦄) → substitute₂-₁ᵣ(_∈_)(L *) eq ([*]-setₗ{ws = ws} member) })
      (\wL → [∃]-intro ([*]-set.unconcat _ _ ⦃ wL ⦄) ⦃ [∧]-intro [*]-set.concat-unconcat-inverse [*]-set.unconcat-membership ⦄)

  [??]-set : ∀{L : Language(Σ)}{w} → (w ∈ (L ??)) ↔ ((w ∈ L) ∨ (w ≡ []))
  [??]-set {L = L}{w} = [↔]-intro (l{w = w}) (r{w = w}) where
    l : ∀{w} → (w ∈ (L ??)) ← ((w ∈ L) ∨ (w ≡ []))
    l {[]}    _ = <>
    l {c ⊰ w} ([∨]-introₗ p) = p
    l {c ⊰ w} ([∨]-introᵣ ())

    r : ∀{w} → (w ∈ (L ??)) → ((w ∈ L) ∨ (w ≡ []))
    r {[]}    p = [∨]-introᵣ [≡]-intro
    r {c ⊰ w} p = [∨]-introₗ p

  symbolFilter-set : ∀{f : Σ → Bool}{w} → (w ∈ symbolFilter f) ↔ ∃(c ↦ IsTrue(f(c)) ∧ (w ≡ List.singleton c))
  symbolFilter-set {Σ = Σ}{f = f}{w} = [↔]-intro (\([∃]-intro c ⦃ [∧]-intro tc eq ⦄) → substitute₂-₁ₗ(_∈_)(_) eq (l tc)) (\p → [∃]-intro (rGen{w} p) ⦃ [∧]-intro (rTrue{w} p) (rEq{w} p) ⦄) where
    l : ∀{c} → IsTrue(f(c)) → (List.singleton c ∈ symbolFilter f)
    l {c} p with f(c)
    ... | 𝑇 = p

    rGen : ∀{w} → (w ∈ symbolFilter f) → Σ
    rGen {[]}    ()
    rGen {c ⊰ _} _ = c

    rTrue : ∀{w} → (p : w ∈ symbolFilter f) → IsTrue(f(rGen{w}(p)))
    rTrue {[]}    ()
    rTrue {c ⊰ w} p with f(c)
    ... | 𝑇 = <>
    ... | 𝐹 with () ← [∅]-membership {x = w} p

    rEq : ∀{w} → (p : w ∈ symbolFilter f) → (w ≡ List.singleton(rGen{w} p))
    rEq {[]}    ()
    rEq {c ⊰ w} p with f(c)
    ... | 𝑇 = congruence₂-₂(_⊰_)(c) ([↔]-to-[→] [ε]-set p)
    ... | 𝐹 with () ← [∅]-membership {x = w} p

  postulate symbol-set : ⦃ equiv-dec : EquivDecidable(Σ) ⦄ → ∀{c : Σ}{w} → (w ∈ symbol ⦃ equiv-dec = equiv-dec ⦄ c) ↔ (w ≡ List.singleton c)
  -- symbol-set {c = c}{w = w} = symbolFilter-set{f = c ==_}{w = w} ⇔ {!!}
  

  -- TODO: Set properties
  -- TODO: Connection with logic (from sets) in relations
  -- open import Structure.Set.Operators.Proofs.LogicalOperator

  {- TODO: This may not be neccesary to prove separately if [□][∪]-distributivityₗ is proven
  open import Structure.Operator
  import      Structure.Operator.Names as Names
  open import Structure.Operator.Proofs.Util
  open import Structure.Operator.Properties
  open import Syntax.Transitivity

  instance postulate [∪]-function : BinaryOperator ⦃ [≅]-equiv ⦄ ⦃ [≅]-equiv ⦄ ⦃ [≅]-equiv ⦄ (_∪_ {Σ = Σ})
  instance postulate [∪]-commutativity : Commutativity ⦃ [≅]-equiv ⦄ (_∪_ {Σ = Σ})
  instance postulate [∪]-associativity : Associativity ⦃ [≅]-equiv ⦄ (_∪_ {Σ = Σ})

  instance
    [𝁼][∪]-distributivityₗ : Distributivityₗ ⦃ [≅]-equiv {Σ = Σ}⦄ (_𝁼_)(_∪_)
    [𝁼][∪]-distributivityₗ = intro p where
      p : Names.Distributivityₗ ⦃ [≅]-equiv {Σ = Σ}⦄ (_𝁼_)(_∪_)
      _≅_.accepts-ε (p {x = x}) with accepts x
      ... | 𝑇 = [≡]-intro
      ... | 𝐹 = [≡]-intro
      _≅_.suffix (p {x = x}{y}{z}) {c} with accepts x | p{x = suffix x c}{y}{z}
      ... | 𝑇 | prev =
        ((suffix x c) 𝁼 (y ∪ z)) ∪ ((suffix y c) ∪ (suffix z c))                  🝖[ _≅_ ]-[ congruence₂-₁(_∪_)(_) prev ]
        (((suffix x c) 𝁼 y) ∪ ((suffix x c) 𝁼 z)) ∪ ((suffix y c) ∪ (suffix z c)) 🝖[ _≅_ ]-[ One.associate-commute4 (commutativity(_∪_)) ]
        (((suffix x c) 𝁼 y) ∪ (suffix y c)) ∪ (((suffix x c) 𝁼 z) ∪ (suffix z c)) 🝖[ _≅_ ]-end
      ... | 𝐹 | prev = prev
  -}
