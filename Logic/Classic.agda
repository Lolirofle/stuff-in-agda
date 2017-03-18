module Logic.Classic lvl where

open import Data
open import Functional
import      Level as Lvl
open import Logic(lvl)
  using (Stmt ; ¬_ ; _∧_ ; ⊥)
import      Logic(lvl) as Constructive
open import LogicTheorems(lvl)
  using ([¬¬]-intro)
open import Type

-- data Classic : Stmt → Stmt where
--   [¬¬]-elim : {X : Stmt} → (¬ (¬ X)) → Classic(X)

-- intro : {X : Stmt} → X → (Classic X)
-- intro = [¬¬]-elim ∘ [¬¬]-intro

-- elim : {X : Stmt} → (Classic X) → (¬ (¬ X))
-- elim([¬¬]-elim x) = x

-- [→]-elim : {X Y : Stmt} → (Classic X) → (X → (Classic Y)) → (Classic Y)
-- [→]-elim{X}{Y}([¬¬]-elim nnx) xnny = [¬¬]-elim(([⊥]-elim ∘ nnx)
-- (¬ (¬ X)) → (X → (¬ (¬ Y))) → (¬ (¬ Y))
-- ((X → ⊥) → ⊥) → (X → ((Y → ⊥) → ⊥)) → ((Y → ⊥) → ⊥)
-- ((X → ⊥) → ⊥) → ((X → ((Y → ⊥) → ⊥)) → ((Y → ⊥) → ⊥))

-- [→]-elim : {X Y : Stmt} → ((Classic X) ⨯ (X → Y)) → (Classic Y)
-- [→]-elim = Tuple.uncurry(swap intro)

-- [→]-elim : {X Y : Stmt} → Classic(X → Y) → (Classic X) → (Classic Y)
-- [→]-elim f = 

postulate ClassicStmt : Set(Lvl.𝐒 lvl)
-- postulate map       : {X Y : Stmt} → (X → Y) → (Classic X) → (Classic Y)
-- postulate [¬¬]-elim : {X : Stmt} → (¬ (¬ (Classic X))) → Classic X

-- test[¬¬]-elim : {X : Stmt} → (¬ (¬ X)) → Classic X
-- test[¬¬]-elim x = [¬¬]-elim x

-- testClassic : {X : Stmt} → Stmt → ClassicStmt
-- testClassic x = x
