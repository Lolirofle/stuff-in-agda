module Logic.Classic lvl where

open import Data
open import Functional
import      Level as Lvl
open import Logic(lvl)
  using (¬_ ; _∧_ ; ⊥)
import      Logic(lvl) as Constructive
open import LogicTheorems(lvl)
  using ([¬¬]-intro)
open import Type

abstract
  Stmt : Set(Lvl.𝐒 lvl)
  Stmt = Constructive.Stmt

  private
    from : Constructive.Stmt → Stmt
    from stmt = stmt

    to : Stmt → Constructive.Stmt
    to stmt = stmt

  _⇒_ : Stmt → Stmt → Stmt
  _⇒_ X Y = X → Y

  ¬₂_ : Stmt → Stmt
  ¬₂_ = ¬_

-- postulate [¬¬]-elim : {X : Stmt} → (¬₂ (¬₂ X)) ⇒ X -- TODO: _⇒_ must be of type (Stmt → Stmt → Set n) because of ({X : Stmt} → _)



-- test[¬¬]-elim : {X : Stmt} → (¬ (¬ X)) → Classic X
-- test[¬¬]-elim x = [¬¬]-elim x

-- testClassic : {X : Stmt} → Stmt → ClassicStmt
-- testClassic x = x
