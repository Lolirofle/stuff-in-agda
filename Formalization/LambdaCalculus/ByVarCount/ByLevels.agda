-- Examples:
--   (λf. λx. f x) is for example Abstract(Abstract(Apply(Var 0) (Var 1))) : Term(0)
--   (λx. x) is for example:
--     Abstract(Var 0) : Term(0)
--     Abstract(Var 1) : Term(1)
--     Abstract(Var 2) : Term(2)
--     …
-- Also called: DeBrujin levels.
module Formalization.LambdaCalculus.ByVarCount.ByLevels where
