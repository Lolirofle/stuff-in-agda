module Test.Numeral where
import Lvl
open import Relator.Equals{Lvl.𝟎}

module Modulo where
  module Zero where
    test0 : (0 mod₀ 0) ≡ 0
    test0 = [≡]-intro

    test1 : (1 mod₀ 0) ≡ 0
    test1 = [≡]-intro

    test2 : (2 mod₀ 0) ≡ 0
    test2 = [≡]-intro

  module One where
    test0 : (0 mod₀ 1) ≡ 0
    test0 = [≡]-intro

    test1 : (1 mod₀ 1) ≡ 0
    test1 = [≡]-intro

    test2 : (2 mod₀ 1) ≡ 0
    test2 = [≡]-intro

    test3 : (3 mod₀ 1) ≡ 0
    test3 = [≡]-intro

    test4 : (4 mod₀ 1) ≡ 0
    test4 = [≡]-intro

    test5 : (5 mod₀ 1) ≡ 0
    test5 = [≡]-intro

    test6 : (6 mod₀ 1) ≡ 0
    test6 = [≡]-intro

    test7 : (7 mod₀ 1) ≡ 0
    test7 = [≡]-intro

    test8 : (8 mod₀ 1) ≡ 0
    test8 = [≡]-intro

    test9 : (9 mod₀ 1) ≡ 0
    test9 = [≡]-intro

    test10 : (10 mod₀ 1) ≡ 0
    test10 = [≡]-intro

    test11 : (11 mod₀ 1) ≡ 0
    test11 = [≡]-intro

  module Two where
    test0 : (0 mod₀ 2) ≡ 0
    test0 = [≡]-intro

    test1 : (1 mod₀ 2) ≡ 1
    test1 = [≡]-intro

    test2 : (2 mod₀ 2) ≡ 0
    test2 = [≡]-intro

    test3 : (3 mod₀ 2) ≡ 1
    test3 = [≡]-intro

    test4 : (4 mod₀ 2) ≡ 0
    test4 = [≡]-intro

    test5 : (5 mod₀ 2) ≡ 1
    test5 = [≡]-intro

    test6 : (6 mod₀ 2) ≡ 0
    test6 = [≡]-intro

    test7 : (7 mod₀ 2) ≡ 1
    test7 = [≡]-intro

    test8 : (8 mod₀ 2) ≡ 0
    test8 = [≡]-intro

    test9 : (9 mod₀ 2) ≡ 1
    test9 = [≡]-intro

    test10 : (10 mod₀ 2) ≡ 0
    test10 = [≡]-intro

    test11 : (11 mod₀ 2) ≡ 1
    test11 = [≡]-intro

  module Three where
    test0 : (0 mod₀ 3) ≡ 0
    test0 = [≡]-intro

    test1 : (1 mod₀ 3) ≡ 1
    test1 = [≡]-intro

    test2 : (2 mod₀ 3) ≡ 2
    test2 = [≡]-intro

    test3 : (3 mod₀ 3) ≡ 0
    test3 = [≡]-intro

    test4 : (4 mod₀ 3) ≡ 1
    test4 = [≡]-intro

    test5 : (5 mod₀ 3) ≡ 2
    test5 = [≡]-intro

    test6 : (6 mod₀ 3) ≡ 0
    test6 = [≡]-intro

    test7 : (7 mod₀ 3) ≡ 1
    test7 = [≡]-intro

    test8 : (8 mod₀ 3) ≡ 2
    test8 = [≡]-intro

    test9 : (9 mod₀ 3) ≡ 0
    test9 = [≡]-intro

    test10 : (10 mod₀ 3) ≡ 1
    test10 = [≡]-intro

    test11 : (11 mod₀ 3) ≡ 2
    test11 = [≡]-intro
