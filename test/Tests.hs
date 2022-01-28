{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}


import Data.Foldable     (for_)
import Test.Hspec        (Spec, describe, it, shouldBe)
import Test.Hspec.Runner (configFastFail, defaultConfig, hspecWith)
import Data.String       (fromString)

import HDTP

main :: IO ()
main = hspecWith defaultConfig {configFastFail = True} specs

specs :: Spec
specs = describe "apply" $ for_ cases test
  where
    test Case{..} = it description $ (apply (fst input) (snd input)) `shouldBe` expected


data Case = Case { description :: String
                 , input       :: (Sub, Form)
                 , expected    :: Form
                 }

permFun :: Int -> Int
permFun 0 = 1
permFun 1 = 2
permFun 2 = 0
permFun x = x

cases :: [Case]
cases = [ Case { description = "Permutation dist(Y,X,T) > 0"
               , input       = (SP $ P ("Y", fun), Forall "T" (FT (PS "geq") [T (VS "F") [T (VS "Y") [], T (VS "X") [], T (VS "T") [] ]]))
               , expected    = Forall "T" (FT (PS "geq") [T (VS "F") [T (VS "X") [],T (VS "T") [],T (VS "Y") []]])
               }
        , Case { description = "Fixation fix X -> sun, mass(X) > mass(Y), "
               , input       = (SF $ F ("X", "sun"), FT (PS "leq") [ T (FS "mass") [T (VS "X") [] ], T (FS "mass") [T (VS "Y") [] ]  ] )
               , expected    = FT (PS "leq") [ T (FS "mass") [T (FS "sun") [] ], T (FS "mass") [T (VS "Y") [] ]  ]
               }
        ]

-- a0b1123b94254a9db443a84a612b51cc3f3ed537
