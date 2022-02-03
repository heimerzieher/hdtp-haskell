\begin{code}

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}


import Data.Foldable     (for_)
import Test.Hspec        (Spec, describe, it, shouldBe)
import Test.Hspec.Runner (configFastFail, defaultConfig, hspecWith)

import HDTP

main :: IO ()
main = hspecWith defaultConfig {configFastFail = True} $ do
        
        describe "apply" $ do
               for_ casesSubs test where
                     test CaseSubs{..} = it descriptionSubs $ (apply (fst inputSubs) (snd inputSubs)) `shouldBe` expectedSubs
                     
        describe "lambda" $ do
               for_ casesSubs test where
                     test CaseSubs{..} = it descriptionSubs $ (apply (fst inputSubs) (snd inputSubs)) `shouldBe` expectedSubs



data CaseSubs = CaseSubs { descriptionSubs :: String
                 , inputSubs       :: (Sub, Form)
                 , expectedSubs    :: Form
                 }

casesSubs :: [CaseSubs]
casesSubs = [ CaseSubs { descriptionSubs = "Permutation dist(Y,X,T) > 0"
               , inputSubs       = (SP $ P ("F", "G", fun), Forall "T" (FT (PS "geq") [T (VS "F") [T (VS "Y") [], T (VS "X") [], T (VS "T") [] ]]))
               , expectedSubs    = Forall "T" (FT (PS "geq") [T (VS "G") [T (VS "X") [],T (VS "T") [],T (VS "Y") []]])
               }
        , CaseSubs { descriptionSubs = "Permutation dist(Y,X,T) > 0"
               , inputSubs       = (SP $ P ("W", "G", fun), Forall "T" (FT (PS "geq") [T (VS "F") [T (VS "Y") [], T (VS "X") [], T (VS "T") [] ]]))
               , expectedSubs    = Forall "T" (FT (PS "geq") [T (VS "F") [T (VS "Y") [],T (VS "X") [],T (VS "T") []]])
               }
        , CaseSubs { descriptionSubs = "Fixation fix X -> sun, mass(X) > mass(Y), "
               , inputSubs       = (SF $ F ("X", "sun"), FT (PS "leq") [ T (FS "mass") [T (VS "X") [] ], T (FS "mass") [T (VS "Y") [] ]  ] )
               , expectedSubs    = FT (PS "leq") [ T (FS "mass") [T (FS "sun") [] ], T (FS "mass") [T (VS "Y") [] ]  ]
               }
        , CaseSubs { descriptionSubs = "Renaming X -> Y, mass(X) > mass(Z), "
               , inputSubs       = (SR $ R ("X", "Z"), FT (PS "leq") [ T (FS "mass") [T (VS "X") [] ], T (FS "mass") [T (VS "Y") [] ]  ] )
               , expectedSubs    = FT (PS "leq") [ T (FS "mass") [T (VS "Z") [] ], T (FS "mass") [T (VS "Y") [] ]  ]
               }
        , CaseSubs { descriptionSubs = "AI F F W 2, F(X,Y,Z)"
               , inputSubs       = (SI $ AI ("F", "F", "W", 2), FT (PS "P") [T (VS "F") [ T (FS "X") [], T (FS "Y") [], T (FS "Z") []]])
               , expectedSubs    = FT (PS "P") [T (VS "F") [ T (FS "X") [], T (FS "Y") [], T (VS "W") [T (FS "Z") []]]]
               }
        ]


data CaseLambda = CaseLambda { descriptionLambda :: String
                 , inputLambda       :: (Form, Form, [Subs])
                 , expectedLambda    :: (Form, [Subs])
                 }

casesLambda :: [CaseLambda]
casesLambda = [ CaseLambda { descriptionLambda = "mass(sun) > mass(planet), mass(nucleus) > mass(electron)"
               , inputLambda       = ((FT (PS "geq") [ T (FS "mass") [T (FS "sun") [] ], T (FS "mass") [T (FS "planet") [] ]  ]), (FT (PS "geq") [ T (FS "mass") [T (FS "nucleus") [] ], T (FS "mass") [T (FS "electron") [] ]  ]), [])
               , expectedLambda    = (FT (PS "geq") [T (FS "mass") [T (VS "X") []],T (FS "mass") [T (VS "Y") []]], [])
               }

        ]

-- a0b1123b94254a9db443a84a612b51cc3f3ed537

\end{code}