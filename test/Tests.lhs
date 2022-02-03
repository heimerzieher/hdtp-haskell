\begin{code}

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}


import Data.Foldable     (for_)
import Test.Hspec        (Spec, describe, it, shouldBe)
import Test.Hspec.Runner (configFastFail, defaultConfig, hspecWith)

import HDTP

main :: IO ()
main = hspecWith defaultConfig {configFastFail = False} specs

specs :: Spec
specs = do
          describe "apply substitution" $ for_ casesSubs testSubs  
          describe "lambda algorithm for lgg" $ for_ casesLambda testLambda
                where 
                      testSubs CaseSubs{..} = it descriptionSubs $ (apply (fst inputSubs) (snd inputSubs)) `shouldBe` expectedSubs
                      testLambda CaseLambda{..} = it descriptionLambda $ (lambda (head $ map (\(a, _, _) -> a) (inputLambda : [])) (head $ map (\(_, b, _) -> b) (inputLambda : [])) (head $ map (\(_, _, c) -> c) (inputLambda : []))) `shouldBe` expectedLambda
       



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
casesLambda = [ CaseLambda { descriptionLambda = "mass(sun) > mass(planet), mass(nucleus) > mass(electron) -> mass(X) > mass(Y)"
               , inputLambda       = ((FT (PS "geq") [ T (FS "mass") [T (FS "sun") [] ], T (FS "mass") [T (FS "planet") [] ]  ]), (FT (PS "geq") [ T (FS "mass") [T (FS "nucleus") [] ], T (FS "mass") [T (FS "electron") [] ]  ]), [])
               , expectedLambda    = (FT (PS "geq") [T (FS "mass") [T (VS "X") []],T (FS "mass") [T (VS "Y") []]], [("Y",T (FS "planet") [],T (FS "electron") []),("X",T (FS "sun") [],T (FS "nucleus") [])])
               }
              , CaseLambda { descriptionLambda = "dist(planet, sun, T) , dist(electron, nucleus, T)  -> dist(X,Y,T)"
               , inputLambda       = ((FT (PS "dist") [ T (FS "planet") [], T (FS "sun") [], T (VS "T") [] ]), (FT (PS "dist") [ T (FS "electron") [], T (FS "nucleus") [], T (VS "T") [] ]), [])
               , expectedLambda    = (FT (PS "dist") [ T (VS "X") [], T (VS "Y") [], T (VS "T") [] ], [("Y",T (FS "sun") [],T (FS "nucleus") []),("X",T (FS "planet") [],T (FS "electron") [])])
               }
              , CaseLambda { descriptionLambda = "dist(planet, sun, T) , dist(electron, nucleus, T)  -> dist(X,Y,T)"
               , inputLambda       = ((FT (PS "dist") [ T (FS "planet") [], T (FS "sun") [], T (VS "T") [] ]), (FT (PS "dist") [ T (FS "electron") [], T (FS "nucleus") [], T (VS "T") [] ]), [])
               , expectedLambda    = (FT (PS "dist") [ T (VS "X") [], T (VS "Y") [], T (VS "T") [] ], [("Y",T (FS "sun") [],T (FS "nucleus") []),("X",T (FS "planet") [],T (FS "electron") [])])
               }

               , CaseLambda { descriptionLambda = "DummyPr(height(in(water, beaker), t)), DummyPr(temp(in(coffee, cup), t)) -> DummyPr(X(Y, t))"
               , inputLambda       = ((FT (PS "DummyPr") [T (FS "height") [T (FS "in") [T (FS "water") [], T (FS "beaker") []], T (VS "t") []]]), (FT (PS "DummyPr") [T (FS "temp") [T (FS "in") [T (FS "coffee") [], T (FS "cup") []], T (VS "t") []]]), [])
               , expectedLambda    = (FT (PS "DummyPr") [T (VS "X") [T (VS "Y") [], T (VS "t") []]], [])
               }

               , CaseLambda { descriptionLambda = "f(g(a, b, c), d), f(d, h (a)) -> f(X, Y)"
               , inputLambda       = (FT (PS "f") [T (FS "g") [T (FS "a") [], T (FS "b") [], T (FS "c") []], T (FS "d") []] , FT (PS "f") [T (FS "d") [], T (FS "h") [T (FS "a") []]], [])
               , expectedLambda    = (FT (PS "f") [T (VS "X") [], T (VS "Y") []], [("Y",T (FS "d") [],T (FS "h") [T (FS "a") []]),("X",T (FS "g") [T (FS "a") [],T (FS "b") [],T (FS "c") []],T (FS "d") [])])
               }

               , CaseLambda { descriptionLambda = "revolves_around(earth, sun), revolves_around(electron, nucleus) -> revolves_around(X, Y)"
               , inputLambda       = (FT (PS "revolves_around") [T (FS "earth") [], T (FS "sun") []], FT (PS "revolves_around") [T (FS "electron") [], T (FS "nucleus") []], [])
               , expectedLambda    = (FT (PS "revolves_around") [T (VS "X") [], T (VS "Y") []], [("Y",T (FS "sun") [],T (FS "nucleus") []),("X",T (FS "earth") [],T (FS "electron") [])])
               }

               

        ]

-- a0b1123b94254a9db443a84a612b51cc3f3ed537

\end{code}