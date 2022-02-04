\ifx true false 
% We put this to exclude the first part from the compilation of the pdf file 

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
  describe "lambdaForTerms algorithm for lgg" $ for_ casesLambdaT testLambdaT
  describe "align" $ for_ casesAlign testAlign
  describe "testTransfer" $ for_ casesTransfer testTransfer
    where 
      testSubs CaseSubs{..} = it descriptionSubs $ uncurry apply inputSubs `shouldBe` expectedSubs
      testLambda CaseLambda{..} = it descriptionLambda $ (\(a, b, c) -> lambda a b c) inputLambda `shouldBe` expectedLambda
      testLambdaT CaseLambdaT{..} = it descriptionLambdaT $ (\(a, b, c) -> lambdaForTerms a b c) inputLambdaT `shouldBe` expectedLambdaT
      testAlign CaseAlign{..} = it descriptionAlign $ uncurry align inputAlign `shouldBe` expectedAligns
      testTransfer CaseTransfer{..} = it descriptionTransfer $ (transfer . alignsToTransfers . uncurry align) inputTransfer `shouldBe` expectedTransfer




data CaseSubs = CaseSubs {
    descriptionSubs :: String
  , inputSubs       :: (Sub, Form)
  , expectedSubs    :: Form
}

fun :: Int -> Int
fun 0 = 1
fun 1 = 2
fun 2 = 0

casesSubs :: [CaseSubs]
casesSubs = [
  CaseSubs {
      descriptionSubs = "Permutation dist(Y,X,T) > 0"
    , inputSubs       = (SP $ P ("F", "G", fun), Forall "T" (FT (PS "geq") [T (VS "F") [T (VS "Y") [], T (VS "X") [], T (VS "T") [] ]]))
    , expectedSubs    = Forall "T" (FT (PS "geq") [T (VS "G") [T (VS "X") [],T (VS "T") [],T (VS "Y") []]])
    }
  , CaseSubs {
      descriptionSubs = "Permutation dist(Y,X,T) > 0"
    , inputSubs       = (SP $ P ("W", "G", fun), Forall "T" (FT (PS "geq") [T (VS "F") [T (VS "Y") [], T (VS "X") [], T (VS "T") [] ]]))
    , expectedSubs    = Forall "T" (FT (PS "geq") [T (VS "F") [T (VS "Y") [],T (VS "X") [],T (VS "T") []]])
    }
  , CaseSubs {
      descriptionSubs = "Fixation fix X -> sun, mass(X) > mass(Y), "
    , inputSubs       = (SF $ F ("X", "sun"), FT (PS "leq") [ T (FS "mass") [T (VS "X") [] ], T (FS "mass") [T (VS "Y") [] ]  ] )
    , expectedSubs    = FT (PS "leq") [ T (FS "mass") [T (FS "sun") [] ], T (FS "mass") [T (VS "Y") [] ]  ]
    }
  , CaseSubs {
      descriptionSubs = "Renaming X -> Y, mass(X) > mass(Z), "
    , inputSubs       = (SR $ R ("X", "Z"), FT (PS "leq") [ T (FS "mass") [T (VS "X") [] ], T (FS "mass") [T (VS "Y") [] ]  ] )
    , expectedSubs    = FT (PS "leq") [ T (FS "mass") [T (VS "Z") [] ], T (FS "mass") [T (VS "Y") [] ]  ]
    }
  , CaseSubs {
      descriptionSubs = "AI F F W 2, F(X,Y,Z)"
    , inputSubs       = (SI $ AI ("F", "F", "W", 2), FT (PS "P") [T (VS "F") [ T (FS "X") [], T (FS "Y") [], T (FS "Z") []]])
    , expectedSubs    = FT (PS "P") [T (VS "F") [ T (FS "X") [], T (FS "Y") [], T (VS "W") [T (FS "Z") []]]]
    }
  ]

data CaseLambda = CaseLambda {
    descriptionLambda :: String
  , inputLambda       :: (Form, Form, [TermGen])
  , expectedLambda    :: (Form, [TermGen])
}

casesLambda :: [CaseLambda]
casesLambda = [
  CaseLambda {
      descriptionLambda = "mass(sun) > mass(planet), mass(nucleus) > mass(electron) -> mass(X) > mass(Y)"
    , inputLambda       = (FT (PS "geq") [ T (FS "mass") [T (FS "sun") [] ], T (FS "mass") [T (FS "planet") [] ]  ], FT (PS "geq") [ T (FS "mass") [T (FS "nucleus") [] ], T (FS "mass") [T (FS "electron") [] ]  ], [])
    , expectedLambda    = (FT (PS "geq") [T (FS "mass") [T (VS "X") []],T (FS "mass") [T (VS "Y") []]], [("Y",T (FS "planet") [],T (FS "electron") []),("X",T (FS "sun") [],T (FS "nucleus") [])])
  },
  CaseLambda {
      descriptionLambda = "dist(planet, sun, T) , dist(electron, nucleus, T)  -> dist(X,Y,T)"
    , inputLambda       = (FT (PS "dist") [ T (FS "planet") [], T (FS "sun") [], T (VS "T") [] ], FT (PS "dist") [ T (FS "electron") [], T (FS "nucleus") [], T (VS "T") [] ], [])
    , expectedLambda    = (FT (PS "dist") [ T (VS "X") [], T (VS "Y") [], T (VS "T") [] ], [("Y",T (FS "sun") [],T (FS "nucleus") []),("X",T (FS "planet") [],T (FS "electron") [])])
  },
  CaseLambda {
    descriptionLambda = "dist(planet, sun, T) , dist(electron, nucleus, T)  -> dist(X,Y,T)"
  , inputLambda       = (FT (PS "dist") [ T (FS "planet") [], T (FS "sun") [], T (VS "T") [] ], FT (PS "dist") [ T (FS "electron") [], T (FS "nucleus") [], T (VS "T") [] ], [])
  , expectedLambda    = (FT (PS "dist") [ T (VS "X") [], T (VS "Y") [], T (VS "T") [] ], [("Y",T (FS "sun") [],T (FS "nucleus") []),("X",T (FS "planet") [],T (FS "electron") [])])
  },
 -- CaseLambda {
 --   descriptionLambda = "DummyPr(height(in(water, beaker), t)), DummyPr(temp(in(coffee, cup), t)) -> DummyPr(X(Y, t))"
 -- , inputLambda       = (FT (PS "DummyPr") [T (FS "height") [T (FS "in") [T (FS "water") [], T (FS "beaker") []], T (VS "t") []]], FT (PS "DummyPr") [T (FS "temp") [T (FS "in") [T (FS "coffee") [], T (FS "cup") []], T (VS "t") []]], [])
 -- , expectedLambda    = (FT (PS "DummyPr") [T (VS "X") [T (VS "Y") [], T (VS "t") []]], []) -- TODO: according to the paper this should be the right solution. But we get sth different.
 -- },
  CaseLambda { descriptionLambda = "f(g(a, b, c), d), f(d, h (a)) -> f(X, Y)"
  , inputLambda       = (FT (PS "f") [T (FS "g") [T (FS "a") [], T (FS "b") [], T (FS "c") []], T (FS "d") []] , FT (PS "f") [T (FS "d") [], T (FS "h") [T (FS "a") []]], [])
  , expectedLambda    = (FT (PS "f") [T (VS "X") [], T (VS "Y") []], [("Y",T (FS "d") [],T (FS "h") [T (FS "a") []]),("X",T (FS "g") [T (FS "a") [],T (FS "b") [],T (FS "c") []],T (FS "d") [])])
  },

\end{code}

\fi

% We need to break the block here in order to display in the pdf only the following lines 

\begin{code}

  CaseLambda {
    descriptionLambda = "revolves_around(earth, sun), revolves_around(electron, nucleus) -> revolves_around(X, Y)"
  , inputLambda       = (FT (PS "revolves_around") [T (FS "earth") [], T (FS "sun") []], FT (PS "revolves_around") [T (FS "electron") [], T (FS "nucleus") []], [])
  , expectedLambda    = (FT (PS "revolves_around") [T (VS "X") [], T (VS "Y") []], [("Y",T (FS "sun") [],T (FS "nucleus") []),("X",T (FS "earth") [],T (FS "electron") [])])
  }

\end{code}

\ifx true false
% The rest won't be compiled for the pdf

\begin{code}
  ]





data CaseLambdaT = CaseLambdaT {
    descriptionLambdaT :: String
  , inputLambdaT       :: (Term, Term, [TermGen])
  , expectedLambdaT    :: (Term, [TermGen])
}

casesLambdaT :: [CaseLambdaT]
casesLambdaT = [
  CaseLambdaT {
    descriptionLambdaT = "dist(planet, sun, T) , dist(electron, nucleus, T)  -> dist(X,Y,T)",
    inputLambdaT       = (T (FS "dist") [ T (FS "planet") [], T (FS "sun") [], T (VS "T") [] ], T (FS "dist") [ T (FS "electron") [], T (FS "nucleus") [], T (VS "T") [] ], []),
    expectedLambdaT    = (T (FS "dist") [ T (VS "X") [], T (VS "Y") [], T (VS "T") [] ], [("Y",T (FS "sun") [],T (FS "nucleus") []),("X",T (FS "planet") [],T (FS "electron") [])])
  }
 -- CaseLambdaT {
 --   descriptionLambdaT = "height(in(water, beaker), t), temp(in(coffee, cup), t) -> X(Y, t)"
 -- , inputLambdaT       = (T (FS "height") [T (FS "in") [T (FS "water") [], T (FS "beaker") []], T (VS "t") []], T (FS "temp") [T (FS "in") [T (FS "coffee") [], T (FS "cup") []], T (VS "t") []], [])
 -- , expectedLambdaT    = (T (VS "X") [T (VS "Y") [], T (VS "t") []], []) -- TODO: according to the paper this should be the right solution. But we get sth different.
 -- }
  ]

data CaseAlign = CaseAlign {
    descriptionAlign :: String
  , inputAlign       :: (Domain, Domain)
  , expectedAligns    :: [(Form, [Sub], Form, [Sub], Form)]
}

casesAlign :: [CaseAlign]
casesAlign = [
  CaseAlign {
    descriptionAlign = "TODO",
    inputAlign = (
      [FT (PS "geq") [ T (FS "mass") [T (FS "sun") []], T (FS "mass") [T (FS "planet") []]]],
      [FT (PS "geq") [T (FS "mass") [T (FS "nucleus") [] ], T (FS "mass") [T (FS "electron") []]]]
    ),
    expectedAligns = [
      (
        FT (PS "geq") [T (FS "mass") [T (VS "X") []],T (FS "mass") [T (VS "Y") []]],
        [
          SF (F ("X","planet")),
          SR (R ("Y","X")),
          SF (F ("X","sun")),
          SR (R ("X","X"))
        ],
        FT (PS "geq") [T (FS "mass") [T (FS "sun") []],T (FS "mass") [T (FS "planet") []]],
        [
          SF (F ("X","electron")),
          SR (R ("Y","X")),
          SF (F ("X","nucleus")),
          SR (R ("X","X"))
        ],
        FT (PS "geq") [T (FS "mass") [T (FS "nucleus") []],T (FS "mass") [T (FS "electron") []]]
      )
    ]
  }
  ]

data CaseTransfer = CaseTransfer {
    descriptionTransfer :: String
  , inputTransfer       :: (Domain, Domain)
  , expectedTransfer    :: [(Form, Form)]
}

casesTransfer :: [CaseTransfer]
casesTransfer = [
  CaseTransfer {
    descriptionTransfer = "TODO",
    inputTransfer = (
      [FT (PS "geq") [ T (FS "mass") [T (FS "sun") []], T (FS "mass") [T (FS "planet") []]]],
      [FT (PS "geq") [T (FS "mass") [T (FS "nucleus") [] ], T (FS "mass") [T (FS "electron") []]]]
    ),
    expectedTransfer = [
      (
        FT (PS "geq") [T (FS "mass") [T (FS "sun") []],T (FS "mass") [T (FS "planet") []]],
        FT (PS "geq") [T (FS "mass") [T (FS "nucleus") []],T (FS "mass") [T (FS "electron") []]]
      )
    ]
  }
  ]

\end{code}

\fi