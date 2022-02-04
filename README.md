# Heuristic-Driven Theory Projection in Haskell

See report.pdf for documentation.

Abstract: 

In (Schmidt et al. 2014), the authors provide an overview of Heuristic-Driven Theory Projection (HDTP), a logic-based computational model of analogical reasoning. In this framework, an agent's knowledge of a familiar domain S is represented as a first-order theory, which can be projected into another, less familiar domain T, by constructing a more general domain G, using anti-unification of formulas (Plotkin 1970). 

To our knowledge, there has been so far no implementation of HDTP in a functional programming language. In the following report, we provide a functional algorithm in Haskell for reproducing many of the aspects of HDTP laid out in (Schmidt 2014).
