Examples
========

> module HDTP.Examples where

Sorts
-----

> r = S "real"
> o = S "object"
> t = S "time"


Constants
---------

> sun = T (FS "s") []
> planet = T (FS "p") []


Functions
---------

> mass = FS "m"
> force = FS "f"
> distance = FS "d"
> gravity = FS "g"
> centrifugal = FS "c"


Predicates
----------

> revolvesAround = PS "ra"

% > predAr (PS "ra") = ([])

> form = FT revolvesAround [sun, planet]

Note: when the user defines their signature, we will prevent them from defining a non-sensical arity function, 
like one which allows predicates which take arguments, etc.

% > lambda :: Term -> Term -> [Sub] -> (Term, [Sub])
% > lambda t t' theta | t == t' = (t, theta)
% > lambda (T t t:ts) (T u u:us) theta | t == u = loop 
% >   loop 
