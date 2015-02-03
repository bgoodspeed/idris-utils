module Homomorphism

import Syntax.PreorderReasoning

-- TODO why is isomorphism data ... instead of class? 
--data Hom : (Semigroup a, Semigroup b) => a -> b -> Type where
--  MkHom : a -> b -> (a -> b) -> Hom a b
{-
data Hom : Type -> Type -> Type where
  MkHom : (a -> b) -> Hom a b

class (Semigroup a, Semigroup b, Hom a b) => VerifiedHom a b where
  homomorphismRespectsBinaryOp : (h : Hom a b) -> (a1 : a) -> (a2 : a) -> (h (a1 <+> a2)) = (h a1) <+> (h a2)

-}


data Hom : Type -> Type -> Type where
  MkHom : (Semigroup a, Semigroup b) => (h : a -> b) -> 
                                        (preservesGroup : (a1 : a) -> (a2 : a) -> h (a1 <+> a2) = (h a1) <+> (h a2)) -> Hom a b


homRefl : (Semigroup a) => Hom a a
homRefl = MkHom id (\x,y => Refl) 

-- (\x,y => ?prf ) 
homTrans : (Semigroup a, Semigroup b, Semigroup c) => Hom a b -> Hom b c -> Hom a c
homTrans (MkHom h preservesGroup) (MkHom h' preservesGroup') = 
  MkHom (\x => h' (h x)) (\x,y => ?prf )
        {- (\x,y => h' (h (x <+> y))        ={ rewrite preservesGroup x y              }=
                 h' (h(x) <+> h(y))      ={ preservesGroup' h(x) h(y)       }=
                 h'(h(x)) <+> h'(h(y))   QED
        ) 
        -}
{-
> intros
> compute
----------              Assumptions:              ----------
 a : Type
 b : Type
 h : a -> b
 constrarg : Semigroup a
 constrarg1 : Semigroup b
 preservesGroup : (a1 : a) ->
                  (a2 : a) -> h (a1 <+> a2) = h a1 <+> h a2
 c : Type
 h' : b -> c
 constrarg2 : Semigroup b
 constrarg3 : Semigroup c
 preservesGroup' : (a1 : b) ->
                   (a2 : b) -> h' (a1 <+> a2) = h' a1 <+> h' a2
 constrarg4 : Semigroup a
 constrarg5 : Semigroup b
 constrarg6 : Semigroup c
 constrarg7 : Semigroup a
 constrarg8 : Semigroup c
 x15 : a
 y : a
----------                 Goal:                  ----------
{hole103} : h' (h (x15 <+> y)) = h' (h x15) <+> h' (h y)
-Homomorphism.prf> rewrite preservesGroup x15 y
-- does not change the goal?  weird.

-}

{- TODO is this even true?
homSym : Hom a b -> Hom b a
homSym (MkHom h preservesGroup) = ?foo_1
-}
       

