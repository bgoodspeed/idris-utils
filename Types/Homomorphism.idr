module Homomorphism


-- TODO why is isomorphism data ... instead of class? 
--data Hom : (Semigroup a, Semigroup b) => a -> b -> Type where
--  MkHom : a -> b -> (a -> b) -> Hom a b
{-
data Hom : Type -> Type -> Type where
  MkHom : (a -> b) -> Hom a b

class (Semigroup a, Semigroup b, Hom a b) => VerifiedHom a b where
  homomorphismRespectsBinaryOp : (h : Hom a b) -> (a1 : a) -> (a2 : a) -> (h (a1 <+> a2)) = (h a1) <+> (h a2)

-}


{-
data Iso : Type -> Type -> Type where
    MkIso : (to : a -> b) ->
                      (from : b -> a) ->
                                (toFrom : (y : b) -> to (from y) = y) ->
                                          (fromTo : (x : a) -> from (to x) = x) ->
                                                    Iso a b

                                                    -}

