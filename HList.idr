module HList

public export
data HList : List Type -> Type where
  Nil : HList []
  (::) : a -> HList ts -> HList (a :: ts)

export
(++) : HList as -> HList bs -> HList (as ++ bs)
(++) Nil bs = bs
(++) (a :: as) bs = a :: (as ++ bs)
