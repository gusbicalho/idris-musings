module HList

public export
data HList : List Type -> Type where
  Nil : HList []
  (::) : a -> HList ts -> HList (a :: ts)

export
(++) : HList as -> HList bs -> HList (as ++ bs)
(++) Nil bs = bs
(++) (a :: as) bs = a :: (as ++ bs)

export
hfilter : ((type : Type) -> (term : type) -> Bool) -> (ts ** HList ts) -> (us ** HList us)
hfilter pred = go
 where
  go : (as ** HList as) -> (bs ** HList bs)
  go ([] ** []) = (_ ** [])
  go ((t :: ts) ** (x :: xs)) =
    let (us ** ys) = go (ts ** xs)
    in
      if pred t x
      then ((t :: us) ** (x :: ys))
      else (us ** ys)
