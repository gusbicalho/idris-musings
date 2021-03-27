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

intercalate : Semigroup a => a -> List a -> List a
intercalate sep = go
 where
  go : List a -> List a
  go [] = []
  go [a] = [a]
  go (a :: as) = a :: sep :: go as

public export
all : (Type -> Type) -> List Type -> Type
all constraint = foldr (\t, acc => (constraint t, acc)) ()

export
(all Show ts) => Show (HList ts) where
  show = brackets . concat . intercalate ", " . go
   where
    brackets : String -> String
    brackets s = "[" <+> s <+> "]"
    go : all Show as => HList as -> List String
    go [] = []
    go (a :: as) = show a :: go as
