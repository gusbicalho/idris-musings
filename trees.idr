module Main

import HList
import BTree

t : Tree Int
t = Node 4
      (Node 2
        (Node 1 Bud Bud)
        (Node 3 Bud Bud))
      (Node 6
        (Node 5 Bud Bud)
        (Node 7 Bud Bud))

x : List Int
x = inOrder t

intercalate : Semigroup a => a -> List a -> List a
intercalate sep = go
 where
  go : List a -> List a
  go [] = []
  go [a] = [a]
  go (a :: as) = a :: sep :: go as

all : (Type -> Type) -> List Type -> Type
all constraint = foldr (\t, acc => (constraint t, acc)) ()

(all Show ts) => Show (HList ts) where
  show = brackets . concat . intercalate ", " . go
   where
    brackets : String -> String
    brackets s = "[" <+> s <+> "]"
    go : all Show as => HList as -> List String
    go [] = []
    go (a :: as) = show a :: go as

ht : HTree ?htT
ht =
  Node ()
    (Node "Foo" Bud Bud)
    (Node 2.3
      (Node ints Bud Bud)
      (Node True Bud Bud))
 where
  ints : List Integer
  ints = [5, 6, 7]

hl : HList ?hlT
hl = inOrder ht

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

main : IO ()
main = printLn hl
