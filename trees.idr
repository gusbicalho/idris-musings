module Main

import Data.Vect
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

st : SizedTree 7 Int
st = Node 4
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

ht : HTree ?ht_
ht =
  Node ()
    (Node "Foo" Bud Bud)
    (Node 2.3
      (Node ints Bud Bud)
      (Node True Bud Bud))
 where
  ints : List Integer
  ints = [5, 6, 7]

main : IO ()
main = do
  printLn $ inOrder t
  printLn $ inOrder st
  printLn $ inOrder ht
