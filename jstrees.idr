module Main

import Data.Vect
import BTree
import HList
import BrowserUtils

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
  consoleLog $ inOrder t
  consoleLog $ inOrder st
  consoleLog $ inOrder ht
