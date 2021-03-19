module Main

data Tree : Type -> Type where
  Bud : Tree a
  Node : a -> Tree a -> Tree a -> Tree a

inOrder : forall a. Tree a -> List a
inOrder t =
  case t of
    Bud => []
    Node v left right => inOrder left ++ (v :: inOrder right)

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

data HTree : Tree Type -> Type where
  HBud : HTree Bud
  HNode : t -> HTree left -> HTree right -> HTree (Node t left right)

data HList : List Type -> Type where
  HNil : HList []
  (-::) : a -> HList ts -> HList (a :: ts)
infixr 10 -::

interface HShow t where
  hshow : t -> List String

-- HShow (HList []) where
--   hshow HNil = []

-- (Show a, HShow (HList as)) => HShow (HList (a :: as)) where
--   hshow (a -:: as) = show a :: hshow as

-- HShow (HList ts) => Show (HList ts) where
--   show hl = show (hshow hl)

intercalate : Semigroup a => a -> List a -> List a
intercalate sep = go
 where
  go : List a -> List a
  go [] = []
  go [a] = [a]
  go (a :: as) = a :: sep :: go as

all : (Type -> Type) -> List Type -> Type
all constraint = foldr step ()
 where
  step : Type -> Type -> Type
  step t acc = (constraint t, acc)

(all Show ts) => Show (HList ts) where
  show = brackets . concat . intercalate ", " . go
   where
    brackets : String -> String
    brackets s = "[" <+> s <+> "]"
    go : all Show as => HList as -> List String
    go HNil = []
    go (a -:: as) = show a :: go as

hleft : HTree (Node _ left _) -> HTree left
hleft (HNode _ left _) = left

hright : HTree (Node _ _ right) -> HTree right
hright (HNode _ _ right) = right

(-++-) : HList as -> HList bs -> HList (as ++ bs)
infixr 9 -++-
(-++-) HNil bs = bs
(-++-) (a -:: as) bs = a -:: (as -++- bs)

hInOrder : HTree t -> HList (inOrder t)
hInOrder HBud = HNil
hInOrder (HNode val left right) = hInOrder left -++- (val -:: hInOrder right)

ht : HTree ?htT
ht =
  HNode ()
    (HNode  "Foo" HBud HBud)
    (HNode  2.3
      (HNode  [5, 6, 7] HBud HBud)
      (HNode  True HBud HBud))

hl : HList ?hlT
hl = hInOrder ht

main : IO ()
main = printLn hl
