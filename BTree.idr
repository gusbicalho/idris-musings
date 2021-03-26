module BTree

import HList
import Data.Vect

namespace Tree
  public export
  data Tree : Type -> Type where
    Bud : Tree a
    Node : a -> Tree a -> Tree a -> Tree a

  public export
  left : Tree a -> Maybe (Tree a)
  left (Node _ l _) = Just l
  left Bud = Nothing

  public export
  right : Tree a -> Maybe (Tree a)
  right (Node _ _ r) = Just r
  right Bud = Nothing

  public export
  inOrder : forall a. Tree a -> List a
  inOrder Bud = []
  inOrder (Node v left right) = inOrder left ++ (v :: inOrder right)

namespace SizedTree
  public export
  data SizedTree : (n : Nat) -> Type -> Type where
    Bud : SizedTree 0 a
    Node : {m: Nat} -> {n: Nat} -> a -> SizedTree m a -> SizedTree n a -> SizedTree (1 + m + n) a

  public export
  left : SizedTree (S k) a -> (n ** SizedTree n a)
  left (Node _ l _) = (_ ** l)

  public export
  right : SizedTree (S k) a -> (n ** SizedTree n a)
  right (Node _ _ r) = (_ ** r)

  flipEq : (x = y) -> (y = x)
  flipEq Refl = Refl

  rightSuccOverPlus : (m: Nat) -> (n:Nat) -> plus m (S n) = S (plus m n)
  rightSuccOverPlus Z Z = Refl
  rightSuccOverPlus Z (S n) = Refl
  rightSuccOverPlus (S m) n = cong S (rightSuccOverPlus m n)

  public export
  inOrder : SizedTree n a -> Vect n a
  inOrder Bud = []
  inOrder (Node val l r) = catParts (inOrder l) val (inOrder r)
   where
    catParts : {left : Nat} -> {right : Nat} -> Vect left a -> a -> Vect right a -> Vect (S (left + right)) a
    catParts l v r = rewrite flipEq $ rightSuccOverPlus left right in (l ++ (val :: r))

namespace HTree
  public export
  data HTree : Tree Type -> Type where
    Bud : HTree Bud
    Node : t -> HTree left -> HTree right -> HTree (Node t left right)

  public export
  left : HTree (Node _ l _) -> HTree l
  left (Node _ l _) = l

  public export
  right : HTree (Node _ _ r) -> HTree r
  right (Node _ _ r) = r

  public export
  inOrder : HTree t -> HList (Tree.inOrder t)
  inOrder Bud = []
  inOrder (Node val left right) = inOrder left ++ (val :: inOrder right)
