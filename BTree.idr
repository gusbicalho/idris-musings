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
  data SizedTree : (n : Nat) -> Type -> Type where
    Bud : SizedTree 0 a
    Node : {m: Nat} -> {n: Nat} -> a -> SizedTree m a -> SizedTree n a -> SizedTree (1 + m + n) a

  public export
  left : SizedTree (S k) a -> (n ** SizedTree n a)
  left (Node _ l _) = (_ ** l)

  public export
  right : SizedTree (S k) a -> (n ** SizedTree n a)
  right (Node _ _ r) = (_ ** r)

  public export
  inOrder : SizedTree n a -> Vect n a
  inOrder Bud = []
  inOrder (Node val l r) = prove (inOrder l ++ (val :: inOrder r))
   where
    succOverPlus : (m: Nat) -> (n:Nat) -> plus m (S n) = S (plus m n)
    succOverPlus Z Z = Refl
    succOverPlus Z (S n) = Refl
    succOverPlus (S m) n = cong S (succOverPlus m n)
    vectSize : (m : Nat) -> (n : Nat) -> (m = n) -> Vect m a = Vect n a
    vectSize _ _ Refl = Refl
    prove : forall m, n. Vect (plus m (S n)) a -> Vect (S (plus m n)) a
    prove vect = ?prf -- rewrite vectSize (plus m (S n)) (S (plus m n)) (succOverPlus m n) in vect

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
