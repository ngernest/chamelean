import Plausible.Chamelean.DeriveConstrainedProducer

open Plausible




-- Binary Search TreeMap implementation in Lean 4
inductive TreeMap : Type where
  | Leaf : TreeMap
  | Node : TreeMap → Nat → Nat → TreeMap → TreeMap
  deriving Repr


-- The operations under test
def find (key : Nat) : TreeMap → Option Nat
  | .Leaf => none
  | .Node l k' v r =>
    if key < k' then find key l
    else if k' < key then find key r
    else some v

def nil : TreeMap := .Leaf

def insert (key : Nat) (val : Nat) : TreeMap → TreeMap
  | .Leaf => .Node .Leaf key val .Leaf
  | .Node l k' v' r =>
    if key < k' then .Node (insert key val l) k' v' r
    else if k' < key then .Node l k' v' (insert key val r)
    else .Node l k' val r

mutual
  def delete (key : Nat) : TreeMap → TreeMap
    | .Leaf => .Leaf
    | .Node l k' v' r =>
      if key < k' then .Node (delete key l) k' v' r
      else if k' < key then .Node l k' v' (delete key r)
      else join l r

  -- Join function for delete operation
  def join : TreeMap → TreeMap → TreeMap
    | TreeMap.Leaf, r => r
    | l, TreeMap.Leaf => l
    | TreeMap.Node l k v r, TreeMap.Node l' k' v' r' =>
      TreeMap.Node l k v (TreeMap.Node (join r l') k' v' r')
end


mutual
def toList : TreeMap → List (Nat × Nat)
  | TreeMap.Leaf => []
  | TreeMap.Node l k v r => toList l ++ [(k, v)] ++ toList r

def keys (t : TreeMap) : List Nat :=
  (toList t).map (·.1)
end

def size (t : TreeMap) : Nat :=
  (keys t).length

-- Union and helper functions
mutual
  def union : TreeMap → TreeMap → TreeMap
    | TreeMap.Leaf, r => r
    | l, TreeMap.Leaf => l
    | TreeMap.Node l k v r, t =>
      TreeMap.Node (union l (below k t)) k v (union r (above k t))

  def below (key : Nat) : TreeMap → TreeMap
    | TreeMap.Leaf => TreeMap.Leaf
    | TreeMap.Node l k' v r =>
      if key ≤ k' then below key l
      else TreeMap.Node l k' v (below key r)

  def above (key : Nat) : TreeMap → TreeMap
    | TreeMap.Leaf => TreeMap.Leaf
    | TreeMap.Node l k' v r =>
      if k' ≤ key then above key r
      else TreeMap.Node (above key l) k' v r
end

-- Get all key-value pairs in insertion order (preorder traversal)
def insertions : TreeMap → List (Nat × Nat)
  | TreeMap.Leaf => []
  | TreeMap.Node l k v r => (k, v) :: insertions l ++ insertions r

-- Example usage and tests
#check TreeMap
#eval insert 5 50 (insert 3 30 (insert 7 70 nil))
#eval find 3 (insert 5 50 (insert 3 30 (insert 7 70 nil)))
#eval toList (insert 5 50 (insert 3 30 (insert 7 70 nil)))
