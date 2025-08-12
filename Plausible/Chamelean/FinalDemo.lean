import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveChecker
import Plausible.Gen
open Plausible

/-- Datatype for binary trees -/
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Repr

/-- `Between lo x hi` means `lo < x < hi` -/
inductive Between : Nat -> Nat -> Nat -> Prop where
| BetweenN : ∀ n m,
  n <= m →
  Between n (.succ n) (.succ (.succ m))
| BetweenS : ∀ n m o,
  Between n m o → Between n (.succ m) (.succ o)

#derive_generator (fun (x : Nat) => Between lo x hi)
#derive_checker (Between lo hi t)

/-- `BST lo hi t` describes whether a tree `t` is a BST that
    contains values strictly within `lo` and `hi` -/
inductive BST : Nat → Nat → Tree → Prop where
  | BSTLeaf: ∀ lo hi, BST lo hi .Leaf
  | BSTNode: ∀ lo hi x l r,
    Between lo x hi →
    BST lo x l →
    BST x hi r →
    BST lo hi (.Node x l r)

#derive_generator (fun (t : Tree) => BST lo hi t)
#derive_checker (BST lo hi t)



/-- Inserts an element into a tree, respecting the BST invariants -/
def insert (x : Nat) (t : Tree) : Tree :=
  match t with
  | .Leaf => .Node x .Leaf .Leaf
  | .Node y l r =>
    if x < y then
      .Node y (insert x l) r
    else if x > y then
      .Node y l (insert x r)
    else t

/-- Buggy insertion function: ignores the input tree and
    returns a two-node tree where both values are `x` -/
def buggyInsert (x : Nat) (_ : Tree) : Tree :=
  .Node x (.Node x .Leaf .Leaf) .Leaf

/-- Test harness for testing the property
    `∀ (x : Nat) (t : Tree), BST 0 10 t → BST 0 10 (insert x t)`
    for `numTrials` iterations.

    (Details omitted) -/
def runTests (numTrials : Nat) : IO Unit :=
  do
    let size := 10
    let useBuggyVersion : Bool := true
    let mut numSucceeded := 0
    for i in [:numTrials] do
      let x ← Gen.run (Subtype.val <$> Gen.chooseNatLt 1 10 (by decide)) size
      let maybeTree ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => BST 0 10 t) size) size
      match maybeTree with
      | some t =>
        let insertFn := if useBuggyVersion then buggyInsert else insert
        let t' := insertFn x t
        let b := DecOpt.decOpt (BST 0 10 t') size
        match b with
        | some bool =>
          if bool then
            numSucceeded := numSucceeded + 1
          else
            IO.println s!"Property falsified!\nt = {repr t}\nx = {x}\nt' = {repr t'}"
            return
        | none => IO.println s!"unable to decide BST validity for {repr t'}"
      | none => IO.println "unable to generate valid BST"
    IO.println s!"Chamelean: finished {numTrials} tests, {numSucceeded} passed"

-- Uncomment this to run the aforementioned test harness
#eval runTests (numTrials := 10000)
