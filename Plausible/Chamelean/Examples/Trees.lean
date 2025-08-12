import Plausible.Chamelean.Examples.ExampleInductiveRelations
import Plausible.Chamelean.OptionTGen
import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DecOpt

import Plausible.Gen
open Plausible
open OptionTGen

open ArbitrarySizedSuchThat

set_option linter.missingDocs false

--------------------------------------------------------------------------
-- Some example `OptionT Gen α` generators
--------------------------------------------------------------------------

/-- `arbitrarySizedST` contains a handwritten generator for BSTs
    (modelled after the automatically derived generator produced by QuickChick).
    Note that:
    - We use the `OptionT` monad transformer to add the possibility of failure to the `Gen` monad
    - All the generators supplied to the `backtrack` combinator are thunked, to avoid unnecessary
      computation (since Lean is strict) -/
def genBST (lo : Nat) (hi : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) : OptionT Gen Tree :=
    match size with
    | .zero =>
      backtrack [
        (1, thunkGen $ fun _ => pure .Leaf),
        (1, thunkGen $ fun _ => OptionT.fail)
      ]
    | .succ size' =>
      backtrack [
        (1, thunkGen $ fun _ => pure .Leaf),
        (.succ size', thunkGen $ fun _ => do
          let x ← Arbitrary.arbitrary
          if (lo_0 < x && x < hi_0) then
            let l ← aux_arb initSize size' lo_0 x
            let r ← aux_arb initSize size' x hi_0
            pure (.Node x l r)
          else OptionT.fail)
      ]
  fun size => aux_arb size size lo hi

/- Instance of the `ArbitrarySizedSuchThat` typeclass for generators of BSTs -/
instance : ArbitrarySizedSuchThat Tree (fun t => bst lo hi t) where
  arbitrarySizedST := genBST lo hi

/-- A handwritten generator for balanced trees of height `n`
    (modelled after the automatically derived generator produced by QuickChick) -/
def genBalancedTree (n : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (initSize : Nat) (size : Nat) (n_0 : Nat) : OptionT Gen Tree :=
      match size with
      | .zero =>
        backtrack [
          (1, thunkGen $ fun _ =>
              match n_0 with
              | .zero => pure .Leaf
              | .succ _ => OptionT.fail),
          (1, thunkGen $ fun _ =>
              match n_0 with
              | 1 => pure .Leaf
              | _ => OptionT.fail),
          (1, thunkGen $ fun _ => OptionT.fail)
        ]
      | .succ size' =>
        backtrack [
          (1, thunkGen $ fun _ =>
              match n_0 with
              | .zero => pure .Leaf
              | _ => OptionT.fail),
          (1, thunkGen $ fun _ =>
              match n_0 with
              | 1 => pure .Leaf
              | _ => OptionT.fail),
          (.succ size', thunkGen $ fun _ =>
            match n_0 with
            | .zero => OptionT.fail
            | .succ n => do
              let l ← aux_arb initSize size' n
              let r ← aux_arb initSize size' n
              let x ← Arbitrary.arbitrary
              pure (.Node x l r))
        ]
  fun size => aux_arb size size n

/- Instance of the `ArbitrarySizedSuchThat` typeclass for generators of balanced trees
   of height `n` -/
-- instance : ArbitrarySizedSuchThat Tree (fun t => balanced n t) where
--   arbitrarySizedST := genBalancedTree n


/-
Example usage:

To sample from the derived generator, we apply the `arbitrarySizedST` function
(from the `ArbitrarySizedSuchThat` typeclass) onto the proposition that constrains
the generated values (e.g. `fun t => balanced 5 t` for balanced trees of height 5).
We then invoke `runSizedGen` to display the generated value in the `IO` monad.

For example:
```
def tempSize := 10
#eval runSizedGen (arbitrarySizedST (fun t => balanced 5 t)) tempSize
```
-/

/-- Hand-written `DecOpt` instance for the inductive relation `between lo x hi`, which means `lo < x < hi` -/
instance : DecOpt (between lo_1 x_1 hi_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (lo_1 : Nat) (x_1 : Nat) (hi_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match hi_1 with
            | Nat.succ (Nat.succ m) =>
              match x_1 with
              | Nat.succ u_3 =>
                DecOpt.andOpt (DecOpt.decOpt (BEq.beq u_3 lo_1) initSize) (DecOpt.decOpt (LE.le lo_1 m) initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match hi_1 with
            | Nat.succ (Nat.succ m) =>
              match x_1 with
              | Nat.succ u_3 =>
                match DecOpt.decOpt (BEq.beq u_3 lo_1) initSize with
                | Option.some Bool.true =>
                  match DecOpt.decOpt (LE.le lo_1 m) initSize with
                  | Option.some Bool.true => Option.some Bool.true
                  | _ => Option.some Bool.false
                | _ => Option.some Bool.false
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match hi_1 with
            | Nat.succ o =>
              match x_1 with
              | Nat.succ m =>
                match aux_dec initSize size' lo_1 m o with
                | Option.some Bool.true => Option.some Bool.true
                | _ => Option.some Bool.false
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size lo_1 x_1 hi_1


/-- Handwritten `DecOpt` instance for the proposition `bst lo hi t` -/
instance : DecOpt (bst lo hi t) where
  decOpt :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) (t_0 : Tree) : Option Bool :=
      match size with
      | .zero =>
        DecOpt.checkerBacktrack [
          fun _ =>
            match t_0 with
            | .Leaf => some true
            | .Node _ _ _ => some false,
          fun _ => none
        ]
      | .succ size' =>
        DecOpt.checkerBacktrack [
          fun _ =>
            match t_0 with
            | .Leaf => some true
            | .Node _ _ _ => some false,
          fun _ =>
            match t_0 with
            | .Leaf => some false
            | .Node x l r =>
              DecOpt.andOptList [
                DecOpt.decOpt (lo_0 < x && x < hi_0) initSize,
                aux_arb initSize size' lo_0 x l,
                aux_arb initSize size' x hi_0 r
              ]
        ]
    fun size => aux_arb size size lo hi t

def checkBST (lo : Nat) (hi : Nat) (t : Tree) : DecOpt (bst lo hi t) :=
  ⟨ let rec aux_dec (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) (t_1 : Tree) : Option Bool :=
        match size with
        | Nat.zero =>
          DecOpt.checkerBacktrack
            [fun _ =>
              match t_1 with
              | Tree.Leaf => Option.some Bool.true
              | _ => Option.some Bool.false]
        | Nat.succ size' =>
          DecOpt.checkerBacktrack
            [fun _ =>
              match t_1 with
              | Tree.Leaf => Option.some Bool.true
              | _ => Option.some Bool.false,
              fun _ =>
              match t_1 with
              | Tree.Node x l r =>
                DecOpt.andOptList
                  [DecOpt.decOpt (between lo_1 x hi_1) initSize,
                    DecOpt.andOptList [aux_dec initSize size' lo_1 x l, aux_dec initSize size' x hi_1 r]]
              | _ => Option.some Bool.false]
      fun size => aux_dec size size lo hi t ⟩




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

def buggyInsert (x : Nat) (_ : Tree) : Tree :=
  .Node x (.Node x .Leaf .Leaf) .Leaf


def runTests (numTrials : Nat) : IO Unit := do
  let size := 10
  let mut numSucceeded := 0
  for _ in [:numTrials] do
    let x ← Gen.run (Subtype.val <$> Gen.chooseNatLt 1 10 (by decide)) size
    let maybeTree ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => bst 0 10 t) size) size
    match maybeTree with
    | some t =>
      let t' := buggyInsert x t
      let b := DecOpt.decOpt (bst 0 10 t') size
      match b with
      | some bool =>
        if bool then
          numSucceeded := numSucceeded + 1
        else
          IO.println s!"Property falsified!"
          IO.println s!"t = {repr t}"
          IO.println s!"x = {x}"
          IO.println s!"t' = {repr t'}"
          return
      | none => IO.println "unable to decide BST"
    | none => IO.println "unable to generate BST"
  IO.println s!"finished {numTrials} tests, {numSucceeded} passed"


-- #eval runTests 10000


/-- Handwritten `DecOpt` instance for the proposition `balanced n t` -/
instance : DecOpt (balanced n t) where
  decOpt :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_0 : Nat) (t_0 : Tree) : Option Bool :=
      match size with
      | .zero =>
        DecOpt.checkerBacktrack [
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 0 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 1 => some true
                      | _ => some false
            | _ => some false),
          (fun _ => none)
        ]
      | .succ size' =>
        DecOpt.checkerBacktrack [
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 0 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 1 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => some false
            | .Node _ l r =>
              match n_0 with
              | .succ n =>
                DecOpt.andOptList [
                  aux_arb initSize size' n l,
                  aux_arb initSize size' n r
                ]
              | _ => some false)
        ]
    fun size => aux_arb size size n t
