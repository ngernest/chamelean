import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
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

-- #derive_generator (fun (x : Nat) => Between lo x hi)
-- #derive_checker (Between lo hi t)

/-- `BST lo hi t` describes whether a tree `t` is a BST that
    contains values strictly within `lo` and `hi` -/
inductive BST : Nat → Nat → Tree → Prop where
  | BSTLeaf: ∀ lo hi, BST lo hi .Leaf
  | BSTNode: ∀ lo hi x l r,
    Between lo x hi →
    BST lo x l →
    BST x hi r →
    BST lo hi (.Node x l r)

-- #derive_generator (fun (t : Tree) => BST lo hi t)
-- #derive_checker (BST lo hi t)

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

/- Test harness for testing the property
    `∀ (x : Nat) (t : Tree), BST 0 10 t → BST 0 10 (insert x t)`
    for `numTrials` iterations.

    (Details omitted) -/
-- def runTests (numTrials : Nat) : IO Unit :=
--   do
--     let size := 10
--     let useBuggyVersion : Bool := true
--     let mut numSucceeded := 0
--     for i in [:numTrials] do
--       let x ← Gen.run (Subtype.val <$> Gen.chooseNatLt 1 10 (by decide)) size
--       let maybeTree ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => BST 0 10 t) size) size
--       match maybeTree with
--       | some t =>
--         let insertFn := if useBuggyVersion then buggyInsert else insert
--         let t' := insertFn x t
--         let b := DecOpt.decOpt (BST 0 10 t') size
--         match b with
--         | some bool =>
--           if bool then
--             numSucceeded := numSucceeded + 1
--           else
--             IO.println s!"Property falsified!\nt = {repr t}\nx = {x}\nt' = {repr t'}"
--             return
--         | none => IO.println s!"unable to decide BST validity for {repr t'}"
--       | none => IO.println "unable to generate valid BST"
--     IO.println s!"Chamelean: finished {numTrials} tests, {numSucceeded} passed"

-- Uncomment this to run the aforementioned test harness
-- #eval runTests (numTrials := 10000)


inductive Permutation : List Nat → List Nat → Prop where
  | PermNil : Permutation [] []
  | PermSkip : ∀ (x : Nat) (l l' : List Nat),
               Permutation l l' →
               Permutation (x :: l) (x :: l')
  | PermSwap : ∀  (x y : Nat) (l : List Nat),
              Permutation (y :: x :: l) (x :: y :: l)
  | PermTrans : ∀  (l l' l'' : List Nat),
                Permutation l l' →
                Permutation l' l'' →
                Permutation l l''

/--
info: Try this generator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => Permutation l_1 l'_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (l'_1 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match l'_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons x (List.cons y l) => return List.cons y (List.cons x l)
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match l'_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons x (List.cons y l) => return List.cons y (List.cons x l)
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons x l' => do
              let l ← aux_enum initSize size' l';
              return List.cons x l
            | _ => OptionT.fail,
            do
            let l' ← aux_enum initSize size' l'_1;
            do
              let l_1 ← aux_enum initSize size' l';
              return l_1]
    fun size => aux_enum size size l'_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l : List Nat) => Permutation l l')

/--
info: Try this generator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => Permutation l'_1 l_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (l'_1 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match l'_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons y (List.cons x l) => return List.cons x (List.cons y l)
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match l'_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons y (List.cons x l) => return List.cons x (List.cons y l)
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons x l => do
              let l' ← aux_enum initSize size' l;
              return List.cons x l'
            | _ => OptionT.fail,
            do
            let l' ← aux_enum initSize size' l'_1;
            do
              let l_1 ← aux_enum initSize size' l';
              return l_1]
    fun size => aux_enum size size l'_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l : List Nat) => Permutation l' l)


/--
info: Try this checker: instance : DecOpt (Permutation l_1 l'_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (l_1 : List Nat) (l'_1 : List Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l'_1 with
            | List.nil =>
              match l_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match l'_1 with
            | List.cons u_2 (List.cons u_3 u_4) =>
              match l_1 with
              | List.cons y (List.cons x l) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_2 x) initSize,
                    DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_4 l) initSize, DecOpt.decOpt (BEq.beq u_3 y) initSize]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l'_1 with
            | List.nil =>
              match l_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match l'_1 with
            | List.cons u_2 (List.cons u_3 u_4) =>
              match l_1 with
              | List.cons y (List.cons x l) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_2 x) initSize,
                    DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_4 l) initSize, DecOpt.decOpt (BEq.beq u_3 y) initSize]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match l'_1 with
            | List.cons u_2 l' =>
              match l_1 with
              | List.cons x l => DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_2 x) initSize, aux_dec initSize size' l l']
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun l' => Permutation l_1 l') initSize)
              (fun l' => aux_dec initSize size' l' l'_1) initSize]
    fun size => aux_dec size size l_1 l'_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (Permutation l l')

def l := [1, 2, 3]
def l' := [2, 1, 5]

#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun l' => Permutation l l')) 1
