import Plausible.Chamelean.Examples.Cedar
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer

open Plausible

/-- We override the default `Arbitrary` instance for `String`s with our custom generator -/
instance : Arbitrary String where
  arbitrary := GeneratorCombinators.elementsWithDefault
    "Aaron" ["Aaron", "John", "Mike", "Kesha", "Hicks", "A", "B", "C", "D"]

-- Derive `Arbitrary` instances for Cedar data/types/expressions/schemas
deriving instance Arbitrary for
  EntityName, EntityUID, Prim, Var, PatElem, UnaryOp, BinaryOp, CedarExpr,
  Request, BoolType, CedarType, EntitySchemaEntry, ActionSchemaEntry, Schema,
  RequestType, Environment, PathSet

/--
info: Try this checker: instance : DecOpt (RecordExpr ce_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ce_1 : CedarExpr) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.recExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.recExprCons fn e r => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.recExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.recExprCons fn e r => Option.some Bool.true
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ce_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (RecordExpr ce)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarExpr (fun ce_1 => RecordExpr ce_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen CedarExpr :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, return CedarExpr.recExprNil),
            (1, do
              let e ← Plausible.Arbitrary.arbitrary;
              do
                let fn ← Plausible.Arbitrary.arbitrary;
                do
                  let r ← Plausible.Arbitrary.arbitrary;
                  return CedarExpr.recExprCons fn e r)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return CedarExpr.recExprNil),
            (1, do
              let e ← Plausible.Arbitrary.arbitrary;
              do
                let fn ← Plausible.Arbitrary.arbitrary;
                do
                  let r ← Plausible.Arbitrary.arbitrary;
                  return CedarExpr.recExprCons fn e r),
            ]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => RecordExpr ce)


/--
info: Try this checker: instance : DecOpt (SetExpr ce_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ce_1 : CedarExpr) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.setExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.setExprCons e r => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.setExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.setExprCons e r => Option.some Bool.true
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ce_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (SetExpr ce)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarExpr (fun ce_1 => SetExpr ce_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen CedarExpr :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, return CedarExpr.setExprNil),
            (1, do
              let e ← Plausible.Arbitrary.arbitrary;
              do
                let r ← Plausible.Arbitrary.arbitrary;
                return CedarExpr.setExprCons e r)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return CedarExpr.setExprNil),
            (1, do
              let e ← Plausible.Arbitrary.arbitrary;
              do
                let r ← Plausible.Arbitrary.arbitrary;
                return CedarExpr.setExprCons e r),
            ]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => SetExpr ce)

/--
info: Try this checker: instance : DecOpt (SetEntityValues ce_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ce_1 : CedarExpr) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.setExprNil => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.setExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.setExprCons (CedarExpr.lit (Prim.entityUID uid)) r => aux_dec initSize size' r
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ce_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (SetEntityValues ce)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarExpr (fun ce_1 => SetEntityValues ce_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen CedarExpr :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return CedarExpr.setExprNil)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return CedarExpr.setExprNil),
            (Nat.succ size', do
              let r ← aux_arb initSize size';
              do
                let uid ← Plausible.Arbitrary.arbitrary;
                return CedarExpr.setExprCons (CedarExpr.lit (Prim.entityUID uid)) r)]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => SetEntityValues ce)

/--
info: Try this checker: instance : DecOpt (DefinedName ns_1 n_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (n_1 : EntityName) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ns_1 with
            | List.cons A L => DecOpt.decOpt (Eq A n_1) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ns_1 with
            | List.cons A L => DecOpt.decOpt (Eq A n_1) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match ns_1 with
            | List.cons B L =>
              DecOpt.andOptList [DecOpt.decOpt (Eq (bne n_1 B) (Bool.true)) initSize, aux_dec initSize size' L n_1]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 n_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (DefinedName ns n)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat EntityName (fun n_1 => DefinedName ns_1 n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) : OptionT Plausible.Gen EntityName :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match ns_1 with
              | List.cons A L => do
                let n_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n_1 => Eq A n_1) initSize;
                return n_1
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match ns_1 with
              | List.cons A L => do
                let n_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n_1 => Eq A n_1) initSize;
                return n_1
              | _ => OptionT.fail),
            (Nat.succ size',
              match ns_1 with
              | List.cons B L => do
                let n_1 ← aux_arb initSize size' L;
                match DecOpt.decOpt (Eq (bne n_1 B) (Bool.true)) initSize with
                  | Option.some Bool.true => return n_1
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : EntityName) => DefinedName ns n)

/--
info: Try this checker: instance : DecOpt (DefinedNames ns_1 ns0_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (ns0_1 : List EntityName) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ns0_1 with
            | List.nil => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ns0_1 with
            | List.nil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ns0_1 with
            | List.cons n ns0 =>
              DecOpt.andOptList [DecOpt.decOpt (DefinedName ns_1 n) initSize, aux_dec initSize size' ns_1 ns0]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 ns0_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (DefinedNames ns ns0)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List EntityName) (fun ns0_1 => DefinedNames ns_1 ns0_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) : OptionT Plausible.Gen (List EntityName) :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return List.nil)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return List.nil),
            (Nat.succ size', do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => DefinedName ns_1 n) initSize;
              do
                let ns0 ← aux_arb initSize size' ns_1;
                return List.cons n ns0)]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ns0 : List EntityName) => DefinedNames ns ns0)
