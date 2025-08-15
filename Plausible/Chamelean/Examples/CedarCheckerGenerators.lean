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
