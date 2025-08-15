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
info: Try this checker: instance : DecOpt (RecordExpr ct_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ct_1 : CedarExpr) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ct_1 with
            | CedarExpr.recExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarExpr.recExprCons fn e r => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ct_1 with
            | CedarExpr.recExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarExpr.recExprCons fn e r => Option.some Bool.true
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ct_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (RecordExpr ct)
