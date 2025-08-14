------------------------------------
-- Part One: Cedar expression syntax
-------------------------------------

/-- The name of an entity -/
inductive EntityName where
| MkName : String → List String → EntityName
deriving Repr, DecidableEq

/-- Entity UIDs -/
inductive EntityUID where
| MkEntityUID : EntityName → String → EntityUID
deriving Repr, DecidableEq

/-- Primitive values -/
inductive Prim where
| boolean (b : Bool)
| int (i : Int)
| stringLit (s : String)
| entityUID (e : EntityUID)
deriving Repr, DecidableEq

/-- Variables -/
inductive Var where
| principal
| action
| resource
| context
deriving Repr, DecidableEq

/-- Pattern elements -/
inductive PatElem where
| star
| justLit (s : String)
deriving Repr, DecidableEq

/-- Unary operations -/
inductive UnaryOp where
| not
| neg
| like (p : List PatElem)
| is (ety : EntityName)
deriving Repr, DecidableEq

/-- Binary operations -/
inductive BinaryOp where
| equals
| mem
| less
| lessEq
| add
| sub
| mul
| contains
| containsAll
| containsAny
deriving Repr, DecidableEq

/-- Cedar expressions
    - Note: we "inlines" list constructors for sets and records to avoid issue with mutual recursion in a list/generic type -/
inductive Expr where
| lit (p : Prim)
| var (v : Var)
| ite (cond : Expr) (thenExpr : Expr) (elseExpr : Expr)
| andExpr (a : Expr) (b : Expr)
| orExpr (a : Expr) (b : Expr)
| unaryApp (op : UnaryOp) (expr : Expr)
| binaryApp (op : BinaryOp) (a : Expr) (b : Expr)
| getAttr (expr : Expr) (attr : String)
| hasAttr (expr : Expr) (attr : String)
| setExprNil
| setExprCons (e : Expr) (ls : Expr)
| recExprNil
| recExprCons (s : String) (e : Expr) (attrs : Expr)
deriving DecidableEq

/-- Type of entity data.
    Precondition: the `Expr` argument should always be a record of values -/
inductive EntityData where
| MkEntityData : Expr → List EntityUID → EntityData
deriving DecidableEq

/-- given `MkReq P A R C`, assumes that `RecordExpr C` and `Value C` hold --/
inductive Request where
| MkReq : EntityUID → EntityUID → EntityUID → Expr → Request
deriving DecidableEq

-------------------------------------------------
-- Part Two: Pretty Printing Cedar Expressions
-------------------------------------------------

/-- Converts the arguments to an `EntityName` to a String -/
def stringOfEntityName (ps : List String) (t : String) : String :=
  match ps with
  | [] => t
  | p::ps' => p ++ "::" ++ stringOfEntityName ps' t

instance : ToString EntityName where
  toString := fun b =>
    match b with
    | .MkName t p => stringOfEntityName p t

/-- Converts an Entity UID to a string -/
def stringOfEntityUID (ps : List String) (t : String) (id : String) : String :=
  stringOfEntityName ps t ++ "::\"" ++ id ++ "\""

instance : ToString EntityUID where
  toString := fun b =>
    match b with
    | EntityUID.MkEntityUID (.MkName t p) id => stringOfEntityUID p t id

/-- Converts a primitive to a string -/
def stringOfPrim (p : Prim) : String :=
  match p with
  | Prim.boolean b => toString b
  | Prim.int i => toString i
  | Prim.stringLit s => toString s
  | Prim.entityUID e => toString e

instance : ToString Prim where
  toString := stringOfPrim

instance : ToString Var where
  toString := fun v => match v with
    | Var.principal => "principal"
    | Var.action => "action"
    | Var.resource => "resource"
    | Var.context => "context"

/-- Converts a `PatElem` to a string -/
def stringOfPatElem (p : PatElem) : String :=
  match p with
  | PatElem.star => "*"
  | PatElem.justLit s => s

/-- Converts a List of `PatElem`s to `String`s -/
def stringOfPats (p : List PatElem) : String :=
  match p with
  | [] => ""
  | p0::ps => stringOfPatElem p0 ++ stringOfPats ps

/-- Converts an `Expr` to a string -/
def stringOfExpr (e : Expr) : String :=
  match e with
  | Expr.lit p => toString p
  | Expr.var v => toString v
  | Expr.ite cond thenExpr elseExpr =>
      "if (" ++ stringOfExpr cond ++ ") then (" ++ stringOfExpr thenExpr ++ ") else (" ++ stringOfExpr elseExpr ++ ")"
  | Expr.andExpr a b => "(" ++ stringOfExpr a ++ ") && (" ++ stringOfExpr b ++ ")"
  | Expr.orExpr a b => "(" ++ stringOfExpr a ++ ") || (" ++ stringOfExpr b ++ ")"
  | Expr.unaryApp op expr =>
    match op with
    | UnaryOp.not => "not (" ++ stringOfExpr expr ++ ")"
    | UnaryOp.neg => "- (" ++ stringOfExpr expr ++ ")"
    | UnaryOp.like ps => "(" ++ stringOfExpr expr ++ ") like \"" ++ stringOfPats ps ++ "\""
    | UnaryOp.is e => "is (" ++ toString e ++ ")"
  | Expr.binaryApp op a b =>
    let sa := "(" ++ stringOfExpr a ++ ")"
    let sb := "(" ++ stringOfExpr b ++ ")"
    match op with
    | BinaryOp.equals => sa ++ "==" ++ sb
    | BinaryOp.mem => sa ++ "in" ++ sb
    | BinaryOp.less => sa ++ "<" ++ sb
    | BinaryOp.lessEq => sa ++ "<=" ++ sb
    | BinaryOp.add => sa ++ "+" ++ sb
    | BinaryOp.sub => sa ++ "-" ++ sb
    | BinaryOp.mul => sa ++ "*" ++ sb
    | BinaryOp.contains => sa ++ ".contains" ++ sb
    | BinaryOp.containsAll => sa ++ ".containsAll" ++ sb
    | BinaryOp.containsAny => sa ++ ".containsAny" ++ sb
  | Expr.getAttr expr attr => "(" ++ stringOfExpr expr ++ ")." ++ attr
  | Expr.hasAttr expr attr => "(" ++ stringOfExpr expr ++ ") has " ++ attr
  | Expr.setExprNil => "nil"
  | Expr.setExprCons e ls => "(" ++ stringOfExpr e ++ ")::" ++ stringOfExpr ls
  | Expr.recExprNil => "{}"
  | Expr.recExprCons s e attrs => "{ " ++ s ++ ": " ++ stringOfExpr e ++ " }" ++ stringOfExpr attrs

instance : ToString Expr where
  toString := stringOfExpr

instance : ToString Request where
  toString := fun r => match r with
    | Request.MkReq p a res c =>
        "MkReq " ++ toString p ++ " " ++ toString a ++ " " ++ toString res ++ " " ++ toString c

/-- Computes the `depth` of an expression, useful during generation -/
def depthExpr (e : Expr) : Nat :=
  match e with
  | Expr.lit _p => 1
  | Expr.var _v => 1
  | Expr.ite cond thenExpr elseExpr =>
    1 + max (max (depthExpr cond) (depthExpr thenExpr)) (depthExpr elseExpr)
  | Expr.andExpr a b => 1 + max (depthExpr a) (depthExpr b)
  | Expr.orExpr a b => 1 + max (depthExpr a) (depthExpr b)
  | Expr.unaryApp _op expr => 1 + depthExpr expr
  | Expr.binaryApp _op a b => 1 + max (depthExpr a) (depthExpr b)
  | Expr.getAttr expr _attr => 1 + depthExpr expr
  | Expr.hasAttr expr _attr => 1 + depthExpr expr
  | Expr.setExprNil => 1
  | Expr.setExprCons e ls => 1 + max (depthExpr e) (depthExpr ls)
  | Expr.recExprNil => 1
  | Expr.recExprCons _s e attrs => 1 + max (depthExpr e) (depthExpr attrs)

/-- Computes the `size` of an expression, useful during generation -/
def sizeExpr (e : Expr) : Nat :=
  match e with
  | Expr.lit _ => 1
  | Expr.var _ => 1
  | Expr.ite cond thenExpr elseExpr =>
    1 + sizeExpr cond + sizeExpr thenExpr + sizeExpr elseExpr
  | Expr.andExpr a b => 1 + sizeExpr a + sizeExpr b
  | Expr.orExpr a b => 1 + sizeExpr a + sizeExpr b
  | Expr.unaryApp _ expr => 1 + sizeExpr expr
  | Expr.binaryApp _ a b => 1 + sizeExpr a + sizeExpr b
  | Expr.getAttr expr _ => 1 + sizeExpr expr
  | Expr.hasAttr expr _ => 1 + sizeExpr expr
  | Expr.setExprNil => 1
  | Expr.setExprCons e ls => 1 + sizeExpr e + sizeExpr ls
  | Expr.recExprNil => 1
  | Expr.recExprCons _ e attrs => 1 + sizeExpr e + sizeExpr attrs


---------------------------------------
-- Part Three: Cedar expression typing
---------------------------------------
-- Some basic predicates useful for typing

/-- predicate: When an expression is a record -/
inductive RecordExpr : Expr → Prop where
| RENil : RecordExpr Expr.recExprNil
| RECons : ∀ fn e r, RecordExpr (Expr.recExprCons fn e r)

/-- predicate: When an expression is a set -/
inductive SetExpr : Expr → Prop where
| SENil : SetExpr Expr.setExprNil
| SECons : ∀ e r, SetExpr (Expr.setExprCons e r)

/-- predicate: When an expression is a value -/
inductive Value : Expr → Prop where
| VLit : ∀ p, Value (Expr.lit p)
| VSNil : Value Expr.setExprNil
| VSCons : ∀ e ls, Value e → Value ls → Value (Expr.setExprCons e ls)
| VRNil : Value Expr.recExprNil
| VRCons : ∀ s e rs, Value e → Value rs → Value (Expr.recExprCons s e rs)

/-- predicate: When an expression is a set of entity values -/
inductive SetEntityValues : Expr → Prop where
| SEVNil : SetEntityValues Expr.setExprNil
| SEVCons : ∀ uid r,
    SetEntityValues r →
    SetEntityValues (Expr.setExprCons (Expr.lit (Prim.entityUID uid)) r)

-- Types

inductive BoolType where
| anyBool
| tt
| ff
deriving Repr, DecidableEq

inductive CedarType where
| boolType (bty : BoolType)
| intType
| stringType
| entityType (ety : EntityName)
| setType (ty : CedarType)
| recordTypeNil
| recordTypeCons (s : String) (opt : Bool) (ty : CedarType) (rest : CedarType)
deriving Repr, DecidableEq

/-- Determines whether a `CedarType` is a `RecordType` -/
inductive RecordType : CedarType → Prop where
| RTNil : RecordType CedarType.recordTypeNil
| RTCons : ∀ fn o T1 T2, RecordType (CedarType.recordTypeCons fn o T1 T2)
