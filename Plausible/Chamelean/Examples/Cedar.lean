-- Import linter from batteries to suppress "missing documentation" linter warnings
import Batteries.Tactic.Lint

------------------------------------
-- Part One: Cedar expression syntax
-------------------------------------

/-- The name of an entity -/
inductive EntityName where
| MkName : String → List String → EntityName
deriving Repr, BEq

/-- Entity UIDs -/
inductive EntityUID where
| MkEntityUID : EntityName → String → EntityUID
deriving Repr, BEq

/-- Primitive values -/
inductive Prim where
| boolean (b : Bool)
| int (i : Int)
| stringLit (s : String)
| entityUID (e : EntityUID)
deriving Repr, BEq

/-- Variables -/
inductive Var where
| principal
| action
| resource
| context
deriving Repr, BEq

/-- Pattern elements -/
inductive PatElem where
| star
| justLit (s : String)
deriving Repr, BEq

/-- Unary operations -/
inductive UnaryOp where
| not
| neg
| like (p : List PatElem)
| is (ety : EntityName)
deriving Repr, BEq

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
deriving Repr, BEq

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
deriving BEq

/-- Type of entity data.
    Precondition: the `Expr` argument should always be a record of values -/
inductive EntityData where
| MkEntityData : Expr → List EntityUID → EntityData
deriving BEq

/-- given `MkReq P A R C`, assumes that `RecordExpr C` and `Value C` hold --/
inductive Request where
| MkReq : EntityUID → EntityUID → EntityUID → Expr → Request
deriving BEq

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

instance : Repr Expr where
  reprPrec e _ := toString e

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

------------------------------------------------------
-- Types
------------------------------------------------------

/-- Boolean types -/
inductive BoolType where
| anyBool
| tt
| ff
deriving Repr, BEq

/-- Types in Cedar -/
inductive CedarType where
| boolType (bty : BoolType)
| intType
| stringType
| entityType (ety : EntityName)
| setType (ty : CedarType)
| recordTypeNil
| recordTypeCons (s : String) (opt : Bool) (ty : CedarType) (rest : CedarType)
deriving BEq

/-- Determines whether a `CedarType` is a `RecordType` -/
inductive RecordType : CedarType → Prop where
| RTNil : RecordType CedarType.recordTypeNil
| RTCons : ∀ fn o T1 T2, RecordType (CedarType.recordTypeCons fn o T1 T2)

@[nolint docBlame]
inductive DefinedName : List EntityName → EntityName → Prop where
| DNFound : ∀ L A B,
    A = B →
    DefinedName (A::L) B
| DNRest : ∀ L A B,
    ¬(A = B) →
    DefinedName L A →
    DefinedName (B::L) A

@[nolint docBlame]
inductive DefinedNames : List EntityName → List EntityName → Prop where
| DNSNil : ∀ ns, DefinedNames ns []
| DNSCons : ∀ n ns0 ns,
    DefinedName ns n →
    DefinedNames ns ns0 →
    DefinedNames ns (n::ns0)

/-- Inductive relation specifying well-formedness conditions for Cedar types -/
inductive WfCedarType : List EntityName → CedarType → Prop where
| WfBoolType : ∀ ns B, WfCedarType ns (CedarType.boolType B)
| WfIntType : ∀ ns, WfCedarType ns CedarType.intType
| WfStringType : ∀ ns, WfCedarType ns CedarType.stringType
| WfEntityType : ∀ ns n,
    DefinedName ns n →
    WfCedarType ns (CedarType.entityType n)
| WfSetType : ∀ T ns,
    WfCedarType ns T →
    WfCedarType ns (CedarType.setType T)
| WfRecordTypeNil : ∀ ns, WfCedarType ns CedarType.recordTypeNil
| WfRecordTypeConsNil : ∀ fn o T1 ns,
    WfCedarType ns T1 →
    WfCedarType ns (CedarType.recordTypeCons fn o T1 CedarType.recordTypeNil)
| WfRecordTypeConsCons : ∀ fn o T1 ns fn1 o1 T2 r,
    WfCedarType ns T1 →
    WfCedarType ns (CedarType.recordTypeCons fn1 o1 T2 r) →
    WfCedarType ns (CedarType.recordTypeCons fn o T1 (CedarType.recordTypeCons fn1 o1 T2 r))

/-- Well-formed record types are types that are both well-formed and record types -/
def WfRecordType (ns : List EntityName) (ct : CedarType) : Prop :=
  WfCedarType ns ct ∧ RecordType ct

------------------------------------------------------
-- Schemas
------------------------------------------------------

@[nolint docBlame]
inductive EntitySchemaEntry where
| MkEntitySchemaEntry (ancestors : List EntityName) (attrs : List (String × Bool × CedarType))
deriving BEq

@[nolint docBlame]
inductive WfAttrs : List EntityName → List (String × Bool × CedarType) → Prop where
| WfAttrsNil : ∀ ns, WfAttrs ns []
| WfAttrsCons : ∀ ns T s b attrs,
    WfCedarType ns T →
    WfAttrs ns attrs →
    WfAttrs ns ((s, b, T)::attrs)

@[nolint docBlame]
inductive WfET : List EntityName → EntitySchemaEntry → Prop where
| WfETSingle : ∀ ns ancs attrs,
    DefinedNames ns ancs →
    WfAttrs ns attrs →
    WfET ns (EntitySchemaEntry.MkEntitySchemaEntry ancs attrs)

@[nolint docBlame]
inductive WfETS : List EntityName → List EntityName → List (EntityName × EntitySchemaEntry) → Prop where
| WfETSSingle : ∀ ns n et,
    DefinedName ns n →
    WfET ns et →
    WfETS ns [n] [(n, et)]
| WfETSCons : ∀ n ns ns0 et ets,
    DefinedName ns n →
    WfET ns et →
    WfETS ns ns0 ets →
    WfETS ns (n::ns0) ((n, et)::ets)

@[nolint docBlame]
inductive ActionSchemaEntry where
| MkActionSchemaEntry (prin : List EntityName) (res : List EntityName) (contextType : List (String × Bool × CedarType))
deriving BEq

/-- LATER: Allow more than one principal and resource -/
inductive WfACT : List EntityName → (EntityUID × ActionSchemaEntry) → Prop where
| WfACTSingle : ∀ n p r ns s attrs,
    DefinedName ns n →
    DefinedName ns p →
    DefinedName ns r →
    WfAttrs ns attrs →
    WfACT ns ((EntityUID.MkEntityUID n s), (ActionSchemaEntry.MkActionSchemaEntry [p] [r] attrs))

@[nolint docBlame]
inductive WfACTS : List EntityName → List (EntityUID × ActionSchemaEntry) → Prop where
| WfACTSSingle : ∀ ns act,
    WfACT ns act →
    WfACTS ns [act]
| WfACTSCons : ∀ ns act acts,
    WfACT ns act →
    WfACTS ns acts →
    WfACTS ns (act::acts)

@[nolint docBlame]
inductive Schema where
| MkSchema (ets : List (EntityName × EntitySchemaEntry)) (acts : List (EntityUID × ActionSchemaEntry))
deriving BEq

@[nolint docBlame]
inductive WfSchema : List EntityName → Schema → Prop where
| WfS : ∀ ns ets acts,
    WfETS ns ns ets →
    WfACTS ns acts →
    WfSchema ns (Schema.MkSchema ets acts)

@[nolint docBlame]
inductive DefinedEntity : List (EntityName × EntitySchemaEntry) → EntityName → Prop where
| DENow : ∀ n E R, DefinedEntity ((n, E)::R) n
| DELater : ∀ n n1 E R,
     ¬(n = n1) →
    DefinedEntity R n →
    DefinedEntity ((n1, E)::R) n

@[nolint docBlame]
inductive DefinedEntities : List (EntityName × EntitySchemaEntry) → List EntityName → Prop where
| DESNil : DefinedEntities [] []
| DESCons : ∀ n ns et ets,
    DefinedEntities ets ns →
    DefinedEntities ((n, et)::ets) (n::ns)

/-- NB: Ideally the string*bool parameter would be two distinct parameters.
    It's written this way due to current QuickChick/Chamelean limitations on generation. -/
inductive LookupEntityAttr : List (String × Bool × CedarType) → (String × Bool) → CedarType → Prop where
| LUNow : ∀ F B FS TF,
    LookupEntityAttr ((F, B, TF)::FS) (F, B) TF
| LULater : ∀ F1 B1 F2 FS TF B,
    ¬(F1 = F2) →
    LookupEntityAttr FS (F1, B1) TF →
    LookupEntityAttr ((F2, B, TF)::FS) (F1, B1) TF

@[nolint docBlame]
inductive GetEntityAttr : List (EntityName × EntitySchemaEntry) → (EntityName × String × Bool) → CedarType → Prop where
| GENow : ∀ n fn b A E R T,
    LookupEntityAttr E (fn, b) T →
    GetEntityAttr ((n, (EntitySchemaEntry.MkEntitySchemaEntry A E))::R) (n, fn, b) T
| GELater : ∀ n n1 fn b E R T,
    ¬(n = n1) →
    GetEntityAttr R (n, fn, b) T →
    GetEntityAttr ((n1, E)::R) (n, fn, b) T

------------------------------------------------------
-- Environments
------------------------------------------------------

@[nolint docBlame]
inductive RequestType : Type where
| MkRequest (prin : EntityName) (act : EntityUID) (res : EntityName) (ctxt : List (String × Bool × CedarType))
deriving BEq

/-- Converts a context description in RequestType to a Cedar record type -/
inductive ReqContextToCedarType : List (String × Bool × CedarType) → CedarType → Prop where
| RNil : ReqContextToCedarType [] CedarType.recordTypeNil
| RCons : ∀ i B T R TR,
    ReqContextToCedarType R TR →
    ReqContextToCedarType ((i, B, T)::R) (CedarType.recordTypeCons i B T TR)

@[nolint docBlame]
inductive ActionToRequestTypes : EntityUID → EntityName → List EntityName → List (String × Bool × CedarType) → List RequestType → List RequestType → Prop where
| ATRTSingle : ∀ uid p r c acc,
    ActionToRequestTypes uid p [r] c acc ((RequestType.MkRequest p uid r c)::acc)
| ATRTCons : ∀ uid p r rs c reqs acc,
    ActionToRequestTypes uid p rs c acc reqs →
    ActionToRequestTypes uid p (r::rs) c acc ((RequestType.MkRequest p uid r c)::reqs)

@[nolint docBlame]
inductive ActionSchemaEntryToRequestTypes : EntityUID → ActionSchemaEntry → List RequestType → List RequestType → Prop where
| ASTRTSingle : ∀ uid p rs c reqs acc,
    ActionToRequestTypes uid p rs c acc reqs →
    ActionSchemaEntryToRequestTypes uid (ActionSchemaEntry.MkActionSchemaEntry [p] rs c) acc reqs
| ASTRTCons : ∀ uid p ps rs c acc reqs reqs',
    ActionToRequestTypes uid p rs c acc reqs' →
    ActionSchemaEntryToRequestTypes uid (ActionSchemaEntry.MkActionSchemaEntry ps rs c) reqs' reqs →
    ActionSchemaEntryToRequestTypes uid (ActionSchemaEntry.MkActionSchemaEntry (p::ps) rs c) acc reqs

@[nolint docBlame]
inductive ActionSchemaToRequestTypes : List (EntityUID × ActionSchemaEntry) → List RequestType → List RequestType → Prop where
| ASTESingle : ∀ uid a acc reqs,
    ActionSchemaEntryToRequestTypes uid a acc reqs →
    ActionSchemaToRequestTypes [(uid, a)] acc reqs
| ASTECons : ∀ uid a ass acc reqs' reqs,
    ActionSchemaEntryToRequestTypes uid a acc reqs' →
    ActionSchemaToRequestTypes ass reqs' reqs →
    ActionSchemaToRequestTypes ((uid, a)::ass) acc reqs

@[nolint docBlame]
inductive Environment : Type where
| MkEnvironment (schema : Schema) (reqType : RequestType)
deriving BEq

@[nolint docBlame]
inductive SchemaToEnvironments : Schema → List RequestType → List Environment → Prop where
| MkEnvsSingle : ∀ r s,
    SchemaToEnvironments s [r] [(Environment.MkEnvironment s r)]
| MkEnvsCons : ∀ r rs s envs,
    SchemaToEnvironments s rs envs →
    SchemaToEnvironments s (r::rs) ((Environment.MkEnvironment s r)::envs)

------------------------------------------------------
-- Subtyping
------------------------------------------------------

/-- Note: Cedar has no width subtyping, just depth -/
inductive SubType : CedarType → CedarType → Prop where
| SBoolAny : ∀ B,
    SubType (CedarType.boolType B) (CedarType.boolType BoolType.anyBool)
| SSet : ∀ T1 T2,
    SubType T1 T2 →
    SubType (CedarType.setType T1) (CedarType.setType T2)
| SRecEmpty :
    SubType CedarType.recordTypeNil CedarType.recordTypeNil
| SRecAttr : ∀ A o T1 T2 R1 R2,
    SubType T1 T2 →
    RecordType R2 →
    SubType R1 R2 →
    RecordType R1 →
    SubType (CedarType.recordTypeCons A o T1 R1) (CedarType.recordTypeCons A o T2 R2)
| ST : ∀ T, SubType T T

------------------------------------------------------
-- Typing: Primitives and Variables
------------------------------------------------------

@[nolint docBlame]
inductive HasTypePrim : Environment → Prim → CedarType → Prop where
| TTrue : ∀ V, HasTypePrim V (Prim.boolean true) (CedarType.boolType BoolType.tt)
| TFalse : ∀ V, HasTypePrim V (Prim.boolean false) (CedarType.boolType BoolType.ff)
| TInt : ∀ V i, HasTypePrim V (Prim.int i) CedarType.intType
| TString : ∀ V s, HasTypePrim V (Prim.stringLit s) CedarType.stringType
| TEntity : ∀ ETS ACTS n i R,
    DefinedEntity ETS n →
    HasTypePrim
      (Environment.MkEnvironment (Schema.MkSchema ETS ACTS) R)
      (Prim.entityUID (EntityUID.MkEntityUID n i))
      (CedarType.entityType n)

@[nolint docBlame]
inductive HasTypeVar : Environment → Var → CedarType → Prop where
| TPrincipal : ∀ s P A R C,
    HasTypeVar (Environment.MkEnvironment s (RequestType.MkRequest P A R C)) Var.principal (CedarType.entityType P)
| TAction : ∀ s P n i R C,
    HasTypeVar (Environment.MkEnvironment s (RequestType.MkRequest P (EntityUID.MkEntityUID n i) R C)) Var.action (CedarType.entityType n)
| TResource : ∀ s P A R C,
    HasTypeVar (Environment.MkEnvironment s (RequestType.MkRequest P A R C)) Var.resource (CedarType.entityType R)
| TContext : ∀ s P A R C T,
    ReqContextToCedarType C T →
    HasTypeVar (Environment.MkEnvironment s (RequestType.MkRequest P A R C)) Var.context T

@[nolint docBlame]
inductive BindAttrType : List EntityName → (CedarType × String × Bool) → CedarType → Prop where
| BindNow : ∀ x t b r ns,
    WfRecordType ns r →
    BindAttrType ns ((CedarType.recordTypeCons x b t r), x, b) t
| BindLater : ∀ x y b i t1 t r ns,
    ¬(x = y) →
    WfRecordType ns r →
    BindAttrType ns (r, x, b) t1 →
    BindAttrType ns ((CedarType.recordTypeCons y i t r), x, b) t1

/-- A PathSet is a Cedar typing "capability" -- it is a set of accessible record-access expressions, or infinity (meaning all are accessible) -/
inductive PathSet : Type where
| allpaths
| somepaths (paths : List Expr)
deriving Repr, BEq

------------------------------------------------------
-- Typing: Defining "Capabilities" for record access
------------------------------------------------------

/-- Membership test of `x` in `ps` -/
def validPathExpr (x : Expr) (ps : PathSet) : Bool :=
  let rec aux (xs : List Expr) : Bool :=
    match xs with
    | [] => false
    | y::ys =>
        if x == y then true else aux ys
  match ps with
  | PathSet.allpaths => true
  | PathSet.somepaths xs => aux xs

/-- Intersects two pathsets -/
def interExprs (ps : PathSet) (ys : PathSet) : PathSet :=
  let rec aux (xs : List Expr) : List Expr :=
    match xs with
    | [] => []
    | x::xs' =>
        if validPathExpr x ys then x::(aux xs')
        else aux xs'
  match ps with
  | PathSet.allpaths => ys
  | PathSet.somepaths xs => PathSet.somepaths (aux xs)

/-- returns `l` with `x` removed -/
def subExprs (x : Expr) (l : List Expr) : List Expr :=
   match l with
   | [] => []
   | y::ys =>
      if x == y then ys
      else y::(subExprs x ys)

/-- union of `xs` and `ys` -/
def mergeExprs (xs : PathSet) (ys : PathSet) : PathSet :=
  let rec aux (xs : List Expr) (ys : List Expr) : List Expr :=
    match xs with
    | [] => ys
    | x::xs' => x::(aux xs' (subExprs x ys))
  match xs with
  | PathSet.allpaths => PathSet.allpaths
  | PathSet.somepaths xs0 =>
    match ys with
    | PathSet.allpaths => PathSet.allpaths
    | PathSet.somepaths ys0 => PathSet.somepaths (aux xs0 ys0)

-------------------------
-- Typing: Expressions
-------------------------

/-- `HasType a v (e,x) t` is equivalent to a,v |- e : ;xt in the paper. This is
  Written assuming we will derive a generator for (e,x) given a v and t (ideally e and x would be their own parameters) -/
inductive HasType : PathSet → Environment → (Expr × PathSet) → CedarType → Prop where
| TLitFalse : ∀ a V P,
    HasTypePrim V P (CedarType.boolType BoolType.ff) →
    HasType a V ((Expr.lit P), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TLitOther : ∀ a V P T,
    ¬(T = (CedarType.boolType BoolType.ff)) →
    HasTypePrim V P T →
    HasType a V ((Expr.lit P), PathSet.somepaths []) T
| TVar : ∀ a V X T,
    HasTypeVar V X T →
    HasType a V ((Expr.var X), PathSet.somepaths []) T
| TCondTrue : ∀ a V E1 E2 E3 x1 x2 T2,
    HasType a V (E1, x1) (CedarType.boolType BoolType.tt) →
    HasType (mergeExprs a x1) V (E2, x2) T2 →
    HasType a V ((Expr.ite E1 E2 E3), (mergeExprs x1 x2)) T2
| TCondFalse : ∀ a V E1 E2 E3 x1 x3 T3,
    HasType a V (E1, x1) (CedarType.boolType BoolType.ff) →
    HasType a V (E3, x3) T3 →
    HasType a V ((Expr.ite E1 E2 E3), x3) T3
| TCondBool : ∀ a V E1 E2 E3 x1 x2 x3 T2 T3 T,
    SubType T2 T → SubType T3 T →
    HasType a V (E1, x1) (CedarType.boolType BoolType.anyBool) →
    HasType (mergeExprs a x1) V (E2, x2) T2 →
    HasType a V (E3, x3) T3 →
    HasType a V ((Expr.ite E1 E2 E3), (interExprs (mergeExprs x1 x2) x3)) T
| TAnd : ∀ a x V E1 E2 T1,
    HasType a V ((Expr.ite E1 E2 (Expr.lit (Prim.boolean false))), x) T1 →
    HasType a V ((Expr.andExpr E1 E2), x) T1
| TOr : ∀ a x V E1 E2 T1,
    HasType a V ((Expr.ite E1 (Expr.lit (Prim.boolean true)) E2), x) T1 →
    HasType a V ((Expr.orExpr E1 E2), x) T1
| TNotAny : ∀ a x V e,
    HasType a V (e, x) (CedarType.boolType BoolType.anyBool) →
    HasType a V ((Expr.unaryApp UnaryOp.not e), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TNotTrue : ∀ a x V e,
    HasType a V (e, x) (CedarType.boolType BoolType.tt) →
    HasType a V ((Expr.unaryApp UnaryOp.not e), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TNotFalse : ∀ a x V e,
    HasType a V (e, x) (CedarType.boolType BoolType.ff) →
    HasType a V ((Expr.unaryApp UnaryOp.not e), PathSet.somepaths []) (CedarType.boolType BoolType.tt)
| TNeg : ∀ a V x e,
    HasType a V (e, x) CedarType.intType →
    HasType a V ((Expr.unaryApp UnaryOp.neg e), PathSet.somepaths []) CedarType.intType
| TLike : ∀ a V e x P,
    HasType a V (e, x) CedarType.stringType →
    HasType a V ((Expr.unaryApp (UnaryOp.like P) e), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TIsTrue : ∀ a x V e n ets acts R ns,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType n) →
    HasType a V (e, x) (CedarType.entityType n) →
    HasType a V ((Expr.unaryApp (UnaryOp.is n) e), PathSet.somepaths []) (CedarType.boolType BoolType.tt)
| TIsFalse : ∀ a x V e N1 N2 ets acts R ns,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType N1) →
    HasType a V (e, x) (CedarType.entityType N2) →
    ¬(N1 = N2) →
    HasType a V ((Expr.unaryApp (UnaryOp.is N1) e), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TEqLitTrue : ∀ a V P,
    HasType a V ((Expr.binaryApp BinaryOp.equals (Expr.lit P) (Expr.lit P)), PathSet.somepaths []) (CedarType.boolType BoolType.tt)
| TEqLitFalse : ∀ a V P1 P2,
    ¬(P1 = P2) →
    HasType a V ((Expr.binaryApp BinaryOp.equals (Expr.lit P1) (Expr.lit P2)), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TEqEntity : ∀ a x1 x2 V E1 N1 E2 N2 ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType N1) →
    WfCedarType ns (CedarType.entityType N2) →
    ¬(N1 = N2) →
    HasType a V (E1, x1) (CedarType.entityType N1) →
    HasType a V (E2, x2) (CedarType.entityType N2) →
    HasType a V ((Expr.binaryApp BinaryOp.equals E1 E2), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TEqAny : ∀ a x1 x2 V E1 E2 T T1 T2 ets acts R ns,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns T →
    SubType T1 T → SubType T2 T →
    HasType a V (E1, x1) T1 →
    HasType a V (E2, x2) T2 →
    HasType a V ((Expr.binaryApp BinaryOp.equals E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
/-- LATER: Following two rules could look in request env for more precision -/
| TInEntity : ∀ a x1 x2 V E1 E2 N1 N2 ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType N1) →
    WfCedarType ns (CedarType.entityType N2) →
    HasType a V (E1, x1) (CedarType.entityType N1) →
    HasType a V (E2, x2) (CedarType.entityType N2) →
    HasType a V ((Expr.binaryApp BinaryOp.mem E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TInEntitySet : ∀ a x1 x2 V E1 E2 N1 N2 ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType N1) →
    WfCedarType ns (CedarType.entityType N2) →
    HasType a V (E1, x1) (CedarType.entityType N1) →
    HasType a V (E2, x2) (CedarType.setType (CedarType.entityType N2)) →
    HasType a V ((Expr.binaryApp BinaryOp.mem E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TLessThan : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((Expr.binaryApp BinaryOp.less E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TLessEqualThan : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((Expr.binaryApp BinaryOp.lessEq E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TAdd : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((Expr.binaryApp BinaryOp.add E1 E2), PathSet.somepaths []) CedarType.intType
| TSub : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((Expr.binaryApp BinaryOp.sub E1 E2), PathSet.somepaths []) CedarType.intType
| TMul : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((Expr.binaryApp BinaryOp.mul E1 E2), PathSet.somepaths []) CedarType.intType
| TContains : ∀ a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns T →
    SubType T1 T → SubType T2 T →
    HasType a V (E1, x1) T1 →
    HasType a V (E2, x2) (CedarType.setType T2) →
    HasType a V ((Expr.binaryApp BinaryOp.contains E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TContainsAll : ∀ a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns T →
    SubType T1 T → SubType T2 T →
    HasType a V (E1, x1) (CedarType.setType T1) →
    HasType a V (E2, x2) (CedarType.setType T2) →
    HasType a V ((Expr.binaryApp BinaryOp.containsAll E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TContainsAny : ∀ a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns T →
    SubType T1 T → SubType T2 T →
    HasType a V (E1, x1) (CedarType.setType T1) →
    HasType a V (E2, x2) (CedarType.setType T2) →
    HasType a V ((Expr.binaryApp BinaryOp.containsAny E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TRecNil : ∀ a V, HasType a V (Expr.recExprNil, PathSet.somepaths []) CedarType.recordTypeNil
| TRecCons : ∀ a x rx V e i T R b TR,
    HasType a V (e, x) T →
    RecordType TR →
    HasType a V (R, rx) TR →
    HasType a V ((Expr.recExprCons i e R), PathSet.somepaths []) (CedarType.recordTypeCons i b T TR)
| TSetSingle : ∀ a x V e T,
    HasType a V (e, x) T →
    HasType a V ((Expr.setExprCons e Expr.setExprNil), PathSet.somepaths []) (CedarType.setType T)
| TSetMany : ∀ a x rx V e T R,
    HasType a V (e, x) T →
    HasType a V (R, rx) (CedarType.setType T) →
    HasType a V ((Expr.setExprCons e R), PathSet.somepaths []) (CedarType.setType T)
| THasAttrRecOpt : ∀ a x V e F T TE ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    BindAttrType ns (TE, F, true) T →
    HasType a V (e, x) TE →
    HasType a V ((Expr.hasAttr e F), (PathSet.somepaths [Expr.getAttr e F])) (CedarType.boolType BoolType.anyBool)
| THasAttrRecReq : ∀ a x V e F T TE ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    BindAttrType ns (TE, F, false) T →
    HasType a V (e, x) TE →
    HasType a V ((Expr.hasAttr e F), (PathSet.somepaths [Expr.getAttr e F])) (CedarType.boolType BoolType.tt)
| TGetAttrRecOpt : ∀ a x V e F T TE ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    BindAttrType ns (TE, F, true) T →
    HasType a V (e, x) TE →
    validPathExpr (Expr.getAttr e F) a = true →
    HasType a V ((Expr.getAttr e F), PathSet.somepaths []) T
| TGetAttrRecReq : ∀ a x V e F T TE ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    BindAttrType ns (TE, F, false) T →
    HasType a V (e, x) TE →
    HasType a V ((Expr.getAttr e F), PathSet.somepaths []) T
| THasAttrEntityOpt : ∀ a x V ets acts R e n fn T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    GetEntityAttr ets (n, fn, true) T →
    HasType a V (e, x) (CedarType.entityType n) →
    HasType a V ((Expr.hasAttr e fn), PathSet.somepaths [Expr.getAttr e fn]) (CedarType.boolType BoolType.anyBool)
| THasAttrEntityReq : ∀ a x V ets acts R e n fn T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    GetEntityAttr ets (n, fn, false) T →
    HasType a V (e, x) (CedarType.entityType n) →
    HasType a V ((Expr.hasAttr e fn), PathSet.somepaths [Expr.getAttr e fn]) (CedarType.boolType BoolType.tt)
| TGetAttrEntityOpt : ∀ a x V ets acts R e n fn T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    GetEntityAttr ets (n, fn, true) T →
    HasType a V (e, x) (CedarType.entityType n) →
    validPathExpr (Expr.getAttr e fn) a = true →
    HasType a V ((Expr.getAttr e fn), PathSet.somepaths []) T
| TGetAttrEntityReq : ∀ a x V ets acts R e n fn T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    GetEntityAttr ets (n, fn, false) T →
    HasType a V (e, x) (CedarType.entityType n) →
    HasType a V ((Expr.getAttr e fn), PathSet.somepaths []) T

------------------------------
-- Pretty printing for types
-------------------------------
def stringOfBooltype (b : BoolType) : String :=
    match b with
    | BoolType.anyBool => "Bool"
    | BoolType.tt => "True"
    | BoolType.ff => "False"

instance : ToString BoolType where
  toString := stringOfBooltype

instance : Repr BoolType where
  reprPrec boolTy _ := toString boolTy

def stringOfCedartype (t : CedarType) : String :=
  match t with
    | CedarType.boolType b => stringOfBooltype b
    | CedarType.intType => "Int"
    | CedarType.stringType => "String"
    | CedarType.entityType n => toString n
    | CedarType.setType t => "Set<" ++ stringOfCedartype t ++ ">"
    | CedarType.recordTypeNil => "{}"
    | CedarType.recordTypeCons s o t' CedarType.recordTypeNil =>
        "{" ++ s ++ ":" ++ (if o then "?" else " ") ++ stringOfCedartype t' ++ "}"
    | CedarType.recordTypeCons s o t' tr =>
        "{" ++ s ++ ":" ++ (if o then "?" else " ") ++ stringOfCedartype t' ++ ", " ++ stringOfRecordtype tr ++ "}"
where
  stringOfRecordtype (t : CedarType) : String :=
    match t with
    | CedarType.recordTypeNil => ""
    | CedarType.recordTypeCons s o t' tr =>
        s ++ ":" ++ (if o then "?" else " ") ++ stringOfCedartype t' ++ ", " ++ stringOfRecordtype tr
    | _ => ""

instance : ToString CedarType where
  toString := stringOfCedartype

instance : Repr CedarType where
  reprPrec ty _ := toString ty

def stringOfAttrs (attrs : List (String × Bool × CedarType)) : String :=
  match attrs with
  | [] => ""
  | [(s, o, t')] => s ++ ":" ++ (if o then " " else "? ") ++ stringOfCedartype t'
  | (s, o, t')::attrs' => s ++ ":" ++ (if o then " " else "? ") ++ stringOfCedartype t' ++ ", " ++ stringOfAttrs attrs'

def stringOfEse (ancs : List EntityName) (attrs : List (String × Bool × CedarType)) : String :=
  (match ancs with
  | [] => " "
  | _ => " in " ++ toString ancs) ++
  (match attrs with
  | [] => ""
  | _ => " { " ++ stringOfAttrs attrs ++ " }")

instance : ToString EntitySchemaEntry where
  toString := fun ese =>
      match ese with
      | EntitySchemaEntry.MkEntitySchemaEntry ancs attrs => stringOfEse ancs attrs

instance : Repr EntitySchemaEntry where
  reprPrec ese _ := toString ese

def stringOfAse (prin : List EntityName) (res : List EntityName) (ct : List (String × Bool × CedarType)) : String :=
    "{ principal: " ++ toString prin ++
    "; resource: " ++ toString res ++
    (match ct with | [] => "" | _ => "; context: {" ++ stringOfAttrs ct ++ " }") ++ " }"

instance : ToString ActionSchemaEntry where
  toString := fun ase =>
        match ase with
        | ActionSchemaEntry.MkActionSchemaEntry ps rs ct => stringOfAse ps rs ct

instance : Repr ActionSchemaEntry where
  reprPrec ase _ := toString ase

def stringOfSchemaEts (eses : List (EntityName × EntitySchemaEntry)) : String :=
    match eses with
    | [] => ""
    | (n, ese)::eses' => "entity " ++ toString n ++ toString ese ++ "; " ++ stringOfSchemaEts eses'

def stringOfSchemaActs (acts : List (EntityUID × ActionSchemaEntry)) : String :=
    match acts with
    | [] => ""
    | (uid, act)::acts' => "action " ++ toString uid ++ " appliesTo " ++ toString act ++ "; " ++ stringOfSchemaActs acts'

def stringOfSchema (s : Schema) : String :=
    match s with
    | Schema.MkSchema ets acts => stringOfSchemaEts ets ++ stringOfSchemaActs acts

instance : ToString Schema where
  toString := stringOfSchema

instance : Repr Schema where
  reprPrec s _ := toString s

instance : ToString PathSet where
  toString := fun ps => match ps with
    | PathSet.allpaths => "allpaths"
    | PathSet.somepaths paths => "somepaths " ++ toString paths

instance : Repr PathSet where
  reprPrec pathset _ := toString pathset
