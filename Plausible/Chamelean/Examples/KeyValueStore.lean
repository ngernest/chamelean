import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators

open Plausible

namespace KeyValueStore

-- Suppress warnings for unused variables in derived generators/checkers
set_option linter.unusedVariables false

/-!

The K/V store is (represented as) an association list of bucket IDs and states and a counter of legal bucket IDs,
and each state is an association list of key-value pairs (i.e. a `List (String × String)` in Lean).
Operations on the store involve creating and deleting buckets, and operating on the contents of a bucket's state.

Updating the state adds a _new_ pair to the state, which will be seen first on lookup, making it the newest version, version 0.
Removal clears all pairs for the key from the state.

A real key-value store we use for differential testing may represent things differently.
For example, bucket IDs could be arbitrary, rather than a predictable count.
Thus, when doing checking against a real store, you'd generate a set of inputs and then map the bucket IDs
that occur in those inputs against the real bucket IDs you see in the real store's I/O. This is basically implementing "prophecy variables".

-/

---------------------------------------------------------
-- Part One: Basic syntax for API calls to a K/V store
---------------------------------------------------------

/-- Operations on a bucket state -/
inductive StateAPICall where
| Get (k : String) (ver : Option Nat)
| KeyExists (k : String)
| Set (k : String) (v : String)
| Copy (k : String) (k2 : String)
| Append (k : String) (v : String)
| Delete (k : String)
deriving Repr, DecidableEq, Arbitrary

/-- The result of a `StateAPICall`.
    Note that we've changed `.Failure "no such key"`, `.Failure "no such version"` and `.Result "no such key"`
    in the original Coq code to their own dedicated constructors,
    since Chamelean doesn't have good support for handling string literals right now. -/
inductive StateResult where
| Ok
| NoSuchKeyFailure
| NoSuchVersionFailure
| NoSuchKeyResult
| Result (s : String)
deriving Repr, DecidableEq, Arbitrary

/-- Operations on the K/V store -/
inductive APICall where
| CreateBucket
| OpBucket (bucketID : Nat) (c : StateAPICall)
| DeleteBucket (bucketID : Nat)
deriving Repr, DecidableEq, Arbitrary

/-- The result of an `APICall` operation -/
inductive Result where
| Created (n : Nat)
| Removed
| Error (s : String)
| OpResult (r : StateResult)
deriving Repr, DecidableEq, Arbitrary

------------------------------------------------------------------
-- Part Two: Semantics of the K/V store, as an inductive relation
------------------------------------------------------------------

/-! **Functions for updating a bucket's state**

Notes about the way these are expressed:
  1. We express these basic semantic functions as inductive relations so QC can run them backwards.
     We do similarly with the definitions of API call semantics below.
  2. Some of the relations group things as tuples in order to support auto-derivation of input generators.
    For example, we have `lookup_kv s (k,v)` and not `lookup_kv s k v` because we want to generate both `k` and `v` together.
    Future versions of QuickChick should alleviate the need to do this grouping.
-/

/-- `AddKV k v s1 s2` holds if state `s1` is the same as `s2` where the latter has the pair `(k,v)`
     added at version .zero, bumping the versions of prior pairs with `k`. -/
inductive AddKV : String → String → List (String × String) → List (String × String) → Prop where
| ANil : ∀ k v s, AddKV k v s ((k, v)::s)

/-- Helper function used to improve the generator's success rate. -/
def ver (k1 : String) (k2 : String) (n : Nat) : Nat :=
  if k1 == k2 then (.succ n) else n

/-- `LookupKV s (Ok,k,n,v)` holds if the pair `(k,v)` is the `n`th pair with key `k` in state `s`.
     `LookupKV s ((Failure s),k,n,v)` holds if either `k` does not exist in `s`,
     or it does but not at the version `n`. -/
inductive LookupKV : List (String × String) → StateResult × String × Nat × String → Prop where
| LNone : forall k v, LookupKV [] (.NoSuchKeyFailure, k, .zero, v)
| LFound : forall k v s, LookupKV ((k, v)::s) (.Ok, k, .zero, v)
| LFoundS : forall k1 k2 v1 v2 s n n',
    LookupKV s (.Ok, k1, n, v1) →
    n' = ver k1 k2 n →
    LookupKV ((k2, v2)::s) (.Ok, k1, n', v1)
| LWrongver : forall k v n,
    LookupKV [(k, v)] (.NoSuchVersionFailure, k, (.succ n), v)
| LWrongverS : forall k1 v1 k2 v2 s n n',
    LookupKV s (.NoSuchVersionFailure, k1, n, v1) →
    n' = ver k1 k2 n →
    LookupKV ((k2, v2)::s) (.NoSuchVersionFailure, k1, n', v1)

/-- `RemoveKV k s1 s2` holds if `s2` is the same as `s1` but with all occurrences of `(k,v)` removed, for any `v` -/
inductive RemoveKV : String → (List (String × String)) → (List (String × String)) → Prop where
| RNil : forall k, RemoveKV k [] []
| RFound : forall k v s1 s2,
    RemoveKV k s1 s2 →
    RemoveKV k ((k, v)::s1) s2
| RCons : forall k1 k2 v2 s1 s2,
    k1 != k2 →
    RemoveKV k1 s1 s2 →
    RemoveKV k1 ((k2, v2)::s1) ((k2, v2)::s2)

/-- `EvalStateApiCall s1 (c, r, s2)` holds iff `s2` is the result of evaluating API call `c` on `s1`, returning result `r`. -/
inductive EvalStateApiCall : List (String × String) → (StateAPICall × StateResult × List (String × String)) → Prop where
| EGet : forall s k v,
    LookupKV s (.Ok, k, .zero, v) →
    EvalStateApiCall s ((.Get k none), (.Result v), s)
| EGetFailNoKey : forall s k v,
    LookupKV s (.NoSuchKeyFailure, k, .zero, v) →
    EvalStateApiCall s ((.Get k none), .NoSuchKeyFailure, s)
| EGetVersion : forall s k n v,
    LookupKV s (.Ok, k, n, v) →
    EvalStateApiCall s ((.Get k (some n)), (.Result v), s)
| EGetFailNoVer : forall s k n v,
    LookupKV s (.NoSuchVersionFailure, k, n, v) →
    EvalStateApiCall s (.Get k (some n), .NoSuchVersionFailure, s)
| EExists : forall k v s,
    LookupKV s (.Ok, k, .zero, v) →
    EvalStateApiCall s ((.KeyExists k), .Ok, s)
| EExistsFail : forall k v s,
    LookupKV s (.NoSuchKeyFailure, k, .zero, v) →
    EvalStateApiCall s (.KeyExists k, .NoSuchKeyResult, s)
| ESet : forall s1 s2 k v,
    AddKV k v s1 s2 →
    EvalStateApiCall s1 ((.Set k v), .Ok, s2)
| ECopy : forall k v k2 s1 s2,
    LookupKV s1 (.Ok, k, .zero, v) →
    AddKV k2 v s1 s2 →
    EvalStateApiCall s1 ((.Copy k k2), .Ok, s2)
| ECopyFail : forall k v k2 s,
    LookupKV s (.NoSuchKeyFailure, k, .zero, v) →
    EvalStateApiCall s ((.Copy k k2), .NoSuchKeyFailure, s)
| EAppend : forall s1 s2 k v v2 v3,
    LookupKV s1 (.Ok, k, .zero, v) →
    v3 = v ++ v2 →
    AddKV k v3 s1 s2 →
    EvalStateApiCall s1 ((.Append k v3), .Ok, s2)
| EAppendFail : forall s k v v2,
    LookupKV s (.NoSuchKeyFailure, k, .zero, v) →
    EvalStateApiCall s ((.Append k v2), .NoSuchKeyFailure, s)
| EDeletePresent : forall s1 s2 k v,
    LookupKV s1 (.Ok, k, .zero, v) →
    RemoveKV k s1 s2 →
    EvalStateApiCall s1 ((.Delete k), .Ok, s2)
| EDeleteFail : forall s k v,
    LookupKV s (.NoSuchKeyFailure, k, .zero, v) →
    EvalStateApiCall s ((.Delete k), .NoSuchKeyFailure, s)

/-- `GetBucket s (n, x)` holds if the bucket store `s` contains a bucket with identifier `n` and contents `x`. -/
inductive GetBucket : List (Nat × List (String × String)) → (Nat × List (String × String)) → Prop where
| GBFound : forall n x s, GetBucket ((n, x)::s) (n, x)
| GBNext : forall n n' x x' s,
    n != n' →
    GetBucket s (n, x) →
    GetBucket ((n', x')::s) (n, x)

/-- Add a new bucket with identifier `n` and empty contents to the K/V store `s`. -/
def addBucket (n : Nat) (s : List (Nat × List α)) : List (Nat × (List α)) :=
  (n, [])::s

/-- Remove the bucket with identifier `n` from the K/V store `s`.
    Returns `some s'` where `s'` is the store with the bucket removed,
    or `none` if no such bucket exists. -/
def removeBucket (n : Nat) (s : List (Nat × List α)) : Option (List (Nat × List α)) :=
  match s with
  | [] => none
  | (n', x)::s' =>
      if n == n' then some s'
      else
        match removeBucket n s' with
        | none => none
        | some s'' => some ((n', x)::s'')

/-- Update the contents of bucket with identifier `n` in store `s` to contain `x`.
    Returns `some s'` where `s'` is the updated store, or `none` if no such bucket exists. -/
def updateBucket (n : Nat) (s : List (Nat × List α)) (x : List α) : Option (List (Nat × List α)) :=
  match s with
  | [] => none
  | (n', x')::s' =>
      if n == n' then some ((n', x)::s')
      else
        match updateBucket n s' x with
        | none => none
        | some s'' => some ((n', x')::s'')

------------------------------------------------------------------------
-- Part Three: Inductive relations for evaluating API calls on the store
-----------------------------------------------------------------------

/-- `EvalApiCall (n, s) (c, r, (n', s'))` holds if evaluating API call `c` on state `(n, s)`
    produces result `r` and new state `(n', s')`, where `n` is the next bucket ID and `s` is the resultant store. -/
inductive EvalApiCall : Nat × List (Nat × List (String × String)) → (APICall × Result × (Nat × List (Nat × List (String × String)))) → Prop where
| ESCreate : forall n s s',
    addBucket n s = s' →
    EvalApiCall (n, s) (APICall.CreateBucket, Result.Created n, (Nat.succ n, s'))
| ESOp : forall n n' c r s s' x x',
    GetBucket s (n', x) →
    EvalStateApiCall x (c, r, x') →
    (some s') = updateBucket n' s x' →
    EvalApiCall (n, s) ((APICall.OpBucket n' c), Result.OpResult r, (n, s'))
| ESRemove : forall n n' s s' x,
    GetBucket s (n', x) →
    (some s') = removeBucket n' s →
    EvalApiCall (n, s) ((APICall.DeleteBucket n'), Result.Removed, (n, s'))

/-- `EvalApiCalls s1 crs s2` holds if evaluating the list of API calls `crs` on `s1` produces `s2`. -/
inductive EvalApiCalls : Nat × List (Nat × List (String × String)) → List (APICall × Result) × (Nat × List (Nat × List (String × String))) → Prop where
| EsNil : forall s, EvalApiCalls s ([], s)
| EsCons : forall s1 s2 s3 c crs r,
    EvalApiCall s1 (c, r, s2) →
    EvalApiCalls s2 (crs, s3) →
    EvalApiCalls s1 (((c, r)::crs), s3)


----------------------
-- Derived Generators
---------------------

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (String × String)) (fun s1_1 => KeyValueStore.RemoveKV k_1 s1_1 s2_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (k_1 : String) (s2_1 : List (String × String)) :
      OptionT Plausible.Gen (List (String × String)) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match s2_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match s2_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail),
            (Nat.succ size', do
              let s1 ← aux_arb initSize size' k_1 s2_1;
              do
                let v ← Plausible.Arbitrary.arbitrary;
                return List.cons (Prod.mk k_1 v) s1),
            (Nat.succ size',
              match s2_1 with
              | List.cons (Prod.mk k2 v2) s2 =>
                match DecOpt.decOpt (Eq (bne k_1 k2) (Bool.true)) initSize with
                | Option.some Bool.true => do
                  let s1 ← aux_arb initSize size' k_1 s2;
                  return List.cons (Prod.mk k2 v2) s1
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size k_1 s2_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (s1 : List (String × String)) => KeyValueStore.RemoveKV k s1 s2)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (String × String)) (fun s2_1 => KeyValueStore.RemoveKV k_1 s1_1 s2_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (k_1 : String) (s1_1 : List (String × String)) :
      OptionT Plausible.Gen (List (String × String)) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match s1_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match s1_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail),
            (Nat.succ size',
              match s1_1 with
              | List.cons (Prod.mk u_3 v) s1 =>
                match DecOpt.decOpt (BEq.beq u_3 k_1) initSize with
                | Option.some Bool.true => do
                  let s2_1 ← aux_arb initSize size' k_1 s1;
                  return s2_1
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match s1_1 with
              | List.cons (Prod.mk k2 v2) s1 =>
                match DecOpt.decOpt (Eq (bne k_1 k2) (Bool.true)) initSize with
                | Option.some Bool.true => do
                  let s2 ← aux_arb initSize size' k_1 s1;
                  return List.cons (Prod.mk k2 v2) s2
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size k_1 s1_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (s2 : List (String × String)) => KeyValueStore.RemoveKV k s1 s2)


/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (String × String)) (fun s1_1 => KeyValueStore.AddKV k_1 v_1 s1_1 s2_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (k_1 : String) (v_1 : String) (s2_1 : List (String × String)) :
      OptionT Plausible.Gen (List (String × String)) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match s2_1 with
              | List.cons (Prod.mk u_4 u_5) s1_1 =>
                match DecOpt.decOpt (BEq.beq u_4 k_1) initSize with
                | Option.some Bool.true =>
                  match DecOpt.decOpt (BEq.beq u_5 v_1) initSize with
                  | Option.some Bool.true => return s1_1
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match s2_1 with
              | List.cons (Prod.mk u_4 u_5) s1_1 =>
                match DecOpt.decOpt (BEq.beq u_4 k_1) initSize with
                | Option.some Bool.true =>
                  match DecOpt.decOpt (BEq.beq u_5 v_1) initSize with
                  | Option.some Bool.true => return s1_1
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            ]
    fun size => aux_arb size size k_1 v_1 s2_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (s1 : List (String × String)) => KeyValueStore.AddKV k v s1 s2)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (String × String)) (fun s2_1 => KeyValueStore.AddKV k_1 v_1 s1_1 s2_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (k_1 : String) (v_1 : String) (s1_1 : List (String × String)) :
      OptionT Plausible.Gen (List (String × String)) :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return List.cons (Prod.mk k_1 v_1) s1_1)]
      | Nat.succ size' => OptionTGen.backtrack [(1, return List.cons (Prod.mk k_1 v_1) s1_1), ]
    fun size => aux_arb size size k_1 v_1 s1_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (s2 : List (String × String)) => KeyValueStore.AddKV k v s1 s2)

/--
info: Try this checker: instance : DecOpt (KeyValueStore.LookupKV s_1 kv_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (s_1 : List (String × String))
      (kv_1 : StateResult × String × Nat × String) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match kv_1 with
            | Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v)) =>
              match s_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match kv_1 with
            | Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk u_2 (Prod.mk (Nat.zero) u_3)) =>
              match s_1 with
              | List.cons (Prod.mk k v) s =>
                DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_2 k) initSize, DecOpt.decOpt (BEq.beq u_3 v) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match kv_1 with
            | Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk u_2 (Prod.mk (Nat.succ n) u_3)) =>
              match s_1 with
              | List.cons (Prod.mk k v) (List.nil) =>
                DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_2 k) initSize, DecOpt.decOpt (BEq.beq u_3 v) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match kv_1 with
            | Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v)) =>
              match s_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match kv_1 with
            | Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk u_2 (Prod.mk (Nat.zero) u_3)) =>
              match s_1 with
              | List.cons (Prod.mk k v) s =>
                DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_2 k) initSize, DecOpt.decOpt (BEq.beq u_3 v) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match kv_1 with
            | Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk u_2 (Prod.mk (Nat.succ n) u_3)) =>
              match s_1 with
              | List.cons (Prod.mk k v) (List.nil) =>
                DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_2 k) initSize, DecOpt.decOpt (BEq.beq u_3 v) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match kv_1 with
            | Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k1 (Prod.mk n' v1)) =>
              match s_1 with
              | List.cons (Prod.mk k2 v2) s =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun n =>
                    DecOpt.andOptList
                      [aux_dec initSize size' s (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k1 (Prod.mk n v1))),
                        DecOpt.decOpt (Eq n' (KeyValueStore.ver k1 k2 n)) initSize])
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match kv_1 with
            | Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk k1 (Prod.mk n' v1)) =>
              match s_1 with
              | List.cons (Prod.mk k2 v2) s =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun n =>
                    DecOpt.andOptList
                      [aux_dec initSize size' s
                          (Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk k1 (Prod.mk n v1))),
                        DecOpt.decOpt (Eq n' (KeyValueStore.ver k1 k2 n)) initSize])
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size s_1 kv_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (KeyValueStore.LookupKV s kv)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (String × String)) (fun s1_1 => KeyValueStore.LookupKV s1_1 kv_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (kv_1 : StateResult × String × Nat × String) :
      OptionT Plausible.Gen (List (String × String)) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match kv_1 with
              | Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v)) =>
                return List.nil
              | _ => OptionT.fail),
            (1,
              match kv_1 with
              | Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v)) => do
                let s ← Plausible.Arbitrary.arbitrary;
                return List.cons (Prod.mk k v) s
              | _ => OptionT.fail),
            (1,
              match kv_1 with
              | Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk k (Prod.mk (Nat.succ n) v)) =>
                return List.cons (Prod.mk k v) (List.nil)
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match kv_1 with
              | Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v)) =>
                return List.nil
              | _ => OptionT.fail),
            (1,
              match kv_1 with
              | Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v)) => do
                let s ← Plausible.Arbitrary.arbitrary;
                return List.cons (Prod.mk k v) s
              | _ => OptionT.fail),
            (1,
              match kv_1 with
              | Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk k (Prod.mk (Nat.succ n) v)) =>
                return List.cons (Prod.mk k v) (List.nil)
              | _ => OptionT.fail),
            (Nat.succ size',
              match kv_1 with
              | Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k1 (Prod.mk n' v1)) => do
                let k2 ← Plausible.Arbitrary.arbitrary;
                do
                  let n ← Plausible.Arbitrary.arbitrary;
                  do
                    let v2 ← Plausible.Arbitrary.arbitrary;
                    match DecOpt.decOpt (Eq n' (KeyValueStore.ver k1 k2 n)) initSize with
                      | Option.some Bool.true => do
                        let s ←
                          aux_arb initSize size' (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k1 (Prod.mk n v1)));
                        return List.cons (Prod.mk k2 v2) s
                      | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match kv_1 with
              | Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk k1 (Prod.mk n' v1)) => do
                let k2 ← Plausible.Arbitrary.arbitrary;
                do
                  let n ← Plausible.Arbitrary.arbitrary;
                  do
                    let v2 ← Plausible.Arbitrary.arbitrary;
                    match DecOpt.decOpt (Eq n' (KeyValueStore.ver k1 k2 n)) initSize with
                      | Option.some Bool.true => do
                        let s ←
                          aux_arb initSize size'
                              (Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk k1 (Prod.mk n v1)));
                        return List.cons (Prod.mk k2 v2) s
                      | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size kv_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (s1 : List (String × String)) => KeyValueStore.LookupKV s1 kv)


-- TODO: figure out why these doesn't work (same reason)
-- #derive_generator (fun (kv : List (String × String)) => KeyValueStore.LookupKV s kv)
-- #derive_generator (fun (nb : Nat × List (String × String)) => KeyValueStore.GetBucket s nb)
-- #derive_generator (fun (crns : APICall × Result × (Nat × List (Nat × List (String × String)))) => KeyValueStore.EvalApiCall s crns)
-- #derive_generator (fun (o : List (APICall × Result) × (Nat × List (Nat × List (String × String)))) => KeyValueStore.EvalApiCalls s o)

/--
info: Try this checker: instance : DecOpt (KeyValueStore.AddKV k2_1 v_1 s_1_1 s2_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (k2_1 : String) (v_1 : String) (s_1_1 : List (String × String))
      (s2_1 : List (String × String)) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match s2_1 with
            | List.cons (Prod.mk u_4 u_5) u_6 =>
              DecOpt.andOptList
                [DecOpt.decOpt (BEq.beq u_6 s_1_1) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (BEq.beq u_5 v_1) initSize, DecOpt.decOpt (BEq.beq u_4 k2_1) initSize]]
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match s2_1 with
            | List.cons (Prod.mk u_4 u_5) u_6 =>
              DecOpt.andOptList
                [DecOpt.decOpt (BEq.beq u_6 s_1_1) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (BEq.beq u_5 v_1) initSize, DecOpt.decOpt (BEq.beq u_4 k2_1) initSize]]
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size k2_1 v_1 s_1_1 s2_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (KeyValueStore.AddKV k2 v s_1 s2)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (String × String)) (fun s_1 => KeyValueStore.EvalStateApiCall s_1 x_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (x_1 : StateAPICall × StateResult × List (String × String)) :
      OptionT Plausible.Gen (List (String × String)) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Get k (Option.none))
                  (Prod.mk (KeyValueStore.StateResult.Result v) s_1) =>
                match
                  DecOpt.decOpt
                    (KeyValueStore.LookupKV s_1
                      (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                    initSize with
                | Option.some Bool.true => return s_1
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Get k (Option.none))
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Get k (Option.some n))
                  (Prod.mk (KeyValueStore.StateResult.Result v) s_1) =>
                match
                  DecOpt.decOpt
                    (KeyValueStore.LookupKV s_1 (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk n v))))
                    initSize with
                | Option.some Bool.true => return s_1
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Get k (Option.some n))
                  (Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk k (Prod.mk n v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.KeyExists k) (Prod.mk (KeyValueStore.StateResult.Ok) s_1) => do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.KeyExists k)
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyResult) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.Set k v) (Prod.mk (KeyValueStore.StateResult.Ok) s2) => do
                let s_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun s_1 => KeyValueStore.AddKV k v s_1 s2) initSize;
                return s_1
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.Copy k k2) (Prod.mk (KeyValueStore.StateResult.Ok) s2) => do
                let v ← Plausible.Arbitrary.arbitrary;
                do
                  let s_1 ←
                    ArbitrarySizedSuchThat.arbitrarySizedST
                        (fun s_1 =>
                          KeyValueStore.LookupKV s_1
                            (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                        initSize;
                  match DecOpt.decOpt (KeyValueStore.AddKV k2 v s_1 s2) initSize with
                    | Option.some Bool.true => return s_1
                    | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Copy k k2)
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.Append k v3) (Prod.mk (KeyValueStore.StateResult.Ok) s2) => do
                let s_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun s_1 => KeyValueStore.AddKV k v3 s_1 s2) initSize;
                do
                  let v ← Plausible.Arbitrary.arbitrary;
                  do
                    let v2 ← Plausible.Arbitrary.arbitrary;
                    match
                        DecOpt.decOpt
                          (KeyValueStore.LookupKV s_1
                            (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                          initSize with
                      | Option.some Bool.true =>
                        match DecOpt.decOpt (Eq v3 (HAppend.hAppend v v2)) initSize with
                        | Option.some Bool.true => return s_1
                        | _ => OptionT.fail
                      | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Append k v2)
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.Delete k) (Prod.mk (KeyValueStore.StateResult.Ok) s2) => do
                let s_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun s_1 => KeyValueStore.RemoveKV k s_1 s2) initSize;
                do
                  let v ← Plausible.Arbitrary.arbitrary;
                  match
                      DecOpt.decOpt
                        (KeyValueStore.LookupKV s_1
                          (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                        initSize with
                    | Option.some Bool.true => return s_1
                    | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Delete k)
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Get k (Option.none))
                  (Prod.mk (KeyValueStore.StateResult.Result v) s_1) =>
                match
                  DecOpt.decOpt
                    (KeyValueStore.LookupKV s_1
                      (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                    initSize with
                | Option.some Bool.true => return s_1
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Get k (Option.none))
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Get k (Option.some n))
                  (Prod.mk (KeyValueStore.StateResult.Result v) s_1) =>
                match
                  DecOpt.decOpt
                    (KeyValueStore.LookupKV s_1 (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk n v))))
                    initSize with
                | Option.some Bool.true => return s_1
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Get k (Option.some n))
                  (Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchVersionFailure) (Prod.mk k (Prod.mk n v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.KeyExists k) (Prod.mk (KeyValueStore.StateResult.Ok) s_1) => do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.KeyExists k)
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyResult) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.Set k v) (Prod.mk (KeyValueStore.StateResult.Ok) s2) => do
                let s_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun s_1 => KeyValueStore.AddKV k v s_1 s2) initSize;
                return s_1
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.Copy k k2) (Prod.mk (KeyValueStore.StateResult.Ok) s2) => do
                let v ← Plausible.Arbitrary.arbitrary;
                do
                  let s_1 ←
                    ArbitrarySizedSuchThat.arbitrarySizedST
                        (fun s_1 =>
                          KeyValueStore.LookupKV s_1
                            (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                        initSize;
                  match DecOpt.decOpt (KeyValueStore.AddKV k2 v s_1 s2) initSize with
                    | Option.some Bool.true => return s_1
                    | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Copy k k2)
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.Append k v3) (Prod.mk (KeyValueStore.StateResult.Ok) s2) => do
                let s_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun s_1 => KeyValueStore.AddKV k v3 s_1 s2) initSize;
                do
                  let v ← Plausible.Arbitrary.arbitrary;
                  do
                    let v2 ← Plausible.Arbitrary.arbitrary;
                    match
                        DecOpt.decOpt
                          (KeyValueStore.LookupKV s_1
                            (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                          initSize with
                      | Option.some Bool.true =>
                        match DecOpt.decOpt (Eq v3 (HAppend.hAppend v v2)) initSize with
                        | Option.some Bool.true => return s_1
                        | _ => OptionT.fail
                      | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Append k v2)
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Prod.mk (KeyValueStore.StateAPICall.Delete k) (Prod.mk (KeyValueStore.StateResult.Ok) s2) => do
                let s_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun s_1 => KeyValueStore.RemoveKV k s_1 s2) initSize;
                do
                  let v ← Plausible.Arbitrary.arbitrary;
                  match
                      DecOpt.decOpt
                        (KeyValueStore.LookupKV s_1
                          (Prod.mk (KeyValueStore.StateResult.Ok) (Prod.mk k (Prod.mk (Nat.zero) v))))
                        initSize with
                    | Option.some Bool.true => return s_1
                    | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              |
              Prod.mk (KeyValueStore.StateAPICall.Delete k)
                  (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) s_1) =>
                do
                let v ← Plausible.Arbitrary.arbitrary;
                match
                    DecOpt.decOpt
                      (KeyValueStore.LookupKV s_1
                        (Prod.mk (KeyValueStore.StateResult.NoSuchKeyFailure) (Prod.mk k (Prod.mk (Nat.zero) v))))
                      initSize with
                  | Option.some Bool.true => return s_1
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            ]
    fun size => aux_arb size size x_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (s : List (String × String)) => KeyValueStore.EvalStateApiCall s x)







end KeyValueStore
