import Lean
open Nat

namespace KeyValueStore


/-!

The K/V store is (represented as) an association list of bucket IDs and states and a counter of legal bucket IDs,
and each state is an association list of key-value pairs.
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
deriving Repr

/-- The result of a `StateAPICall` -/
inductive StateResult where
| Ok
| Failure (s : String)
| Result (s : String)
deriving Repr

/-- Operations on the K/V store -/
inductive APICall where
| CreateBucket
| OpBucket (bucketID : Nat) (c : StateAPICall)
| DeleteBucket (bucketID : Nat)
deriving Repr

/-- The result of an `APICall` operation -/
inductive Result where
| Created (n : Nat)
| Removed
| Error (s : String)
| OpResult (r : StateResult)
deriving Repr

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

inductive AddKV : String → String → (List (String × String)) → List (String × String) → Prop where
| ANil : ∀ k v s, AddKV k v s ((k, v)::s)

/-- Helper function used to improve improve the generator's success rate -/
def ver (k1 : String) (k2 : String) (n : Nat) : Nat :=
  if k1 == k2 then (succ n) else n

def appendString (s1 : String) (s2 : String) : String := s1 ++ s2

inductive LookupKV : (List (String × String)) → StateResult × String × Nat × String → Prop where
| LNone : forall k v, LookupKV [] ((.Failure "no such key"), k, 0, v)
| LFound : forall k v s, LookupKV ((k, v)::s) (.Ok, k, 0, v)
| LFoundS : forall k1 k2 v1 v2 s n n',
    LookupKV s (.Ok, k1, n, v1) ->
    n' = ver k1 k2 n ->
    LookupKV ((k2, v2)::s) (.Ok, k1, n', v1)
| LWrongver : forall k v n,
    LookupKV [(k, v)] ((.Failure "no such version"), k, (succ n), v)
| LWrongverS : forall k1 v1 k2 v2 s n n',
    LookupKV s ((.Failure "no such version"), k1, n, v1) ->
    n' = ver k1 k2 n ->
    LookupKV ((k2, v2)::s) ((.Failure "no such version"), k1, n', v1)


inductive RemoveKV : String → (List (String × String)) → (List (String × String)) → Prop where
| RNil : forall k, RemoveKV k [] []
| RFound : forall k v s1 s2,
    RemoveKV k s1 s2 ->
    RemoveKV k ((k, v)::s1) s2
| RCons : forall k1 k2 v2 s1 s2,
    k1 != k2 ->
    RemoveKV k1 s1 s2 ->
    RemoveKV k1 ((k2, v2)::s1) ((k2, v2)::s2)


inductive EvalStateApiCall : (List (String × String)) → (StateAPICall × StateResult × (List (String × String))) → Prop where
| EGet : forall s k v,
    LookupKV s (.Ok, k, 0, v) ->
    EvalStateApiCall s ((.Get k none), (.Result v), s)
| EGetFailNoKey : forall s k v,
    LookupKV s ((.Failure "no such key"), k, 0, v) ->
    EvalStateApiCall s ((.Get k none), (.Failure "no such key"), s)
| EGetVersion : forall s k n v,
    LookupKV s (.Ok, k, n, v) ->
    EvalStateApiCall s ((.Get k (some n)), (.Result v), s)
| EGetFailNoVer : forall s k n v,
    LookupKV s ((.Failure "no such version"), k, n, v) ->
    EvalStateApiCall s ((.Get k (some n)), (.Failure "no such version"), s)
| EExists : forall k v s,
    LookupKV s (.Ok, k, 0, v) ->
    EvalStateApiCall s ((.KeyExists k), .Ok, s)
| EExistsFail : forall k v s,
    LookupKV s ((.Failure "no such key"), k, 0, v) ->
    EvalStateApiCall s ((.KeyExists k), (.Result "no such key"), s)
| ESet : forall s1 s2 k v,
    AddKV k v s1 s2 ->
    EvalStateApiCall s1 ((.Set k v), .Ok, s2)
| ECopy : forall k v k2 s1 s2,
    LookupKV s1 (.Ok, k, 0, v) ->
    AddKV k2 v s1 s2 ->
    EvalStateApiCall s1 ((.Copy k k2), .Ok, s2)
| ECopyFail : forall k v k2 s,
    LookupKV s ((.Failure "no such key"), k, 0, v) ->
    EvalStateApiCall s ((.Copy k k2), (.Failure "no such key"), s)
| EAppend : forall s1 s2 k v v2 v3,
    LookupKV s1 (.Ok, k, 0, v) ->
    v3 = appendString v v2 ->
    AddKV k v3 s1 s2 ->
    EvalStateApiCall s1 ((.Append k v3), .Ok, s2)
| EAppendFail : forall s k v v2,
    LookupKV s ((.Failure "no such key"), k, 0, v) ->
    EvalStateApiCall s ((.Append k v2), (.Failure "no such key"), s)
| EDeletePresent : forall s1 s2 k v,
    LookupKV s1 (.Ok, k, 0, v) ->
    RemoveKV k s1 s2 ->
    EvalStateApiCall s1 ((.Delete k), .Ok, s2)
| EDeleteFail : forall s k v,
    LookupKV s ((.Failure "no such key"), k, 0, v) ->
    EvalStateApiCall s ((.Delete k), (.Failure "no such key"), s)

inductive GetBucket : List (Nat × (List (String × String))) → (Nat × (List (String × String))) → Prop where
| GBFound : forall n x s, GetBucket ((n, x)::s) (n, x)
| GBNext : forall n n' x x' s,
    n != n' ->
    GetBucket s (n, x) ->
    GetBucket ((n', x')::s) (n, x)

end KeyValueStore
