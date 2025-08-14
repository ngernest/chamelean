import Plausible.Chamelean.Examples.KeyValueStore
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators

open Plausible
open KeyValueStore

-- Suppress warnings for unused variables in derived generators/checkers
set_option linter.unusedVariables false

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
