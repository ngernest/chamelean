import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators

/-- Inductive relation specifying what it means for two lists to be permutations of each other.
    - Adapted from https://softwarefoundations.cis.upenn.edu/vfa-1.4/Perm.html -/
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
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => Permutation l_1 l'_1) where
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
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => Permutation l'_1 l_1) where
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

-- def l := [1, 2, 3]
-- def l' := [2, 1, 5]

-- #eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun l' => Permutation l l')) 1
