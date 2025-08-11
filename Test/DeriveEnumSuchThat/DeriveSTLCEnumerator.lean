import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.Examples.ExampleInductiveRelations
import Test.DeriveEnum.DeriveSTLCTermTypeEnumerators

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun x_1 => lookup Γ_1 x_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) : OptionT Enumerator Nat :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | List.cons τ Γ =>
              match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
              | Option.some Bool.true => return Nat.zero
              | _ => OptionT.fail
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | List.cons τ Γ =>
              match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
              | Option.some Bool.true => return Nat.zero
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match Γ_1 with
            | List.cons τ' Γ => do
              let n ← aux_enum initSize size' Γ τ_1;
              return Nat.succ n
            | _ => OptionT.fail]
    fun size => aux_enum size size Γ_1 τ_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (x : Nat) => lookup Γ x τ)

/--
info: Try this enumerator: instance : EnumSizedSuchThat type (fun τ_1 => lookup Γ_1 x_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (x_1 : Nat) : OptionT Enumerator type :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => return τ
              | _ => OptionT.fail
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => return τ
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match x_1 with
            | Nat.succ n =>
              match Γ_1 with
              | List.cons τ' Γ => do
                let τ_1 ← aux_enum initSize size' Γ n;
                return τ_1
              | _ => OptionT.fail
            | _ => OptionT.fail]
    fun size => aux_enum size size Γ_1 x_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (τ : type) => lookup Γ x τ)

/--
info: Try this enumerator: instance : EnumSizedSuchThat type (fun τ_1 => typing Γ_1 e_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) : OptionT Enumerator type :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match e_1 with
            | term.Const n => return type.Nat
            | _ => OptionT.fail,
            match e_1 with
            | term.Var x => do
              let τ_1 ← EnumSizedSuchThat.enumSizedST (fun τ_1 => lookup Γ_1 x τ_1) initSize;
              return τ_1
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match e_1 with
            | term.Const n => return type.Nat
            | _ => OptionT.fail,
            match e_1 with
            | term.Var x => do
              let τ_1 ← EnumSizedSuchThat.enumSizedST (fun τ_1 => lookup Γ_1 x τ_1) initSize;
              return τ_1
            | _ => OptionT.fail,
            match e_1 with
            | term.Add e1 e2 =>
              match DecOpt.decOpt (typing Γ_1 e1 (type.Nat)) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (typing Γ_1 e2 (type.Nat)) initSize with
                | Option.some Bool.true => return type.Nat
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match e_1 with
            | term.Abs τ1 e => do
              let τ2 ← aux_enum initSize size' (List.cons τ1 Γ_1) e;
              return type.Fun τ1 τ2
            | _ => OptionT.fail,
            match e_1 with
            | term.App e1 e2 => do
              let τ1 ← aux_enum initSize size' Γ_1 e2;
              do
                let τ_1 ← Enum.enum;
                match DecOpt.decOpt (typing Γ_1 e1 (type.Fun τ1 τ_1)) initSize with
                  | Option.some Bool.true => return τ_1
                  | _ => OptionT.fail
            | _ => OptionT.fail]
    fun size => aux_enum size size Γ_1 e_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (τ : type) => typing Γ e τ)

/--
info: Try this enumerator: instance : EnumSizedSuchThat term (fun e_1 => typing Γ_1 e_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) : OptionT Enumerator term :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match τ_1 with
            | type.Nat => do
              let n ← Enum.enum;
              return term.Const n
            | _ => OptionT.fail,
            do
            let x ← EnumSizedSuchThat.enumSizedST (fun x => lookup Γ_1 x τ_1) initSize;
            return term.Var x]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match τ_1 with
            | type.Nat => do
              let n ← Enum.enum;
              return term.Const n
            | _ => OptionT.fail,
            do
            let x ← EnumSizedSuchThat.enumSizedST (fun x => lookup Γ_1 x τ_1) initSize;
            return term.Var x,
            match τ_1 with
            | type.Nat => do
              let e1 ← aux_enum initSize size' Γ_1 (type.Nat);
              do
                let e2 ← aux_enum initSize size' Γ_1 (type.Nat);
                return term.Add e1 e2
            | _ => OptionT.fail,
            match τ_1 with
            | type.Fun τ1 τ2 => do
              let e ← aux_enum initSize size' (List.cons τ1 Γ_1) τ2;
              return term.Abs τ1 e
            | _ => OptionT.fail,
            do
            let e2 ← Enum.enum;
            do
              let τ1 ← EnumSizedSuchThat.enumSizedST (fun τ1 => typing Γ_1 e2 τ1) initSize;
              do
                let e1 ← aux_enum initSize size' Γ_1 (type.Fun τ1 τ_1);
                return term.App e1 e2]
    fun size => aux_enum size size Γ_1 τ_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (e : term) => typing Γ e τ)
