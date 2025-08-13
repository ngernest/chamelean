
import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer

set_option guard_msgs.diff true

mutual
  inductive Even : Nat → Prop where
    | zero_is_even : Even .zero
    | succ_of_odd_is_even : ∀ n : Nat, Odd n → Even (.succ n)

  inductive Odd : Nat → Prop where
    | succ_of_even_is_odd : ∀ n : Nat, Even n → Odd (.succ n)
end

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun n_1 => Odd n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Even n) initSize;
              return Nat.succ n)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Even n) initSize;
              return Nat.succ n),
            ]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : Nat) => Odd n)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun n_1 => Even n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, return Nat.zero),
            (1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Odd n) initSize;
              return Nat.succ n)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return Nat.zero),
            (1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Odd n) initSize;
              return Nat.succ n),
            ]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : Nat) => Even n)
