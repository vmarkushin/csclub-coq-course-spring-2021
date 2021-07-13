From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction and test it
_thoroughly_ using the command `Compute`. |*)

Definition orb (b c : bool) : bool := match (b, c) with
                                | (true, _) => true
                                | (_, true) => true
                                | _ => false
                                end.


Compute orb false false.
Compute orb true false.
Compute orb false true.
Eval cbv delta in orb true true.

Check false : bool.
Check false.
Check fun b => b.

(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition addb (b c : bool) : bool := match (b, c) with
                                 | (false, true) => true
                                 | (true, false) => true
                                 | _ => false
                                  end.

Definition addb' (b c : bool) : bool := match (b, c) with
                                  | (false, c) => c
                                  | (true, c) => negb c
                                  end.

Eval cbv delta in addb true false.
Eval cbv delta in addb' true false.

Eval cbv beta in addb true false.
Eval cbv beta in addb' true false.

Eval cbv iota in addb true false.
Eval cbv iota in addb' true false.

(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb (b c : bool) : bool := match (b, c) with
                                | (true, c) => c
                                | (false, c) => negb c
                                end.

Compute eqb (addb true false) true.
Compute eqb (addb false false) false.
Compute eqb (addb false true) true.
Compute eqb (addb true true) false.


(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.


(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

Definition dec2 (n : nat) : nat := match n with
                               | O | S O => O
                               | S (S n') => n'
                                end.

Compute dec2 O.
Compute dec2 (S O).
Compute dec2 (S (S O)).
Compute dec2 (S (S (S O))).


(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

Fixpoint subn (m n : nat) : nat := match (m, n) with
                               | (O, _) => O
                               | (m', O) => m'
                               | (S m', S n') => subn m' n'
                                end.

Compute subn (S O) O.
Compute subn (S O) (S O).
Compute subn (S (S O)) (S O).
Compute subn O (S O).

(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)


Fixpoint addn (m n : nat) : nat := match (m, n) with
                               | (O, n') => n'
                               | (S m', n') => S (addn m' n')
                                end.

Fixpoint muln (m n : nat) : nat := match (m, n) with
                               | (O, n') => O
                               | (S m', n') => addn n' (muln m' n')
                                end.


Compute muln (S (S O)) (S (S (S (S O)))).

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Fixpoint eqn (m n : nat) : bool := match (m, n) with
                              | (O, O) => true
                              | (S m', S n') => eqn m' n'
                              | _ => false
                              end.


Compute eqn O O.
Compute eqn (S O) O.
Compute eqn O (S O).
Compute eqn (S O) (S O).

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` returns `true` if and only if `m` is less
than or equal to `n`. Your solution must not use recursion but you may reuse any
of the functions you defined in this module so far. *)

Definition leq (m n : nat) : bool := eqn O (subn m n).

Compute leq O O.
Compute leq (S O) O.
Compute leq O (S O).
Compute leq (S O) (S O).


(*| ---------------------------------------------------------------------------- |*)


(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)
Require Import Recdef.


Fixpoint divn' (m n : nat) : nat :=
  match (m, n) with
  | (S m', S n') => divn' m' n'
  | (O, _) => O
  | (m', O) => m'
  end
with divn (m n : nat) :=
  match (m, n) with
  | (_, O) => O
  | (O, _) => O
  | (S _, _) =>
    let m' := (divn' m n) in
    match eqn m' O with
    | true => O
    | false => S (divn m' n)
    end
  end.

End My.
