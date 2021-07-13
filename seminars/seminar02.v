Section PropositionalLogic.

Variables A B C : Prop.

Definition anb1 :
  A /\ B -> A
:= fun '(conj a b) => a.

Definition impl_trans :
  (A -> B) -> (B -> C) -> A -> C
:= fun f g x => g (f x).

Definition HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C
:= fun abc ab a => (abc a (ab a)).

Definition DNE_triple_neg :
  (* (((A -> False) -> False) -> False) -> A -> False *)
  ~ (~ (~ A)) -> ~ A
:= fun x a => x (fun a_f => a_f a).

Print or.

Definition or_comm :
  A \/ B -> B \/ A
  := fun coprod => match coprod with
                | or_introl a => or_intror a
                | or_intror a => or_introl a
                end.

End PropositionalLogic.



Section Quantifiers.

Variable T : Type.
Variable A : Prop.
Variable P Q : T -> Prop.

Print "<->".

Definition forall_conj_comm :
  (forall x, P x /\ Q x) <-> (forall x, Q x /\ P x)
  := conj
       (fun all_pq x => match all_pq x with
                     | conj px qx => conj qx px
       end)
       (fun all_qp x => match all_qp x with
                     | conj qx px => conj px qx
       end).

Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
  := conj
       (fun any_pq x => match any_pq x with
                     | or_introl px => or_intror px
                     | or_intror qx => or_introl qx
                     end
       )
       (fun any_qp x => match any_qp x with
                     | or_introl qx => or_intror qx
                     | or_intror px => or_introl px
                     end
       ).

Print ex_intro.
Definition not_exists_forall_not :
  ((exists x, P x) -> False) -> forall x, ~P x
  := fun not_ex x px => not_ex (ex_intro P x px).

Definition exists_forall_not :
  (exists x, A -> P x) -> (forall x, ~P x) -> ~A :=
  fun '(ex_intro _ x px) n a => n x (px a).

(** Extra exercise (feel free to skip): the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

Definition contra : forall (A : Prop), False -> A := fun a f => match f with end.

Definition or_absurd : forall (A B : Prop), A \/ B -> ~ A -> B :=
fun a b p_or_q na => match p_or_q with
           | or_introl aa => contra _ (na aa)
           | or_intror bb => bb
            end.

Check I : (True : Type).
(*
Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2
  :=
  conj (fun lem => (fun ty Pprop Qprop =>
                      conj
                        (fun all_x_q_or_px => match lem Qprop with
                                        | or_introl a => or_introl a
                                        | or_intror b => or_intror (fun x => or_absurd _ _ (all_x_q_or_px _) b)
                                        end
                        )
                        (fun q_or_all_x_px => (fun X => match q_or_all_x_px with
                                               | or_introl a => or_introl a
                                               | or_intror b => or_intror (b _)                      end))
                   )
          )
       (fun frob => (fun Pprop =>
                    let frob_ap := frob (True:Type) (fun _ => False) Pprop
                    in
                    match frob_ap with
                 | conj all_x_q_or_p q_or_all_x_px => let p := all_x_q_or_p _ in _
       end))
.
*)

End Quantifiers.



Section Equality.

(** exercise: *)
Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
:= fun '(eq_refl _ ) => eq_refl _.

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:= fun '(eq_refl _ ) '(eq_refl _) => eq_refl _.

(** extra exercise *)
(*
Definition congId A {x y : A} (p : x = y) :
  f_congr (fun x => x) p = p :=

(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:=
 *)

End Equality.



Section ExtensionalEqualityAndComposition.

Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

About "\o".
(* Unset Printing Notations. *)

Variables f : A -> B.
Variables g : B -> C.
Variables h : C -> D.


Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
  := erefl.
(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)

Print "=1".
Print eq.
Print eq_refl.
About eqType.
Check erefl _ : 0 = 0.

(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f => fun x => let b := (f x) in erefl.

(** Exercise: Symmetry *)
Definition eqext_sym : forall (f g : A -> B), f =1 g -> g =1 f
 := fun f g feg => fun x => let p := (feg x) in match p in (_ = gx) return (gx = f x) with
                   | erefl => erefl _
                    end.

(** Exercise: Transitivity *)

Definition eqext_trans :
   forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
   := fun f g h feg geh x => match geh x in (_ = hx) return (f x = hx) with
                           | erefl => feg x
                               end
                              .


(** Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
  := fun f g h feg => fun x => match (feg x) in (_ = gx) return (((h \o f) x) = (h gx)) with
                        | erefl => erefl _
                        end.

(** Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
  := fun f g h feg x => match (feg (h x)) in (_ = gx) return (f (h x) = gx) with
                  | erefl => erefl _
                  end.

End ExtensionalEqualityAndComposition.



(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
  := fun a b => match a with
          | true => match b with
                | true => erefl _
                | false => erefl _
                   end

          | false => match b with
                 | true => erefl _
                 | false => erefl _
                    end
          end.

Variables A B : Type.

Definition eqSym : A = B -> B = A := fun 'erefl => erefl.


Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
  := fun b => if b return ~~ ~~ b = true -> b = true then id else id.
