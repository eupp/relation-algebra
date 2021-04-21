(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** kat: Kleene algebra with tests *)

(** We define here the class of Kleene algebra with tests, as a two
   sorted structure *)

Require Export kleene.
Set Implicit Arguments.

(** * KAT operations *)

(** A Kleene algebra with tests is composed of a Kleene algebra
   ([kar], i.e., [(X,dot,pls,one,zer,str)]), a Boolean algebra of
   tests ([tst], i.e., [(T,cap,cup,top,bot,neg)]), and an injection
   from tests to Kleene elements.

   Since we work with typed structures, the Kleene algebra is a
   category, and we actually have a family of Boolean algebras, for
   each square homset ([X n n]). *)
Class ops := mk_ops {
  kar: monoid.ops;
  tst: ob kar -> lattice.ops;
  inj: forall {n}, tst n -> kar n n
}.
Coercion kar: ops >-> monoid.ops.
(** we use [[p]] to denote the injection of the test [p] into the Kleene algebra *)
Notation " [ p ] " := (inj p): ra_terms. 

(* -- failed attempts to declare [inj] as a coercion -- *)
(* SubClass car' {X} n := @car (@tst X n). *)
(* SubClass car'' {X} n := @car (@mor (@kar X) n n). *)
(* Definition inj' X n: @car' X n -> @car'' X n := @inj X n. *)
(* Coercion inj' : car' >-> car''. *)
(* Print Coercion Paths car' car. *)
(* Goal forall `{X: ops} n m (a: X n m) (p: tst n) (q: tst m), p⋅a*q ≡ a. *)


(** * KAT laws  *)

(** The Kleene algebra should be a Kleene algebra (with bottom
   element), the Boolean algebras should be a Boolean lattice, and the
   injection should be a morphism of idempotent semirings, i.e, map 
   [(leq,weq,cap,cup,top,bot)] into [(leq,weq,dot,pls,one,zer)] *)

(* TOTHINK: voir si on laisse les deux instances :>, 
   qui ne sont utiles que dans l'abstrait si les structures 
   concrètes sont déclarées incrémentalement 
   voir aussi s'il ne vaut pas mieux poser ces deux instances en
   paramètres phantomes. 
   TODO: inliner [morphism]?
   TODO: relacher les contraintes sur les niveaux
*)
Class laws (l: level) (l': level) (X: ops) := {
  kar_laws:> monoid.laws l kar;
  tst_laws:> forall n, lattice.laws l' (tst n);

  mor_inj :  forall n, morphism (cross l l') (@inj X n);

  inj_top `{ONE ≪ l} `{TOP ≪ l'}: forall n, [top] ≡ one n;
  inj_cap `{DOT ≪ l} `{CAP ≪ l'}: forall n (p q: tst n), [p ⊓ q] ≡ [p] ⋅ [q]
}.

(** * Basic properties of KAT  *)

Section s.
Context {l l' : level} `{laws l l'}.
Variable n: ob X. 

Global Instance inj_leq: Proper (leq ==> leq) (@inj X n).
Proof. apply mor_inj. Qed.

Global Instance inj_weq: Proper (weq ==> weq) (@inj X n).
Proof. apply mor_inj. Qed.

Lemma inj_bot `{BOT ≪ l * l'}: [bot] ≡ zer n n.
Proof. now apply mor_inj. Qed.

Lemma inj_cup `{CUP ≪ l * l'} (p q: tst n): [p ⊔ q] ≡ [p] + [q].
Proof. now apply mor_inj. Qed.

Lemma str_inj `{DOT+ONE+STR ≪ l} `{TOP ≪ l'} (p: tst n): [p]^* ≡ 1.
Proof. 
  apply antisym; [|apply str_refl].
  rewrite leq_xt with (x:=p).
  now rewrite inj_top, str1.
Qed.

End s.


(** * dual KAT, for duality reasoning *)

Definition dual (X: ops) := {|
  kar := dual kar;
  tst := tst;
  inj := @inj X |}. 

Lemma dual_laws l l' X (L: laws l l' X): laws l l' (dual X).
Proof.
  constructor; try apply L.
  apply dual_laws, kar_laws. 
  intros. simpl in *. 
  rewrite capC. apply inj_cap. 
Qed.

Lemma dualize {l l'} {P: ops -> Prop} (L: forall X, laws l l' X -> P X) 
              {X} {H: laws l l' X}: P (dual X).
Proof. eapply L. apply dual_laws. exact H. Qed.

Ltac dual x := apply (dualize x).
