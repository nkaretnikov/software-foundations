(** * More Logic *)

Require Export "Prop".

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** *** *)
(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** *** *)
(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 


(** Here is another example of how to work with existentials. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* WORKED IN CLASS *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean?

There exists a natural number [n] whose successor is [beautiful].

*)
Theorem exists_succ : ex nat (fun n => beautiful (S n)).
Proof.
  exists 2.
  apply b_3.
Qed.

(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  intros.
  unfold "~".
  intros.
  inversion H0 as [x' Hx'].
  apply Hx'.
  apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros.
  unfold excluded_middle in H.
  unfold "~" in H0.
  unfold "~" in H.
  destruct (H (P x)).           (* destruct P x in the context of LEM *)
  Case "left".
    apply H1.
  Case "right".
    (* Get rid of 'exists' by moving the hypothesis to the goal. *)
    apply ex_falso_quodlibet.
    apply H0.
    exists x.
    apply H1.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  unfold "<->".
  intros.
  split.
  Case "left".
    intros.
    inversion H as [x Hx].
    inversion Hx as [PxH|QxH].
    SCase "left: P x".
      left.
      exists x.
      apply PxH.
    SCase "right: Q x".
      right.
      exists x.
      apply QxH.
  Case "right".
    intros.
    inversion H as [ExPx|ExQx].
    SCase "left: P x".
      inversion ExPx as [x PxH].
      exists x.
      left.
      apply PxH.
    SCase "right: Q x".
      inversion ExQx as [x QxH].
      exists x.
      right.
      apply QxH.
Qed.
(** [] *)

(* ###################################################### *)
(** * Evidence-carrying booleans. *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 
*)

(** *** *)
(** 
It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 

(** *** *)

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 
  
(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)
*) 

(** *** *)
(** 
Here's a simple example illustrating the advantages of the [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)


(** **** Exercise: 1 star (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros.
  unfold override'.
  destruct (eq_nat_dec k1 k2).
  Case "k1 = k2".
    reflexivity.
  Case "k1 <> k2".
    reflexivity.
Qed.
(** [] *)






(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_nil : all X P []
  | all_cons : forall (x : X) (xs : list X),
                 P x -> all X P xs -> all X P (x :: xs).

(* The cons constructor is defined differently, but the definitions
are equivalent. *)
Inductive all_and (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_and_nil : all_and X P []
  | all_and_cons : forall (x : X) (xs : list X),
                     P x /\ all_and X P xs -> all_and X P (x :: xs).

Theorem all__all_and : forall (X : Type) (P : X -> Prop) (xs : list X),
                         all X P xs -> all_and X P xs.
Proof.
  intros.
  induction xs as [|y ys].
  Case "xs = []".
    apply all_and_nil.
  Case "xs = y::ys".
    apply all_and_cons.
    inversion H.
    split.
    SCase "left".
      apply H2.
    SCase "right".
      apply IHys. apply H3.
Qed.

Theorem all_and__all : forall (X : Type) (P : X -> Prop) (xs : list X),
                         all_and X P xs -> all X P xs.
Proof.
  intros.
  induction xs as [|y ys].
  Case "xs = []".
    apply all_nil.
  Case "xs = y::ys".
    inversion H.
    inversion H1.
    apply all_cons.
    apply H3.
    apply IHys.
    apply H4.
Qed.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_holds :
  forall X (test : X -> bool) (xs : list X),
    forallb test xs = true <-> all X (fun x => test x = true) xs.
Proof.
  intros.
  unfold "<->".
  split.
  Case "left".
    intros.
    induction xs as [|y ys].
    SCase "xs = []".
      apply all_nil.
    SCase "xs = y::ys".
      apply all_cons.
      SSCase "P x".
        simpl in H.
        destruct (test y).
        SSSCase "true".
          reflexivity.
        SSSCase "false".
          inversion H.
      SSCase "all X P xs".
        apply IHys.
        simpl in H.
        destruct (test y).
        SSSCase "true".
          simpl in H. apply H.
        SSSCase "false".
          inversion H.
  Case "right".
    intros.
    induction H as [|y ys].
    SCase "xs = []".
      reflexivity.
    SCase "xs = y::ys".
      simpl.
      rewrite H.
      simpl.
      apply IHall.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

Inductive in_order_merge {X : Type} : (list X) -> (list X) -> (list X) -> Prop :=
  | iom_nil : forall (xs : list X),
                in_order_merge [] xs xs
  | iom_seq_l : forall (x : X) (xs ys zs : list X),
                  in_order_merge xs ys zs -> in_order_merge (x::xs) ys (x::zs)
  | iom_seq_r : forall (y : X) (xs ys zs : list X),
                  in_order_merge xs ys zs -> in_order_merge xs (y::ys) (y::zs).

Example in_order_merge_2__0_1__0_1_2 :
  in_order_merge [2] [0;1] [0;1;2].
Proof.
  apply iom_seq_r.
  apply iom_seq_r.
  apply iom_seq_l.
  apply iom_nil.
Qed.

Example in_order_merge_1_6_2__4_3 :
  in_order_merge [1;6;2] [4;3] [1;4;6;2;3].
Proof.
  apply iom_seq_l.
  apply iom_seq_r.
  apply iom_seq_l.
  apply iom_seq_l.
  apply iom_nil.
Qed.

Example not_in_order_merge_1_6_2__4_3 :
  not (in_order_merge [1;6;2] [4;3] [1;4;2;6;3]).
Proof.
  unfold "~".
  intros.
  inversion H.
  inversion H3.
  inversion H7.
Qed.

Theorem iom_nil_r : forall {X : Type} (xs : list X),
                      in_order_merge xs [] xs.
Proof.
  intros.
  induction xs as [|y ys].
  Case "xs = []".
    apply iom_nil.
  Case "xs = y::ys".
    apply iom_seq_l. apply IHys.
Qed.

Theorem not_iom_nil : forall {X : Type} (xs ys : list X),
                        xs <> [] ->
                        ys <> [] ->
                        not (in_order_merge xs ys []).
Proof.
  destruct xs as [|z zs].
  Case "xs = []".
    unfold "~".
    intros.
    apply H.
    reflexivity.
  Case "xs = z::zs".
    unfold "~".
    intros.
    inversion H1.
Qed.

Theorem iom_symmetry : forall (X : Type) (xs ys zs : list X),
                         in_order_merge xs ys zs <-> in_order_merge ys xs zs.
Proof.
  unfold "<->".
  split.
  Case "left".
    intros.
    induction H.
    SCase "iom_nil".
      apply iom_nil_r.
    SCase "iom_seq_l".
      apply iom_seq_r.
      apply IHin_order_merge.
    SCase "iom_seq_r".
      apply iom_seq_l.
      apply IHin_order_merge.
  Case "right".
    intros.
    induction H.
    SCase "iom_nil".
      apply iom_nil_r.
    SCase "iom_seq_l".
      apply iom_seq_r.
      apply IHin_order_merge.
    SCase "iom_seq_r".
      apply iom_seq_l.
      apply IHin_order_merge.
Qed.

(* https://coq.inria.fr/distrib/current/refman/Reference-Manual022.html *)
Class Eq (A : Type) := {
  eqb : A -> A -> bool ;
  eqb_leibniz : forall x y, eqb x y = true -> x = y ;
  leibniz_eqb : forall x y, x = y -> eqb x y = true }.

Instance Eq_nat : Eq nat :=
  { eqb x y := beq_nat x y }.
(* eqb_leibniz *)
  intros. apply beq_nat_true. apply H.
(* leibniz_eqb *)
  induction x as [|x'].
    intros.
    rewrite <- H. reflexivity.
    intros. destruct y as [|y'].
      inversion H.
      simpl. apply IHx'. inversion H. reflexivity.
Defined.

Fixpoint beq_list {X : Type} {eq : Eq X} (xs ys : list X) : bool :=
  match (xs, ys) with
    | ([]   , []   ) => true
    | ([]   , _::_ ) => false
    | (_::_ , []   ) => false
    | (x::xt, y::yt) =>
      if eqb x y
      then beq_list xt yt
      else false
  end.

Instance Eq_list {X : Type} {eq : Eq X} : Eq (list X) :=
  { eqb xs ys := beq_list xs ys }.
Proof.
(* eqb_leibniz *)
  induction x as [|n ns].
  Case "x = []".
    intros.
    destruct y as [|m ms].
    SCase "y = []".
      reflexivity.
    SCase "y = m::ms".
      inversion H.
  Case "x = n::ns".
    destruct y as [|m ms].
    SCase "y = []".
      intros.
      inversion H.
    SCase "y = m::ms".
      intros.
      inversion H.
      destruct (eqb n m) eqn:Heqb.
      Focus 2.
      SSCase "false".
        inversion H1.
      SSCase "true".
        apply eqb_leibniz in Heqb.
        rewrite Heqb.
        apply IHns in H1.
        rewrite H1.
        reflexivity.
(* leibniz_eqb *)
  induction x as [|x xt].
    intros. rewrite <- H. reflexivity.
    intros. simpl. destruct y as [|y yt].
      inversion H.
      destruct (eqb x y) eqn:eqb_x_y.
        apply IHxt. inversion H. reflexivity.
        inversion H. inversion eqb_x_y.
        apply leibniz_eqb in H1. rewrite H1 in H3. inversion H3.
Defined.

Fixpoint elem {X : Type} {eq : Eq X} (x : X) (xs : list X) : bool :=
  match xs with
    | []    => false
    | y::ys => if eqb x y
               then true
               else elem x ys
  end.

Theorem elem_nil_false : forall {X : Type} {eq : Eq X} (x : X),
                           elem x [] = false.
Proof. reflexivity. Qed.

Theorem elem_x_y__elem_x_y_ys :
  forall {X : Type} {eq : Eq X} (x y : X) (ys : list X),
    elem x [y]     = true ->
    elem x (y::ys) = true.
Proof.
  intros.
  unfold elem in H.
  destruct (eqb x y) eqn:Heqb_x_y.
  Case "true".
    simpl. rewrite Heqb_x_y. reflexivity.
  Case "false".
    inversion H.
Qed.

(* XXX: Prove. *)
Theorem iom_elem : forall {X : Type} {eq : Eq X} (x : X) (l l1 l2 : list X),
                     in_order_merge l1 l2 l ->
                     elem x l = true ->
                     elem x l1 = true \/ elem x l2 = true.
Proof.
Abort.

Fixpoint is_in_order_merge {X : Type} {eq_x : Eq X} {eq_list : Eq (list X)}
                           (l1 l2 l : list X) : bool :=
  match (l1, l2, l) with
    | ([], l2, l)
      => if eqb l2 l then true else false
    | ((x::xs), (y::ys), (zy::zx::zs))
      => andb (andb (eqb x zx) (eqb y zy))
              (is_in_order_merge xs ys zs)
    | ((x::xs), ys, (z::zs))
      => andb (eqb x z) (is_in_order_merge xs ys zs)
    | (_ :: _, [], [])
      => false
    | (_ :: _, _ :: _, [])
      => false
  end.

Theorem eqb_refl : forall {X : Type} {eq_x : Eq X} (x : X), eqb x x = true.
Proof.
  intros. apply leibniz_eqb. reflexivity.
Qed.

Theorem eqb_uncons : forall {X : Type} {eq_x : Eq X} {eq_list : Eq (list X)}
                            (x : X) (xs ys : list X) (b : bool),
                       eqb (x :: xs) (x :: ys) = b ->
                       eqb xs ys = b.
Proof.
  intros.
  destruct (eqb xs ys) eqn:Heqb_xs_ys.
  Case "eqb xs ys = true".
    destruct b.
    SCase "b = true".
      reflexivity.
    SCase "b = false".
      apply eqb_leibniz in Heqb_xs_ys.
      rewrite <- Heqb_xs_ys in H.
      assert (Hcontra: eqb (x :: xs) (x :: xs) = true). apply eqb_refl.
      rewrite Hcontra in H.
      inversion H.
  Case "eqb xs ys = false".
    destruct b.
    SCase "b = true".
      apply eqb_leibniz in H.
      inversion H.
      rewrite <- H1 in Heqb_xs_ys.
      assert (Hcontra: eqb xs xs = true). apply eqb_refl.
      rewrite Hcontra in Heqb_xs_ys.
      inversion Heqb_xs_ys.
    SCase "b = false".
      reflexivity.
Qed.

(* XXX: Prove these. *)
Theorem iom__is_iom :
  forall {X : Type} {eq_x : Eq X} {eq_list : Eq (list X)} (l1 l2 l : list X),
    in_order_merge l1 l2 l -> is_in_order_merge l1 l2 l = true.
Proof.
Abort.

Theorem is_iom__iom :
  forall {X : Type} {eq_x : Eq X} {eq_list : Eq (list X)} (l1 l2 l : list X),
    is_in_order_merge l1 l2 l = true -> in_order_merge l1 l2 l.
Proof.
Abort.

Theorem iom_filter : forall {X : Type} (test : X -> bool) (l l1 l2: list X),
                       in_order_merge l1 l2 l ->
                       filter test l1 = l1    ->
                       filter test l2 = []    ->
                       filter test l = l1.
Proof.
Abort.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

(* FILL IN HERE *)

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

(* FILL IN HERE *)
(** [] *)


(** **** Exercise: 3 stars (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
 (* FILL IN HERE *)
.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* FILL IN HERE *) Admitted.
(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  (* FILL IN HERE *) Admitted.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* FILL IN HERE *)


(* $Date: 2014-02-22 09:43:41 -0500 (Sat, 22 Feb 2014) $ *)
