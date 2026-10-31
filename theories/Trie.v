From Coq Require Import Bool PeanoNat PArith OrdersEx OrdersLists.
From Coq Require List.
From MMaps Require Import Utils Interface Comparisons.

(** * Extensional binary tries based on a canonical representation *)

(* Adapted from <https://www.cs.princeton.edu/~appel/papers/ptree.pdf> *)

(* Authors: Andrew W. Appel, Princeton University,
            Xavier Leroy, Collège de France and Inria.
            Andres Erbsen
   Copyright: Andrew W. Appel and Inria and Andres Erbsen.
   Original code licensed under BSD-3-Clause. *)

Definition option_bind {A B} (f : A -> option B) (o : option A) : option B :=
  match o with None => None | Some a => f a end.

(** Nonempty branches. Each constructor is of the form [NodeXYZ], where the
   bit [X] says whether there is a left subtree, [Y] whether there is a value
   at this node, and [Z] whether there is a right subtree. No [Node000] here! *)
Inductive branch (A : Type) : Type :=
| Node001:                  branch A -> branch A
| Node010:             A ->             branch A
| Node011:             A -> branch A -> branch A
| Node100: branch A ->                  branch A
| Node101: branch A ->      branch A -> branch A
| Node110: branch A -> A ->             branch A
| Node111: branch A -> A -> branch A -> branch A.
Arguments Node001 {A}. Arguments Node010 {A}. Arguments Node011 {A}.
Arguments Node100 {A}. Arguments Node101 {A}. Arguments Node110 {A}.
Arguments Node111 {A}.

Definition trie A := option (branch A).
Definition empty A : trie A := None.

(** Smart constructors and eliminators *)

Definition Node {A} (l : trie A) (o : option A) (r : trie A) : trie A :=
  match l,o,r with
  | None,    None,   None    => None
  | None,    None,   Some r' => Some (Node001 r')
  | None,    Some x, None    => Some (Node010 x)
  | None,    Some x, Some r' => Some (Node011 x r')
  | Some l', None,   None    => Some (Node100 l')
  | Some l', None,   Some r' => Some (Node101 l' r')
  | Some l', Some x, None    => Some (Node110 l' x)
  | Some l', Some x, Some r' => Some (Node111 l' x r')
  end.

Definition isBranch {A} (l : trie A) (o : option A) (r : trie A) :=
  match l, o, r with None, None, None => False | _, _, _ => True end.

Definition branch_case {A} (P : trie A -> Type) (f : forall l o r, isBranch l o r -> P (Node l o r)) (m : branch A) : P (Some m) :=
  match m with
  | Node001     r => f None     None     (Some r) I
  | Node010   x   => f None     (Some x) None     I
  | Node011   x r => f None     (Some x) (Some r) I
  | Node100 l     => f (Some l) None     None     I
  | Node101 l   r => f (Some l) None     (Some r) I
  | Node110 l x   => f (Some l) (Some x) None     I
  | Node111 l x r => f (Some l) (Some x) (Some r) I
  end.

Definition branch_map {A B} f : branch A -> B :=
  branch_case (fun _ => B) (fun l o r _ => f l o r).

Section Induction.
Context {A : Type} (P : trie A -> Type)
        (empty : P None)
        (node : forall l, P l -> forall o r, P r -> isBranch l o r -> P (Node l o r)).

Fixpoint trie_branch_ind' (m : branch A) : P (Some m) :=
  branch_case P ltac:(intros [] [] [] ?; apply node; auto) m.
Definition trie_branch_ind := Eval cbv [trie_branch_ind' branch_case] in trie_branch_ind'.

Definition trie_ind : forall m, P m := option_rect P trie_branch_ind empty.
End Induction.

Local Fixpoint get' {A} (p : positive) (m : branch A) : option A :=
  match p, m with
  | xH,   (Node010 x|Node011 x _|Node110 _ x|Node111 _ x _) => Some x
  | xO q, (Node100 m|Node101 m _|Node110 m _|Node111 m _ _) => get' q m
  | xI q, (Node001 m|Node011 _ m|Node101 _ m|Node111 _ _ m) => get' q m
  | _,_ => None
  end.

Definition get {A} p : trie A -> option A := option_bind (get' p).

Lemma get_empty {A} i : get i (empty A) = None.
Proof. trivial. Qed.

Lemma get_Node {A} i l (x : option A) r :
  get i (Node l x r) = match i with xI j => get j r | xO j => get j l | _ => x end.
Proof. case l, x, r; case i; trivial. Qed.

(** ** Extensionality property *)

Local Lemma get'_not_None {A} m : exists i, @get' A i m <> None.
Proof.
  induction m; try case IHm as [p H]; try case IHm1 as [p H];
    try ((exists xH + exists (xI p) + exists (xO p)); cbn; congruence).
Qed.

Lemma extensionality_empty {A} (m : trie A) (H : forall i, get i m = None) : m = None.
Proof. case m as [m|]; auto. case (get'_not_None m) as [i []]. apply H. Qed.

Lemma extensionality {A} : forall m1 m2, (forall i, @get A i m1 = get i m2) -> m1 = m2.
Proof.
  induction m1 using trie_ind; induction m2 using trie_ind; intros;
    eauto using eq_sym, extensionality_empty.
  f_equal; [apply IHm1_1| |apply IHm1_2]; try intros i;
    [>specialize (H1 (xO i)) | specialize (H1 xH) | specialize (H1 (xI i))];
    rewrite ?get_Node in H1; auto.
Qed.

(** Setters *)

Fixpoint singleton {A} (p : positive) (x : A) : branch A :=
  match p with
  | xH => Node010 x
  | xO q => Node100 (singleton q x)
  | xI q => Node001 (singleton q x)
  end.

Local Fixpoint set' {A} (p : positive) (x : A) (m : branch A) : branch A :=
  match p, m with
  | xH, Node001 r => Node011 x r
  | xH, Node010 _ => Node010 x
  | xH, Node011 _ r => Node011 x r
  | xH, Node100 l => Node110 l x
  | xH, Node101 l r => Node111 l x r
  | xH, Node110 l _ => Node110 l x
  | xH, Node111 l _ r => Node111 l x r
  | xO q, Node001 r => Node101 (singleton q x) r
  | xO q, Node010 y => Node110 (singleton q x) y
  | xO q, Node011 y r => Node111 (singleton q x) y r
  | xO q, Node100 l => Node100 (set' q x l)
  | xO q, Node101 l r => Node101 (set' q x l) r
  | xO q, Node110 l y => Node110 (set' q x l) y
  | xO q, Node111 l y r => Node111 (set' q x l) y r
  | xI q, Node001 r => Node001 (set' q x r)
  | xI q, Node010 y => Node011 y (singleton q x)
  | xI q, Node011 y r => Node011 y (set' q x r)
  | xI q, Node100 l => Node101 l (singleton q x)
  | xI q, Node101 l r => Node101 l (set' q x r)
  | xI q, Node110 l y => Node111 l y (singleton q x)
  | xI q, Node111 l y r => Node111 l y (set' q x r)
  end.

Definition set {A} (p : positive) (x : A) (m : trie A) : trie A :=
  Some match m with Some m' => set' p x m' | None => singleton p x end.

Lemma set_Node {A} (v : A) l o r p :
  set p v (Node l o r) =
    match p with
    | xH => Node l (Some v) r
    | xO q => Node (set q v l) o r
    | xI q => Node l o (set q v r)
    end.
Proof. case l, o, r, p; trivial. Qed.

Lemma set_None {A} x p : @set A p x None = set p x (Node None None None).
Proof. trivial. Qed.

Lemma get_set_same {A} : forall i x (m : trie A), get i (set i x m) = Some x.
Proof.
  induction i; induction m using trie_ind; intros;
    rewrite ?set_None, ?set_Node, ?get_Node; auto.
Qed.

Lemma get_set_diff {A} : forall i j x (m : trie A),
  i <> j -> get i (set j x m) = get i m.
Proof.
  induction i, j; induction m using trie_ind; intros;
    rewrite ?set_None, ?set_Node, ?get_Node; auto;
    try (apply IHi); congruence.
Qed.

Local Fixpoint remove'' {A} (p : positive) (m : branch A) : trie A :=
  match p with
  | xH => branch_map (fun l o r => Node l None r) m
  | xO p => branch_map (fun l o r => Node (option_bind (remove'' p) l) o r) m
  | xI p => branch_map (fun l o r => Node l o (option_bind (remove'' p) r)) m
  end.
Local Definition remove' {A} := Eval cbv [remove'' branch_map branch_case option_bind Node ] in @remove'' A.

Definition remove {A} (p : positive) : trie A -> trie A := option_bind (remove' p).

Lemma remove_Node {A} l o r p :
  @remove A p (Node l o r) =
    match p with
    | xH => Node l None r
    | xO q => Node (remove q l) o r
    | xI q => Node l o (remove q r)
    end.
Proof. case l, o, r, p; trivial. Qed.

Lemma get_remove_same {A} i (m: trie A) : get i (remove i m) = None.
Proof.
  revert i; induction m using trie_ind; case i as [];
    rewrite ?remove_Node, ?IHm1, ?IHm2, ?get_Node; trivial.
Qed.

Lemma get_remove_diff {A} i j (m : trie A) :
  i <> j -> get i (remove j m) = get i m.
Proof.
  revert i j; induction m using trie_ind; trivial; case i as [], j as []; intros;
    rewrite ?remove_Node, ?get_Node; try (apply IHm1||apply IHm2); try congruence.
Qed.

(** Bulk operations *)

Section MapFilter.
Context {A B : Type} (f : A -> option B).
Let Fixpoint map_filter'' (m : branch A) : trie B := branch_map (fun l o r =>
  Node (option_bind map_filter'' l) (option_bind f o) (option_bind map_filter'' r)) m.

Local Definition map_filter' :=
  Eval cbv [map_filter'' branch_map branch_case option_bind Node] in map_filter''.

Definition map_filter : trie A -> trie B := option_bind map_filter'.

Lemma map_filter_Node l o r :
  map_filter (Node l o r) = Node (map_filter l) (option_bind f o) (map_filter r).
Proof. case l, o, r; trivial. Qed.

Lemma get_map_filter m : forall i, get i (map_filter m) = option_bind f (get i m).
Proof.
  induction m using trie_ind; case i as [];
    rewrite ?map_filter_Node, ?get_Node, ?IHm1, ?IHm2; trivial.
Qed.
End MapFilter.

Section Combine.
Context {A B C : Type} (f : option A -> option B -> option C).

Local Notation combine'_l m := (map_filter (fun a => f (Some a) None) (Some m)).
Local Notation combine'_r m := (map_filter (fun b => f None (Some b)) (Some m)).

Let Fixpoint combine'' (m1 : branch A) (m2 : branch B) {struct m1} : trie C.
Proof. (* 49 cases *)
  case m1 as [ r1 | x1 | x1 r1 | l1 | l1 r1 | l1 x1 | l1 x1 r1 ];
  case m2 as [ r2 | x2 | x2 r2 | l2 | l2 r2 | l2 x2 | l2 x2 r2 ]; (apply Node;
   [ try (exact (combine'' l1 l2) || exact (combine'_l l1) || exact (combine'_r l2))
   | apply f; [ try exact (Some x1) | try exact (Some x2) ]
   | try (exact (combine'' r1 r2) || exact (combine'_l r1) || exact (combine'_r r2))
   ]; exact None).
Defined.
Local Definition combine' := Eval cbv [combine'' Node map_filter option_bind] in combine''.

Definition combine (m1 : trie A) (m2 : trie B) : trie C :=
  match m1, m2 with
  | None, None => None
  | None, Some m2 => combine'_r m2
  | Some m1, None => combine'_l m1
  | Some m1, Some m2 => combine' m1 m2
  end.

Context (f_None_None : f None None = None).

Lemma combine_Node_Node l1 o1 r1 l2 o2 r2 :
  combine (Node l1 o1 r1) (Node l2 o2 r2) = Node (combine l1 l2) (f o1 o2) (combine r1 r2).
Proof. case l1, o1, r1, l2, o2, r2; trivial; rewrite ?f_None_None; trivial. Qed.

Lemma get_combine : forall m1 m2 i, get i (combine m1 m2) = f (get i m1) (get i m2).
Proof.
  induction m1 using trie_ind; induction m2 using trie_ind; auto; case i as [];
  repeat (change (combine None) with (combine (Node None None None))
       || change (combine ?x None) with (combine x (Node None None None)));
  rewrite ?combine_Node_Node, ?get_Node, ?IHm2_1, ?IHm2_2, ?IHm1_1, ?IHm1_2; auto.
Qed.
End Combine.

Local Set Implicit Arguments.
Local Unset Strict Implicit.
Local Open Scope lazy_bool_scope.

(** * The [MMaps] instance *)

(** The functions below that need the key of each binding ([bindings],
    [fold], [mapi], [merge], ...) carry the current path in the trie
    as an extra [positive] argument, in reverse order, as in
    [MMaps.Positive]. *)

Module TrieMap <: S PositiveOrderedTypeBits.

  Module E := PositiveOrderedTypeBits.
  Module ME := KeyOrderedType E.

  Definition key := positive : Type.

  Definition eq_key {A} := @ME.eqk A.
  Definition eq_key_elt {A} := @ME.eqke A.
  Definition lt_key {A} := @ME.ltk A.

  #[export] Instance eqk_equiv {A} : Equivalence (@eq_key A) := _.
  #[export] Instance eqke_equiv {A} : Equivalence (@eq_key_elt A) := _.
  #[export] Instance ltk_strorder {A} : StrictOrder (@lt_key A) := _.

  (** Reverses the positive [y] and concatenate it with [x] *)

  Fixpoint rev_append (y x : positive) : positive :=
    match y with
    | xH => x
    | xI y => rev_append y (xI x)
    | xO y => rev_append y (xO x)
    end.
  Local Infix "@" := rev_append (at level 60).
  Definition rev x := x@xH.

  Definition t := trie.

  Definition empty {A} : t A := empty A.

  Section A.
  Variable A:Type.

  Definition is_empty (m : trie A) := match m with None => true | _ => false end.

  Definition find (i : key) (m : t A) : option A := get i m.

  Definition mem (i : key) (m : t A) : bool := match get i m with Some _ => true | _ => false end.

  Definition add (i : key) (v : A) (m : t A) : t A := set i v m.

  Definition singleton x e := add x e None.

  Definition remove (i : key) (m : t A) : t A := remove i m.

  (** [bindings]. As in [MMaps.Positive], the recursive functions below
      carry the current path [i] in reverse order, and [branch_map] avoids
      spelling out the seven constructors of [branch]. *)

  Fixpoint xbindings' (m : branch A) (i : positive) (acc : list (key*A))
    {struct m} : list (key*A) :=
    branch_map (fun l o r =>
      let acc := match r with Some r => xbindings' r (xI i) acc | None => acc end in
      let acc := match o with Some e => (rev i, e) :: acc | None => acc end in
      match l with Some l => xbindings' l (xO i) acc | None => acc end) m.

  Definition xbindings (m : t A) (i : positive) (acc : list (key*A)) :=
    match m with Some m => xbindings' m i acc | None => acc end.

  Definition bindings (m : t A) := xbindings m xH nil.

  (** [cardinal] *)

  Definition cardinal : t A -> nat :=
    trie_ind (fun _ => nat) O (fun _ x o _ y _ => x+(match o with Some a => 1|_=> O end)+y).

  (** Specification proofs *)

  Definition MapsTo (i:key)(v:A)(m:t A) := get i m = Some v.

  Definition In (i:key)(m:t A) := exists v, get i m = Some v.

  Lemma MapsTo_compat : Proper (E.eq ==> eq ==> eq ==> iff) MapsTo.
  Proof.
   intros k k' Hk e e' He m m' Hm. red in Hk. now subst.
  Qed.

  Lemma find_spec m x e : find x m = Some e <-> MapsTo x e m.
  Proof. reflexivity. Qed.

  Lemma mem_find :
    forall m x, mem x m = match find x m with None => false | _ => true end.
  Proof.
   induction m; destruct x; simpl; auto.
  Qed.

  Lemma mem_spec : forall m x, mem x m = true <-> In x m.
  Proof.
   intros m x; split.
   - cbv [mem In]. case get eqn:?; eauto; discriminate.
   - cbv [mem In]; intros [v H].
     rewrite H. trivial.
  Qed.

  Theorem empty_spec: forall (i: key), find i empty = None.
  Proof. reflexivity. Qed.

  Lemma is_empty_spec m : is_empty m = true <-> forall k, find k m = None.
  Proof.
   split.
   - case m; simpl; intros b H; [discriminate|reflexivity].
   - intros H. erewrite (extensionality_empty m); trivial.
  Qed.

  Lemma is_empty_Node l o r : isBranch l o r -> is_empty (Node l o r) = false.
  Proof. case l, o, r; simpl; tauto. Qed.

  Theorem add_spec1: forall (m: t A) (i: key) (x: A),
   find i (add i x m) = Some x.
  Proof. intros; apply get_set_same. Qed.

  Theorem add_spec2: forall (m: t A) (i j: key) (x: A),
    i <> j -> find j (add i x m) = find j m.
  Proof.
   intros; cbv [find add].
   rewrite get_set_diff; congruence.
  Qed.

  Theorem remove_spec1: forall (m: t A)(i: key),
    find i (remove i m) = None.
  Proof. intros; apply get_remove_same. Qed.

  Theorem remove_spec2: forall (m: t A)(i j: key),
    i <> j -> find j (remove i m) = find j m.
  Proof.
   intros; cbv [find remove].
   rewrite get_remove_diff; congruence.
  Qed.

  (** Specification of [bindings], adapted from [MMaps.Positive].
      The induction principle [trie_ind] plays the role of the structural
      induction on trees, with [Node] as the smart constructor, so most of
      the proofs are the ones of [PositiveMap] where [simpl] is replaced
      by a rewrite with the corresponding [_Node] equation. *)

  Lemma xbindings_Node l o r i acc :
    xbindings (Node l o r) i acc =
    xbindings l (xO i)
      (match o with
       | Some e => (rev i, e) :: xbindings r (xI i) acc
       | None => xbindings r (xI i) acc
       end).
  Proof. case l, o, r; reflexivity. Qed.

  Local Notation InL := (InA eq_key_elt).

  Lemma xbindings_spec: forall m j acc k e,
    InL (k,e) (xbindings m j acc) <->
    InL (k,e) acc \/ exists x, k=(j@x) /\ find x m = Some e.
  Proof.
    unfold find.
    induction m as [|l IHl o r IHr _] using trie_ind; simpl.
    - intros. split; intro H.
      + now left.
      + destruct H as [H|[x [_ H]]]. assumption.
        discriminate H.
    - intros j acc k e. rewrite xbindings_Node. case o as [e'|];
      rewrite IHl, ?InA_cons, IHr; clear IHl IHr; split.
      + intros [[H|[H|H]]|H]; auto.
        * change (E.eq k (rev j) /\ e = e') in H. destruct H as (->,<-).
          right. exists xH. now rewrite get_Node.
        * destruct H as (x,(->,H)). right. exists (xI x). now rewrite get_Node.
        * destruct H as (x,(->,H)). right. exists (xO x). now rewrite get_Node.
      + intros [H|H]; auto.
        destruct H as (x,(->,H)). rewrite get_Node in H.
        destruct x; simpl in *.
        * left. right. right. now exists x.
        * right. now exists x.
        * left. left. injection H as ->. reflexivity.
      + intros [[H|H]|H]; auto.
        * destruct H as (x,(->,H)). right. exists (xI x). now rewrite get_Node.
        * destruct H as (x,(->,H)). right. exists (xO x). now rewrite get_Node.
      + intros [H|H]; auto.
        destruct H as (x,(->,H)). rewrite get_Node in H.
        destruct x; simpl in *.
        * left. right. now exists x.
        * right. now exists x.
        * discriminate.
  Qed.

  Lemma lt_rev_append: forall j x y, E.lt x y -> E.lt (j@x) (j@y).
  Proof. induction j; intros; simpl; auto. Qed.

  Lemma xbindings_sort m j acc :
    sort lt_key acc ->
    (forall x p, In x m -> InL p acc -> E.lt (j@x) (fst p)) ->
    sort lt_key (xbindings m j acc).
  Proof.
    revert j acc.
    induction m as [|l IHl o r IHr _] using trie_ind; simpl; trivial.
    intros j acc Hacc Hsacc. rewrite xbindings_Node. destruct o as [e|].
    - apply IHl;[constructor;[apply IHr; [apply Hacc|]|]|].
      + intros x p Hx Hp. apply Hsacc; trivial.
        destruct Hx as (v,Hv). exists v. now rewrite get_Node.
      + case_eq (xbindings r (xI j) acc); [constructor|].
        intros (z,e') q H. constructor.
        assert (H': InL (z,e') (xbindings r (xI j) acc)).
        { rewrite H. now constructor. }
        clear H q. rewrite xbindings_spec in H'.
        destruct H' as [H'|H'].
        * apply (Hsacc xH (z,e')); trivial. exists e. now rewrite get_Node.
        * destruct H' as (x,(->,H)).
          red. simpl. now apply lt_rev_append.
      + intros x (y,e') Hx Hy. inversion_clear Hy.
        rewrite H. simpl. now apply lt_rev_append.
        rewrite xbindings_spec in H.
        destruct H as [H|H].
        * apply Hsacc; trivial.
          destruct Hx as (v,Hv). exists v. now rewrite get_Node.
        * destruct H as (z,(->,H)). simpl.
          now apply lt_rev_append.
    - apply IHl; [apply IHr; [apply Hacc|]|].
      + intros x p Hx Hp. apply Hsacc; trivial.
        destruct Hx as (v,Hv). exists v. now rewrite get_Node.
      + intros x (y,e') Hx H. rewrite xbindings_spec in H.
        destruct H as [H|H].
        * apply Hsacc; trivial.
          destruct Hx as (v,Hv). exists v. now rewrite get_Node.
        * destruct H as (z,(->,H)). simpl.
          now apply lt_rev_append.
  Qed.

  Lemma bindings_spec1 m k e :
    InA eq_key_elt (k,e) (bindings m) <-> MapsTo k e m.
  Proof.
   unfold bindings, MapsTo. rewrite xbindings_spec.
   split; [ intros [H|(y & H & H')] | intros IN ].
   - inversion H.
   - simpl in *. now subst.
   - right. now exists k.
  Qed.

  Lemma bindings_spec2 m : sort lt_key (bindings m).
  Proof.
    unfold bindings.
    apply xbindings_sort. constructor. inversion 2.
  Qed.

  Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
  Proof.
    apply ME.Sort_NoDupA.
    apply bindings_spec2.
  Qed.

  (** Some complements about [bindings] that will be used
      in other correctness proofs below. *)

  Lemma xbindings_nil m p acc :
    xbindings m p acc = nil <-> is_empty m = true /\ acc = nil.
  Proof.
  revert p acc.
  induction m as [|l IHl o r IHr B] using trie_ind; simpl; intros; try easy.
  rewrite xbindings_Node, is_empty_Node by trivial.
  rewrite IHl. destruct o; [easy|]. rewrite IHr.
  destruct l, r; simpl in *; intuition easy.
  Qed.

  Lemma bindings_nil m : bindings m = nil <-> is_empty m = true.
  Proof.
  unfold bindings. now rewrite xbindings_nil.
  Qed.

  Definition fstmap (f:key->key) '(k, e) : key*A := (f k, e).

  Lemma xbindings_alt m j l :
   xbindings m j l = List.map (fstmap (rev_append j)) (bindings m) ++ l.
  Proof.
  revert j l.
  induction m as [|l IHl o r IHr _] using trie_ind; simpl; intros; auto.
  unfold bindings. rewrite !xbindings_Node.
  destruct o; simpl;
   rewrite !IHl, !IHr, ?map_app, ?map_map, <- ?app_assoc, ?app_nil_r; simpl;
   repeat match goal with
          | |- context [List.map ?g (List.map ?f ?l)] => rewrite (map_map f g l)
          | |- List.map _ _ = List.map _ _ => apply map_ext; now intros (?,?)
          | _ => progress f_equal
          end.
  Qed.

  Lemma bindings_node r l o :
   bindings (Node l o r) =
   (List.map (fstmap xO) (bindings l)) ++
   (match o with Some e => (xH,e)::nil | None => nil end) ++
   (List.map (fstmap xI) (bindings r)).
  Proof.
  unfold bindings at 1. rewrite xbindings_Node.
  rewrite !xbindings_alt, !app_nil_r.
  destruct o; reflexivity.
  Qed.

  (** [singleton] *)

  Theorem singleton_spec i x : bindings (singleton i x) = (i,x)::nil.
  Proof.
   unfold singleton, add.
   induction i; rewrite set_None, set_Node, bindings_node;
    [rewrite IHi|rewrite IHi|]; reflexivity.
  Qed.

  (** [cardinal] *)

  Lemma cardinal_Node l o r :
    cardinal (Node l o r) =
    (cardinal l + (match o with Some _ => 1 | None => 0 end) + cardinal r)%nat.
  Proof. case l, o, r; reflexivity. Qed.

  Lemma xbindings_length m j acc :
    length (xbindings m j acc) = (cardinal m + length acc)%nat.
  Proof.
   revert j acc.
   induction m as [|l IHl o r IHr _] using trie_ind; simpl; trivial; intros.
   rewrite xbindings_Node, cardinal_Node.
   destruct o; simpl; rewrite IHl; simpl; rewrite IHr;
    now rewrite ?Nat.add_succ_r, ?Nat.add_0_r, Nat.add_assoc.
  Qed.

  Lemma cardinal_spec m : cardinal m = length (bindings m).
  Proof.
   unfold bindings. rewrite xbindings_length. simpl.
   symmetry. apply Nat.add_0_r.
  Qed.

  (** [map] and [mapi] *)

  Variable B : Type.

  Section Mapi.

    Variable f : key -> A -> option B.

    Fixpoint xmapi' (m : branch A) (i : positive) {struct m} : t B :=
      branch_map (fun l o r =>
        Node (option_bind (fun l => xmapi' l (xO i)) l)
             (option_bind (f (rev i)) o)
             (option_bind (fun r => xmapi' r (xI i)) r)) m.

    Definition xmapi (m : t A) (i : positive) : t B :=
      match m with Some m => xmapi' m i | None => None end.

    Lemma xmapi_Node l o r i :
      xmapi (Node l o r) i =
      Node (xmapi l (xO i)) (option_bind (f (rev i)) o) (xmapi r (xI i)).
    Proof. case l, o, r; reflexivity. Qed.

  End Mapi.

  Definition mapi (f : key -> A -> B) m :=
    xmapi (fun k a => Some (f k a)) m xH.

  Definition map (f : A -> B) : t A -> t B := map_filter (fun a => Some (f a)).

  End A.

  Lemma xgmapi:
    forall (A B: Type) (f: key -> A -> option B) (i j : key) (m: t A),
      find i (xmapi f m j) = option_bind (f (j@i)) (find i m).
  Proof.
  unfold find.
  induction i; intros; induction m using trie_ind;
   rewrite ?xmapi_Node, ?get_Node, ?IHi; simpl; auto.
  Qed.

  Lemma xmapi_spec A B (f: key -> A -> option B) (i : key) (m : t A) :
    bindings (xmapi f m i) =
    mapfilter (fun '(k,e) => option_map (pair k) (f (i@k) e))
              (bindings m).
  Proof.
  revert i.
  induction m as [|l IHl o r IHr _] using trie_ind; simpl; intros. easy.
  rewrite xmapi_Node, !bindings_node, !mapfilter_app. f_equal.
  - rewrite IHl; auto. rewrite map_mapfilter, mapfilter_map; f_equiv.
    intros a a' <-. destruct a. simpl. now destruct f.
  - f_equal.
    + destruct o; simpl; trivial.
      unfold rev. now destruct f.
    + rewrite IHr; auto. rewrite map_mapfilter, mapfilter_map; f_equiv.
      intros a a' <-. destruct a. simpl. now destruct f.
  Qed.

  Lemma mapi_spec A B (f:key -> A -> B) (m : t A) :
    bindings (mapi f m) =
     List.map (fun '(k,e) => (k, f k e)) (bindings m).
  Proof.
  unfold mapi. rewrite xmapi_spec; simpl; auto.
  rewrite map_as_mapfilter. f_equiv. now intros (k,e) ? <-.
  Qed.

  Lemma map_as_mapi A B (f:A -> B)(m : t A) : map f m = mapi (fun _ => f) m.
  Proof.
  apply extensionality. intros i. unfold map, mapi.
  rewrite get_map_filter. now rewrite (xgmapi _ i xH m).
  Qed.

  Lemma map_spec A B (f:A -> B)(m : t A) :
    bindings (map f m) =
     List.map (fun '(k,e) => (k, f e)) (bindings m).
  Proof.
  now rewrite map_as_mapi, mapi_spec.
  Qed.

  (** [merge] *)

  Section Merge.
  Variable A B C : Type.
  Variable f : key -> option A -> option B -> option C.

  Local Notation xmerge'_l i m := (xmapi (fun k a => f k (Some a) None) (Some m) i).
  Local Notation xmerge'_r i m := (xmapi (fun k b => f k None (Some b)) (Some m) i).

  Let Fixpoint xmerge'' (m1 : branch A) (m2 : branch B) (i : positive) {struct m1} : t C.
  Proof. (* 49 cases *)
    case m1 as [ r1 | x1 | x1 r1 | l1 | l1 r1 | l1 x1 | l1 x1 r1 ];
    case m2 as [ r2 | x2 | x2 r2 | l2 | l2 r2 | l2 x2 | l2 x2 r2 ]; (apply Node;
     [ try (exact (xmerge'' l1 l2 (xO i)) || exact (xmerge'_l (xO i) l1) || exact (xmerge'_r (xO i) l2))
     | apply (f (rev i)); [ try exact (Some x1) | try exact (Some x2) ]
     | try (exact (xmerge'' r1 r2 (xI i)) || exact (xmerge'_l (xI i) r1) || exact (xmerge'_r (xI i) r2))
     ]; exact None).
  Defined.
  Local Definition xmerge' := Eval cbv [xmerge'' Node xmapi] in xmerge''.

  Definition xmerge (m1 : t A) (m2 : t B) (i : positive) : t C :=
    match m1, m2 with
    | None, None => None
    | None, Some m2 => xmerge'_r i m2
    | Some m1, None => xmerge'_l i m1
    | Some m1, Some m2 => xmerge' m1 m2 i
    end.

  Hypothesis f_None_None : forall k, f k None None = None.

  Lemma xmerge_Node_Node l1 o1 r1 l2 o2 r2 i :
    xmerge (Node l1 o1 r1) (Node l2 o2 r2) i =
    Node (xmerge l1 l2 (xO i)) (f (rev i) o1 o2) (xmerge r1 r2 (xI i)).
  Proof. case l1, o1, r1, l2, o2, r2; trivial; rewrite ?f_None_None; trivial. Qed.

  Lemma xgmerge: forall (i j: key)(m1:t A)(m2: t B),
      find i (xmerge m1 m2 j) = f (j@i) (find i m1) (find i m2).
  Proof.
    unfold find.
    induction i; intros j m1 m2;
    induction m1 using trie_ind; induction m2 using trie_ind;
    repeat (change (xmerge None) with (xmerge (Node None None None))
         || change (xmerge ?x None) with (xmerge x (Node None None None)));
    rewrite ?xmerge_Node_Node, ?get_Node, ?IHi; simpl; auto.
  Qed.

  End Merge.

  Definition merge {A B C}(f:key->option A->option B->option C) m1 m2 :=
   xmerge
     (fun k o1 o2 => match o1,o2 with
       | None,None => None
       | _, _ => f k o1 o2
      end)
     m1 m2 xH.

  Lemma merge_spec1 {A B C}(f:key->option A->option B->option C) :
    forall m m' x,
    In x m \/ In x m' ->
    exists y, E.eq y x /\
     find x (merge f m m') = f y (find x m) (find x m').
  Proof.
  intros. exists x. split. reflexivity.
  unfold merge.
  rewrite xgmerge; simpl; auto.
  rewrite <- 2 mem_spec, 2 mem_find in H.
  destruct (find x m); simpl; auto.
  destruct (find x m'); simpl; auto. intuition discriminate.
  Qed.

  Lemma merge_spec2 {A B C}(f:key->option A->option B->option C) :
    forall m m' x, In x (merge f m m') -> In x m \/ In x m'.
  Proof.
  intros.
  rewrite <-mem_spec, mem_find in H.
  unfold merge in H.
  rewrite xgmerge in H; simpl; auto.
  rewrite <- 2 mem_spec, 2 mem_find.
  destruct (find x m); simpl in *; auto.
  destruct (find x m'); simpl in *; auto.
  Qed.

  (** [fold] *)

  Section Fold.

    Variables A B : Type.
    Variable f : key -> A -> B -> B.

    Fixpoint xfold' (m : branch A) (v : B) (i : key) {struct m} : B :=
      branch_map (fun l o r =>
        let v := match l with Some l => xfold' l v (xO i) | None => v end in
        let v := match o with Some x => f (rev i) x v | None => v end in
        match r with Some r => xfold' r v (xI i) | None => v end) m.

    Definition xfold (m : t A) (v : B) (i : key) : B :=
      match m with Some m => xfold' m v i | None => v end.

    Definition fold m i := xfold m i xH.

    Lemma xfold_Node l o r v i :
      xfold (Node l o r) v i =
      match o with
      | Some x => xfold r (f (rev i) x (xfold l v (xO i))) (xI i)
      | None => xfold r (xfold l v (xO i)) (xI i)
      end.
    Proof. case l, o, r; reflexivity. Qed.

  End Fold.

  Lemma fold_spec :
    forall {A}(m:t A){B}(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
  Proof.
    unfold fold, bindings. intros A m B i f. revert m i.
    set (f' := fun a p => f (fst p) (snd p) a).
    assert (H: forall m i j acc,
      fold_left f' acc (xfold f m i j) =
      fold_left f' (xbindings m j acc) i).
    { induction m as [|l IHl o r IHr _] using trie_ind; intros; trivial.
      rewrite xfold_Node, xbindings_Node.
      destruct o; simpl; now rewrite IHr, <- IHl. }
    intros. exact (H m i xH nil).
  Qed.

  (** [equal] *)

  (** Thanks to extensionality, two tries are [equal] when the trie of
      their differences is empty. *)

  Definition equal_opt (A:Type)(cmp : A -> A -> bool) o1 o2 : option unit :=
    match o1, o2 with
    | None, None => None
    | Some v1, Some v2 => if cmp v1 v2 then None else Some tt
    | _, _ => Some tt
    end.

  Definition equal (A:Type)(cmp : A -> A -> bool)(m1 m2 : t A) : bool :=
    is_empty (combine (equal_opt cmp) m1 m2).

  Definition Equal A (m m':t A) := forall y, find y m = find y m'.

  Definition Eqdom A (m m':t A) := forall k, In k m <-> In k m'.

  Definition Equiv A (R:A->A->Prop) m m' :=
    Eqdom m m' /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').

  Definition Equivb (A:Type)(cmp: A->A->bool) := Equiv (Cmp cmp).

  Lemma equal_spec : forall (A:Type)(cmp:A->A->bool)(m m':t A),
    equal cmp m m' = true <-> Equivb cmp m m'.
  Proof.
  intros A cmp m m'. unfold equal, Equivb, Equiv, Eqdom, In, MapsTo, Cmp.
  rewrite is_empty_spec. unfold find.
  setoid_rewrite get_combine; [|reflexivity].
  split.
  - intros H. split.
    + intros k. specialize (H k). unfold equal_opt in H.
      destruct (get k m), (get k m'); split; try discriminate;
        intros (v,Hv); try discriminate; eauto.
    + intros k e e' He He'. specialize (H k). rewrite He, He' in H.
      simpl in H. now destruct cmp.
  - intros (H1,H2) k. specialize (H1 k). specialize (H2 k).
    unfold equal_opt.
    destruct (get k m) as [v|], (get k m') as [v'|]; trivial.
    + now rewrite (H2 v v').
    + exfalso. destruct H1 as (H1,_). destruct H1 as (?,H1); eauto. discriminate.
    + exfalso. destruct H1 as (_,H1). destruct H1 as (?,H1); eauto. discriminate.
  Qed.

  Lemma equal_1 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    Equivb cmp m m' -> equal cmp m m' = true.
  Proof. intros; now apply equal_spec. Qed.

  Lemma equal_2 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof. intros; now apply equal_spec. Qed.

  (** [compare], adapted from [MMaps.Positive]. *)

  Section Compare.
  Variable A : Type.
  Variable cmp : A -> A -> comparison.

  Definition is_empty2 (o:option A) (r:t A) :=
   match o with None => is_empty r | _ => false end.

  Definition ocompare (ec : branch A -> branch A -> comparison * flag)
    (m1 m2 : t A) : comparison * flag :=
    match m1, m2 with
    | None, None => (Eq,EOL)
    | None, Some _ => (Lt,EOL)
    | Some _, None => (Gt,EOL)
    | Some b1, Some b2 => ec b1 b2
    end.

  Fixpoint ecompare' (b1 b2 : branch A) {struct b1} : comparison * flag :=
    branch_map (fun l1 o1 r1 => branch_map (fun l2 o2 r2 =>
     match ocompare ecompare' l1 l2 with
     | (Eq,_) =>
       match o1, o2 with
       | None, None => ocompare ecompare' r1 r2
       | Some d1, Some d2 => elex (cmp d1 d2) (ocompare ecompare' r1 r2)
       | None, Some _ => if is_empty r1 then (Lt,EOL) else (Gt,Early)
       | Some _, None => if is_empty r2 then (Gt,EOL) else (Lt,Early)
       end
     | (c,Early) => (c,Early)
     | (Lt,EOL) => if is_empty2 o1 r1 then (Lt,EOL) else (Gt,Early)
     | (Gt,EOL) => if is_empty2 o2 r2 then (Gt,EOL) else (Lt,Early)
     end) b2) b1.

  Definition ecompare := ocompare ecompare'.

  Definition compare (m1 m2: t A) := fst (ecompare m1 m2).

  Lemma ecompare_None_l m : ecompare None m = if is_empty m then (Eq,EOL) else (Lt,EOL).
  Proof. now case m. Qed.

  Lemma ecompare_None_r m : ecompare m None = if is_empty m then (Eq,EOL) else (Gt,EOL).
  Proof. now case m. Qed.

  Lemma ecompare_Node l1 o1 r1 l2 o2 r2 :
    ecompare (Node l1 o1 r1) (Node l2 o2 r2) =
     match ecompare l1 l2 with
     | (Eq,_) =>
       match o1, o2 with
       | None, None => ecompare r1 r2
       | Some d1, Some d2 => elex (cmp d1 d2) (ecompare r1 r2)
       | None, Some _ => if is_empty r1 then (Lt,EOL) else (Gt,Early)
       | Some _, None => if is_empty r2 then (Gt,EOL) else (Lt,Early)
       end
     | (c,Early) => (c,Early)
     | (Lt,EOL) => if is_empty2 o1 r1 then (Lt,EOL) else (Gt,Early)
     | (Gt,EOL) => if is_empty2 o2 r2 then (Gt,EOL) else (Lt,Early)
     end.
  Proof.
    case l1, o1, r1, l2, o2, r2; try reflexivity;
      simpl; repeat match goal with |- context [ecompare' ?a ?b] => destruct (ecompare' a b) as ([ ],[ ]) end;
      try reflexivity; try (destruct (cmp _ _); reflexivity).
  Qed.

  Local Notation Lcmp := (list_compare (pair_compare E.compare cmp)).
  Local Notation eLcmp := (list_ecompare (pair_compare E.compare cmp)).

  Lemma eLcmp_fstmap l1 l2 f :
   (forall k k', E.compare (f k) (f k') = E.compare k k') ->
   eLcmp (List.map (fstmap f) l1) (List.map (fstmap f) l2) = eLcmp l1 l2.
  Proof.
  revert l2.
  induction l1 as [|(x1,d1) l1 IH]; destruct l2 as [|(x2,d2) l2];
   intros E; simpl; auto.
  rewrite E. case E.compare_spec; try easy. unfold E.eq. intros <-.
  destruct (cmp d1 d2); auto.
  Qed.

  Lemma ecompare_spec m1 m2 :
   ecompare m1 m2 = eLcmp (bindings m1) (bindings m2).
  Proof.
  revert m2.
  induction m1 as [|l1 IHl1 o1 r1 IHr1 B1] using trie_ind; intros m2.
  - rewrite ecompare_None_l. generalize (bindings_nil m2).
    destruct bindings, is_empty; simpl; intuition easy.
  - generalize (bindings_nil (Node l1 o1 r1)).
    induction m2 as [|l2 _ o2 r2 _ B2] using trie_ind.
    + rewrite ecompare_None_r.
      destruct (bindings (Node l1 o1 r1)), is_empty; intuition easy.
    + intros _.
      rewrite ecompare_Node, !bindings_node.
      rewrite IHl1, ?IHr1; clear IHl1 IHr1.
      rewrite list_ecompare_app.
      * rewrite eLcmp_fstmap by auto.
        destruct (eLcmp (bindings l1) (bindings l2)) as ([ ],b).
        { destruct o1 as [d1| ], o2 as [d2| ]; simpl.
          - destruct (cmp d1 d2) eqn:Eo; auto.
            rewrite eLcmp_fstmap; auto.
          - generalize (bindings_nil r2).
            destruct is_empty, (bindings r2); simpl; intuition; try easy.
            now destruct p.
          - generalize (bindings_nil r1).
            destruct is_empty, (bindings r1); simpl; intuition; try easy.
            now destruct p.
          - rewrite eLcmp_fstmap; auto. }
        { destruct b; auto.
          destruct o1; simpl; auto.
          generalize (bindings_nil r1).
          destruct bindings, is_empty; simpl; intuition easy. }
        { destruct b; auto.
          destruct o2; simpl; auto.
          generalize (bindings_nil r2).
          destruct bindings, is_empty; simpl; intuition easy. }
      * intros (x,d) (y,d').
        rewrite !in_app_iff, !in_map_iff.
        intros ((k,e) & [= <- <-] & _) [P|((k',e') & [= <- <-] & _)];
          simpl; auto.
        destruct o1; try easy. simpl in P.
        now destruct P as [[= <- <-]|[ ]].
      * intros (x,d) (y,d').
        rewrite !in_app_iff, !in_map_iff.
        intros ((k,e) & [= <- <-] & _) [P|((k',e') & [= <- <-] & _)];
          simpl; auto.
        destruct o2; try easy. simpl in P.
        now destruct P as [[= <- <-]|[ ]].
  Qed.

  Lemma compare_spec m1 m2 :
   compare m1 m2 = Lcmp (bindings m1) (bindings m2).
  Proof.
  unfold compare. rewrite <- list_ecompare_fst. f_equal.
  apply ecompare_spec.
  Qed.

  End Compare.

  (** [filter], [partition], [for_all], [exists_] *)

  Definition filter A (f:key->A->bool) m :=
    xmapi (fun k a => if f k a then Some a else None) m xH.
  Definition partition A (f:key->A->bool) m :=
    (filter f m, filter (fun k e => negb (f k e)) m).

  Section ForallExists.
  Variable A : Type.
  Variable f : key -> A -> bool.

  Fixpoint xforall' (m : branch A) (j : key) {struct m} : bool :=
    branch_map (fun l o r =>
      (match o with Some e => f (rev j) e | None => true end) &&&
      (match l with Some l => xforall' l (xO j) | None => true end) &&&
      (match r with Some r => xforall' r (xI j) | None => true end)) m.

  Definition xforall (m : t A) (j : key) : bool :=
    match m with Some m => xforall' m j | None => true end.

  Definition for_all m := xforall m xH.

  Fixpoint xexists' (m : branch A) (j : key) {struct m} : bool :=
    branch_map (fun l o r =>
      (match o with Some e => f (rev j) e | None => false end) |||
      (match l with Some l => xexists' l (xO j) | None => false end) |||
      (match r with Some r => xexists' r (xI j) | None => false end)) m.

  Definition xexists (m : t A) (j : key) : bool :=
    match m with Some m => xexists' m j | None => false end.

  Definition exists_ m := xexists m xH.

  Lemma xforall_Node l o r j :
    xforall (Node l o r) j =
    (match o with Some e => f (rev j) e | None => true end) &&&
    xforall l (xO j) &&& xforall r (xI j).
  Proof. case l, o, r; simpl; now rewrite ?andb_true_r. Qed.

  Lemma xexists_Node l o r j :
    xexists (Node l o r) j =
    (match o with Some e => f (rev j) e | None => false end) |||
    xexists l (xO j) ||| xexists r (xI j).
  Proof. case l, o, r; simpl; now rewrite ?orb_false_r. Qed.

  End ForallExists.

  Lemma filter_spec A (f:key->A->bool) m :
   bindings (filter f m) = List.filter (fun '(k,e) => f k e) (bindings m).
  Proof.
  unfold filter. rewrite xmapi_spec; simpl; auto.
  rewrite filter_as_mapfilter. f_equiv. intros (k,e) ? <-.
  now destruct f.
  Qed.

  Lemma partition_spec A (f:key->A->bool) m :
   prodmap (@bindings _) (partition f m) =
    List.partition (fun '(k,e) => f k e) (bindings m).
  Proof.
  unfold partition, prodmap. rewrite partition_filter. f_equiv.
  apply filter_spec.
  rewrite filter_spec. f_equiv. now intros (k,e) ? <-.
  Qed.

  Lemma forallb_fstmap A (g : key -> A -> bool) (h : key -> key) l :
    forallb (fun '(k,e) => g k e) (List.map (fstmap h) l) =
    forallb (fun '(k,e) => g (h k) e) l.
  Proof. rewrite forallb_map. f_equiv. now intros (k,e) ? <-. Qed.

  Lemma existsb_fstmap A (g : key -> A -> bool) (h : key -> key) l :
    existsb (fun '(k,e) => g k e) (List.map (fstmap h) l) =
    existsb (fun '(k,e) => g (h k) e) l.
  Proof. rewrite existsb_map. f_equiv. now intros (k,e) ? <-. Qed.

  Lemma xforall_spec A (f:key->A->bool) m i :
   xforall f m i = List.forallb (fun '(k,e) => f (i@k) e) (bindings m).
  Proof.
  revert i.
  induction m as [|l IHl o r IHr _] using trie_ind; simpl; intros; auto.
  rewrite xforall_Node, bindings_node, !forallb_app, !forallb_fstmap, IHl, IHr.
  rewrite <- !andb_lazy_alt. unfold rev.
  destruct o; simpl; [destruct (f (i@xH) a); simpl|];
   now rewrite ?andb_false_r, ?andb_true_r.
  Qed.

  Lemma for_all_spec A (f:key->A->bool) m :
   for_all f m = List.forallb (fun '(k,e) => f k e) (bindings m).
  Proof.
  apply xforall_spec.
  Qed.

  Lemma xexists_spec A (f:key->A->bool) m i :
   xexists f m i = List.existsb (fun '(k,e) => f (i@k) e) (bindings m).
  Proof.
  revert i.
  induction m as [|l IHl o r IHr _] using trie_ind; simpl; intros; auto.
  rewrite xexists_Node, bindings_node, !existsb_app, !existsb_fstmap, IHl, IHr.
  rewrite <- !orb_lazy_alt. unfold rev.
  destruct o; simpl; [destruct (f (i@xH) a); simpl|];
   now rewrite ?orb_false_r, ?orb_true_r.
  Qed.

  Lemma exists_spec A (f:key->A->bool) m :
   exists_ f m = List.existsb (fun '(k,e) => f k e) (bindings m).
  Proof.
  apply xexists_spec.
  Qed.

End TrieMap.

(** Here come some additional facts about this implementation.
  Most are facts that cannot be derivable from the general interface. *)

Module TrieMapAdditionalFacts.
  Import TrieMap.

  Lemma MapsTo_1 {A} m x y e : x = y -> @MapsTo A x e m -> MapsTo y e m.
  Proof. congruence. Qed.

  (** The main point of this implementation: [Equal] maps are
      Leibniz-equal. *)

  Lemma Equal_eq {A} (m m' : t A) : Equal m m' <-> m = m'.
  Proof.
  split.
  - apply extensionality.
  - intros <- k. reflexivity.
  Qed.

  Lemma Equiv_eq {A} (m m' : t A) :
    Equiv Logic.eq m m' <-> m = m'.
  Proof.
  rewrite <- Equal_eq. unfold Equiv, Eqdom, In, MapsTo, Equal, find.
  split.
  - intros (H1,H2) k. specialize (H1 k). specialize (H2 k).
    destruct (get k m) as [v|], (get k m') as [v'|]; trivial.
    + f_equal. now apply H2.
    + exfalso. destruct H1 as (H1,_). destruct H1 as (?,H1); eauto. discriminate.
    + exfalso. destruct H1 as (_,H1). destruct H1 as (?,H1); eauto. discriminate.
  - intros H. split.
    + intros k. now rewrite H.
    + intros k e e' He He'. rewrite H in He. congruence.
  Qed.

  (* Derivable from the Map interface *)
  Theorem gsspec {A} i j x (m: t A) :
    find i (add j x m) = if E.eq_dec i j then Some x else find i m.
  Proof.
    destruct (E.eq_dec i j) as [->|];
    [ apply add_spec1 | apply add_spec2; auto ].
  Qed.

  (* Not derivable from the Map interface, but easy from extensionality *)
  Theorem gsident {A} i (m:t A) v :
    find i m = Some v -> add i v m = m.
  Proof.
    intros H. apply extensionality. intros k.
    change (find k (add i v m) = find k m).
    rewrite gsspec. destruct E.eq_dec; congruence.
  Qed.

  Theorem remove_absent {A} i (m:t A) :
    find i m = None -> remove i m = m.
  Proof.
    intros H. apply extensionality. intros k.
    change (find k (remove i m) = find k m).
    destruct (E.eq_dec k i) as [->|].
    - now rewrite remove_spec1.
    - apply remove_spec2; auto.
  Qed.

  Theorem merge_commut{A B C}
    (f: key -> option A -> option B -> option C)
    (g: key -> option B -> option A -> option C) :
    (forall k o1 o2, f k o1 o2 = g k o2 o1) ->
    forall m1 m2, merge f m1 m2 = merge g m2 m1.
  Proof.
    intros E m1 m2. apply extensionality. intros k.
    change (find k (merge f m1 m2) = find k (merge g m2 m1)).
    unfold merge. rewrite !xgmerge by (intro; reflexivity); simpl.
    destruct (find k m1), (find k m2); simpl; auto.
  Qed.

End TrieMapAdditionalFacts.
