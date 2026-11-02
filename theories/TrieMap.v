(** * Finite Modular Maps: Implementation for Positive Keys by Extensional Tries *)

(** The data structure is [MMaps.Trie]; this file only adds the [MMaps]
    specifications. Authors of the trie: Andrew W. Appel, Xavier Leroy,
    Andres Erbsen. *)

From Coq Require Import Bool PeanoNat PArith OrdersEx OrdersLists.
From Coq Require List.
From MMaps Require Import Utils Interface Comparisons Trie.

Local Set Implicit Arguments.
Local Unset Strict Implicit.
Local Open Scope lazy_bool_scope.

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

  Local Infix "@" := rev_append (at level 60).

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

  (** [bindings] *)

  Definition bindings (m : t A) : list (key*A) := to_list m.

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

  (** Specification of [bindings] *)

  Lemma bindings_node r l o :
   bindings (Node l o r) =
   (List.map (fstmap xO) (bindings l)) ++
   (match o with Some e => (xH,e)::nil | None => nil end) ++
   (List.map (fstmap xI) (bindings r)).
  Proof. apply to_list_Node. Qed.

  Local Lemma InA_eq_key_elt (p : key*A) l : InA eq_key_elt p l <-> List.In p l.
  Proof.
    unfold eq_key_elt, ME.eqke, RelProd, relation_conjunction, RelCompFun, E.eq.
    rewrite InA_alt. split.
    - intros ((k,x) & (Hk,Hx) & ?). destruct p; simpl in *. now subst.
    - intros ?. exists p. split; [|trivial]. destruct p; split; reflexivity.
  Qed.

  Lemma bindings_spec1 m k e :
    InA eq_key_elt (k,e) (bindings m) <-> MapsTo k e m.
  Proof. rewrite InA_eq_key_elt. apply In_to_list. Qed.

  Lemma bindings_spec2 m : sort lt_key (bindings m).
  Proof.
    unfold bindings, lt_key, ME.ltk, RelCompFun.
    apply (Sorted_to_list E.lt); unfold E.lt; intros; simpl; auto.
  Qed.

  Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
  Proof.
    apply ME.Sort_NoDupA.
    apply bindings_spec2.
  Qed.

  Lemma is_empty_Node l o r : isBranch l o r -> is_empty (Node l o r) = false.
  Proof. case l, o, r; simpl; tauto. Qed.

  Lemma bindings_nil m : bindings m = nil <-> is_empty m = true.
  Proof.
    induction m as [|l IHl o r IHr B] using trie_ind; [easy|].
    rewrite bindings_node, is_empty_Node by trivial.
    split; [|discriminate]. intros H.
    apply app_eq_nil in H. destruct H as (H1,H2).
    apply app_eq_nil in H2. destruct H2 as (H2,H3).
    apply map_eq_nil in H1. apply map_eq_nil in H3.
    rewrite IHl in H1. rewrite IHr in H3.
    destruct l, o, r; simpl in *; try discriminate; destruct B.
  Qed.

  (** [singleton] *)

  Theorem singleton_spec i x : bindings (singleton i x) = (i,x)::nil.
  Proof. apply to_list_singleton. Qed.

  (** [cardinal] *)

  Lemma cardinal_Node l o r :
    cardinal (Node l o r) =
    (cardinal l + (match o with Some _ => 1 | None => 0 end) + cardinal r)%nat.
  Proof. case l, o, r; reflexivity. Qed.

  Lemma cardinal_spec m : cardinal m = length (bindings m).
  Proof.
    induction m as [|l IHl o r IHr _] using trie_ind; trivial.
    rewrite bindings_node, cardinal_Node, !app_length, !map_length, IHl, IHr.
    destruct o; simpl; now rewrite ?Nat.add_0_r, ?Nat.add_1_r, ?Nat.add_succ_r.
  Qed.

  (** [map] and [mapi] *)

  Variable B : Type.

  Definition mapi (f : key -> A -> B) m :=
    xmapi_filter (fun k a => Some (f k a)) m xH.

  Definition map (f : A -> B) : t A -> t B := map_filter (fun a => Some (f a)).

  End A.

  Lemma xmapi_spec A B (f: key -> A -> option B) (i : key) (m : t A) :
    bindings (xmapi_filter f m i) =
    mapfilter (fun '(k,e) => option_map (pair k) (f (i@k) e))
              (bindings m).
  Proof.
  revert i.
  induction m as [|l IHl o r IHr _] using trie_ind; simpl; intros. easy.
  rewrite xmapi_filter_Node, !bindings_node, !mapfilter_app. f_equal.
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
  rewrite get_map_filter, get_xmapi_filter. reflexivity.
  Qed.

  Lemma map_spec A B (f:A -> B)(m : t A) :
    bindings (map f m) =
     List.map (fun '(k,e) => (k, f e)) (bindings m).
  Proof.
  now rewrite map_as_mapi, mapi_spec.
  Qed.

  (** [merge] *)

  Definition merge {A B C}(f:key->option A->option B->option C) m1 m2 :=
   xmergei
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
  unfold merge, find.
  rewrite get_xmergei; simpl; auto.
  rewrite <- 2 mem_spec, 2 mem_find in H. unfold find in H.
  destruct (get x m); simpl; auto.
  destruct (get x m'); simpl; auto. intuition discriminate.
  Qed.

  Lemma merge_spec2 {A B C}(f:key->option A->option B->option C) :
    forall m m' x, In x (merge f m m') -> In x m \/ In x m'.
  Proof.
  intros.
  rewrite <-mem_spec, mem_find in H.
  unfold merge, find in H.
  rewrite get_xmergei in H; simpl; auto.
  rewrite <- 2 mem_spec, 2 mem_find. unfold find.
  destruct (get x m); simpl in *; auto.
  destruct (get x m'); simpl in *; auto.
  Qed.

  (** [fold] *)

  Section Fold.

    Variables A B : Type.
    Variable f : key -> A -> B -> B.

    Definition fold (m : t A) (i : B) : B := Trie.fold f m i.

  End Fold.

  Lemma fold_spec :
    forall {A}(m:t A){B}(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
  Proof. intros. apply fold_to_list. Qed.

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
    xmapi_filter (fun k a => if f k a then Some a else None) m xH.
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

  (* Not derivable from the Map interface; instances of [Trie.set_idemp]
     and [Trie.remove_not_in] *)
  Theorem gsident {A} i (m:t A) v :
    find i m = Some v -> add i v m = m.
  Proof. apply set_idemp. Qed.

  Theorem remove_absent {A} i (m:t A) :
    find i m = None -> remove i m = m.
  Proof. apply remove_not_in. Qed.

  Theorem merge_commut{A B C}
    (f: key -> option A -> option B -> option C)
    (g: key -> option B -> option A -> option C) :
    (forall k o1 o2, f k o1 o2 = g k o2 o1) ->
    forall m1 m2, merge f m1 m2 = merge g m2 m1.
  Proof.
    intros E m1 m2. apply extensionality. intros k.
    unfold merge. rewrite !get_xmergei by (intro; reflexivity); simpl.
    destruct (get k m1), (get k m2); simpl; auto.
  Qed.

End TrieMapAdditionalFacts.
