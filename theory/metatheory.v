Require Import Log.logicalrelations.

Lemma lc_n_Sn : forall t n,
    lc_at t n -> lc_at t n.+1.
Proof.
  induction t; simpl; intro; eauto.
  - move=> /andP[lct1 lct2].
    apply/andP.
    split; [apply IHt1 | apply IHt2]; auto.
Qed.

Lemma open_lcat: forall t x k k',
    lc_at t k -> lc_at (open' t x k') k.
Proof.
  induction t; unfold open; simpl; intros; eauto.
  { case: ifP; eauto. }
  { move: H.
    move=> /andP H.
    apply /andP.
    split; [eapply IHt1 | eapply IHt2]; intuition.
  }
Qed.

Fixpoint openall t x (n: nat) :=
  match n with
  | O => t
  | S n' => openall (open' t x n') x n'
  end.

Variable x: logicalrelations.ident.
Variable y: logicalrelations.ident.

(* Eval unfold openall) in (openall (tApp (^9) (^10)) x 10). *)

Lemma openall_tapp : forall n t1 t2 x,
  tApp (openall t1 x n) (openall t2 x n) = openall (tApp t1 t2) x n.
Proof.
  induction n; simpl; intros; eauto.
Qed.

Lemma openall_tConst: forall n y x,
    openall (tConst y) x n = tConst y.
Proof.
  induction n; intros; simpl; eauto.
Qed.

Lemma openall_tVar: forall n y x,
    openall (# y) x n = # y.
Proof.
  induction n; intros; simpl; eauto.
Qed.

Lemma open_tVar: forall k y x,
    open' (# y) x k = # y.
Proof.
  induction k; intros; simpl; eauto.
Qed.

Lemma open_tConst: forall n y x,
    open' (tConst y) x n = tConst y.
Proof.
  induction n; intros; simpl; eauto.
Qed.

Lemma open'_tapp : forall n t1 t2 x,
  tApp (open' t1 x n) (open' t2 x n) = open' (tApp t1 t2) x n.
Proof.
  induction n; simpl; intros; eauto.
Qed.

Lemma open_bVar_neq: forall m n x,
    n <> m -> open' ^ (n) x m = ^n.
Proof.
  intros.
  induction m; simpl; case: eqnP; intros; first [contradiction | eauto].
Qed.

Lemma open_bVar: forall n x,
    open' ^ (n) x n = #x.
Proof.
  induction n; simpl; eauto.
  case: eqnP; intuition.
Qed.

Lemma openall_bVar: forall m n x,
    n < m -> openall ^ (n) x m = # x.
Proof.
  induction m.
  { move=> n x H.
    simpl.
    unfold open; unfold open'.
    (* case: eqnP; intros; simpl; eauto. *)
    (* rewrite leq_eqVlt in H. *)
    (* case/orP: H; intros; [|]. *)
    (* by move/eqnP: a. *)
    (* inversion b; eauto. *)
    admit.
  }
  { intros.
    simpl.
    case: eqnP; intros.
    subst.
    rewrite openall_tVar; reflexivity.
    apply IHm.
    (* rewrite ltnS in H. *)
    rewrite leq_eqVlt in H.
    case/orP: H.
    move=> /eqP H.
    subst.
    inversion H.
    contradiction.
    intros.
    admit.
  }
Admitted.


Lemma lc_at_open: forall t x k,
    lc_at (open' t x k) k -> lc_at t k.+1.
Proof.
  induction t.
  { intros.
    simpl in *.
    auto. }
  { intros x k.
    simpl.
    case: ifP.
    move=> /eqnP eq.
    subst; auto.
    move=> /eqnP neq.
    intro.
    inversion H.
    move: H1.
    move=> /ltP l.
    eauto.
  }
  { intros.
    simpl in *.
    eapply IHt.
    eauto.
  }
  { intros x k.
    simpl.
    move=> /andP H.
    apply /andP.
    destruct H.
    split; [ eapply IHt1 | eapply IHt2]; eauto.
  }
  { simpl.
    auto.
  }
Qed.

Lemma open'_comm: forall t k k' x,
    open' (open' t x k') x k = open' (open' t x k) x k'.
Proof.
  induction t; intros; simpl; try solve [f_equal; eauto].
  repeat (case: eqnP; simpl; intros; contradiction || auto).
Qed.

Lemma openall_tLam : forall k t T x,
    k <> 0 -> openall (tLam T t) x k = tLam T (openall t x k.+1).
Proof.
  induction k.
  { intros; contradiction. }
  { simpl.
    intros.
    rewrite IHk; simpl; auto.
    intro.
    admit.
  }
Admitted.

Lemma openall_change : forall k t x y,
  lc (openall t x k) -> lc (openall t y k).
Proof.
  induction t.
  { intros; rewrite openall_tVar; constructor. }
  { induction k; simpl; intros x y; try solve [eauto].
    case: eqnP; intros.
    rewrite openall_tVar; eauto.
    eapply IHk; eauto.
  }
  { clear IHt.
    intros x y.
    (* rewrite ?openall_tLam. *)
    (* intros. *)
    (* inversion_clear H. *)
    (* apply lc_abs with L. *)
    (* simpl. *)
    (* intros. *)

    (* induction k; simpl; intros; auto. *)

    (* admit. *)
    admit. }
  { intros; rewrite <- ?openall_tapp in *.
    inversion_clear H.
    constructor; [eapply IHt1 | eapply IHt2]; eauto.
  }
  { intros.
    rewrite openall_tConst; eauto.
  }


Admitted.

Lemma lcatt_open''_lc: forall t k x,
    lc_at t k -> lc (openall t x k).
Proof.
  induction t; intros; simpl in *.
  { rewrite openall_tVar; eauto. }
  { rewrite openall_bVar; eauto. }
  { apply (IHt k.+1 x) in H.
    simpl in H.
    clear IHt.
    generalize dependent x.
    generalize dependent t.
    induction k; intros; simpl in *.
    { apply lc_abs with nil.
      intros; eauto.
      pose proof (openall_change 1 t i x1); auto.
    }
    { eapply IHk; auto. admit. }
  }
  { move: H.
    move=> /andP H.
    destruct H.
    rewrite <- openall_tapp.
    constructor; eauto. }
  { rewrite openall_tConst; eauto. }
Admitted.

Theorem lc_at_lc : forall t,
    lc t <-> lc_at t 0.
Proof.
  intros.
  split.
  { induction 1; simpl; intuition.
    destruct (ident_fresh L) as [x].
    apply lc_at_open with (x := x).
    apply H0; assumption.
  }
  { destruct (ident_fresh nil) as [x].
    intro H.
    apply (lcatt_open''_lc _ _ x) in H; auto.
  }
Qed.

Definition body (t: term) := exists L, forall x, x ∉ L -> lc (open t x).

Theorem lc_abs_iff_body : forall t T,
    lc (tLam T t) <-> body t.
Proof.
  intros; split; intros; try inversion H; eauto.
  exists L; apply H1; auto.
Qed.
