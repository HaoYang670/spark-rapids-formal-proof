Require Export  Coq.Bool.Bool.
Require Export Coq.Lists.List.

Inductive float :=
  | Nan
  | Others.

(* Nan >= Others *)
Definition CPUge (f1 f2: float): bool := 
  match f1, f2 with
  | Nan, _ => true
  | Others, Nan => false
  | Others, Others => true
  end. 

(* Comparision with Nan always leads to false*)
Definition cuDFge (f1 f2: float): bool := 
  match f1, f2 with
  | Nan, _ => false
  | _, Nan => false
  | Others, Others => true
  end.

(** Give a comparasion function and a column,
  the function will return the max value.
  Type: (float -> float -> bool) -> list (option float) -> option float
  *)
Fixpoint max (ge: float -> float -> bool) col :=
  match col with
  | nil => None
  | None::s => max ge s
  | Some(a)::s => match (max ge s) with
    | None => Some a
    | Some b => Some (if (ge a b) then a else b)
    end
  end.

Definition CPUmax := max CPUge.
Definition cuDFmax := max cuDFge.

Definition isNan f :=
  match f with
  | Some Nan => true
  | _ => false
  end.

Fixpoint hasNan col := 
  match col with
  | nil => false
  | Some Nan :: _ => true
  | _ :: s => hasNan s
  end.

Definition GPUmax col :=
  match (hasNan col) with
  | true => Some(Nan)
  | false => cuDFmax col
  end.

(** All types and functions are defined above.
  The followings are lemmas and theorms we need
  to prove.
  *)

(** if a col doesn't have Nan, 
  then its tail doesn't have nan *)
Lemma derive_not_has_nan: forall a col,
  hasNan (a::col) = false -> hasNan col = false.
Proof.
  intros a col H. destruct a.
  - destruct f.
    + simpl in H. discriminate.
    + simpl in H. apply H.
  - simpl in H. apply H.
Qed.

Lemma some_nan_refl: 
 ~ (Some Nan <> Some Nan).
Proof.
  intros contra. assert (H: Some Nan = Some Nan).
  - reflexivity.
  - apply contra in H. apply H.
Qed.

(** For a column that doesn't have nan,
  the cuDFmax never returns nan
  *)
Lemma cuDFmax_no_Nan_to_not_Nan: forall col,
  hasNan col = false -> cuDFmax col <> Some Nan.
Proof.
  intros col. induction col.
  - intros _ contra. discriminate.
  - intros H contra. destruct a.
    + destruct f.
      * discriminate H.
      * apply derive_not_has_nan in H.
        apply IHcol in H.
        unfold cuDFmax in contra.
        simpl in contra.
        remember (cuDFmax col) as e.
        destruct e eqn: H1.
        -- unfold cuDFmax in Heqe.
          rewrite <- Heqe in contra.
          destruct f.
          ++ apply some_nan_refl in H. destruct H.
          ++ discriminate.
        --unfold cuDFmax in Heqe.
          rewrite <- Heqe in contra.
          discriminate.
    + simpl in H. apply IHcol in H.
      unfold cuDFmax in contra. simpl in contra.
      apply H in contra. destruct contra.
Qed.

Lemma GPUmax_is_Nan_hasNan_refl: forall col,
  GPUmax col = Some Nan <-> hasNan col = true.
Proof.
  intros col. split.
  - intros H. unfold GPUmax in H.
    destruct (hasNan col) eqn:E.
    + reflexivity.
    + apply cuDFmax_no_Nan_to_not_Nan in E.
      apply E in H. destruct H.
  - intros H. unfold GPUmax. rewrite H. reflexivity.
Qed. 

Lemma GPUmax_not_Nan_not_hasNan_refl: forall col,
  GPUmax col <> Some Nan <-> hasNan col = false.
Proof.
  intros col. split.
  - intros H. rewrite GPUmax_is_Nan_hasNan_refl in H. 
    apply not_true_is_false. apply H.
  - intros H. unfold GPUmax. rewrite H.
    apply cuDFmax_no_Nan_to_not_Nan. apply H.
Qed.

Lemma cuDFmax_append_None_no_effect: forall col,
  cuDFmax (None::col) = cuDFmax col.
Proof.
  intros col. unfold cuDFmax. simpl. reflexivity.
Qed.

Lemma GPUmax_append_None_no_effect: forall col,
  GPUmax (None::col) = GPUmax col.
Proof.
  intros col. unfold GPUmax. simpl.
  rewrite cuDFmax_append_None_no_effect. reflexivity.
Qed.

Theorem cpu_gpu_max_eq: forall (col: list (option float)),
  CPUmax col = GPUmax col.
Proof.
  intros col. induction col.
  - reflexivity.
  - destruct a.
    + destruct f.
      * unfold CPUmax. simpl. 
        destruct (CPUmax col) eqn:E.
        -- unfold CPUmax in E. rewrite E.
          unfold GPUmax. simpl. reflexivity.
        -- unfold CPUmax in E. rewrite E.
          unfold GPUmax. simpl. reflexivity.
      * unfold CPUmax. simpl.
        destruct (CPUmax col) eqn:E.
        -- unfold CPUmax in E.
          rewrite E. destruct f.
          ++ unfold GPUmax.
            symmetry in IHcol.
            apply GPUmax_is_Nan_hasNan_refl in IHcol.
            simpl. rewrite IHcol. reflexivity.
          ++ unfold GPUmax. simpl.
            assert (H: GPUmax col <> Some Nan).
            ** intros contra. rewrite <- IHcol in contra.
              discriminate contra.
            ** apply GPUmax_not_Nan_not_hasNan_refl in H.
              rewrite H. unfold GPUmax in IHcol.
              rewrite H in IHcol.
              unfold cuDFmax. simpl.
              unfold cuDFmax in IHcol.
              rewrite <- IHcol. reflexivity.
        -- unfold CPUmax in E. rewrite E.
          unfold GPUmax. simpl.
          assert (H: GPUmax col <> Some Nan).
          ++ intros contra. rewrite contra in IHcol. discriminate.
          ++ apply GPUmax_not_Nan_not_hasNan_refl in H.
            rewrite H. unfold cuDFmax. simpl.
            unfold GPUmax in IHcol.
            rewrite H in IHcol. unfold cuDFmax in IHcol.
            rewrite <- IHcol. reflexivity.
    + rewrite GPUmax_append_None_no_effect.
      rewrite <- IHcol. unfold CPUmax. reflexivity.
Qed.