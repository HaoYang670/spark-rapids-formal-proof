Require Export Coq.ZArith.BinInt.
Require Export  Coq.Bool.Bool.
Require Export Coq.Lists.List.

Infix "*" := Z.mul.
Infix ">=?" := Z.geb (at level 70, no associativity).
Notation "- x" := (Z.opp x).

Inductive float :=
  | Nan
  | Others.

(* Nan >= Others *)
Definition CPUge (f1 f2: float): bool := 
  match f1, f2 with
  | Nan, _ => true
  | _, Nan => false
  | Others, Other => true
  end. 

Lemma CPU_Nan_ge_Nan: forall f, 
  CPUge f Nan = true -> f = Nan.
Proof.
  intros f H. destruct f.
  - reflexivity.
  - discriminate.
Qed.

(* Comparision with Nan always leads to false*)
Definition cuDFge (f1 f2: float): bool := 
  match f1, f2 with
  | Nan, _ => false
  | _, Nan => false
  | Others, Others => true
  end.

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

Lemma isNan_refl: forall f,
  isNan f = true <-> f = Some Nan.
Proof.
  intros f. split.
  - intros H. destruct f.
    + destruct f.
      * reflexivity.
      * discriminate.
    + discriminate.
  - intros H. rewrite H. reflexivity.  
Qed.

Lemma notNan_refl: forall f,
  isNan f = false <-> f = Some Others.
Proof.
  Admitted.

Fixpoint hasNan col := 
  match col with
  | nil => false
  | Some Nan :: _ => true
  | _ :: s => hasNan s
  end.

Lemma derive_not_has_nan: forall a col,
  hasNan (a::col) = false -> hasNan col = false.
Proof.
  intros a col H. destruct a.
  - destruct f.
    + simpl in H. discriminate.
    + simpl in H. apply H.
  - simpl in H. apply H.
Qed.

Definition GPUmax col :=
  match (hasNan col) with
  | true => Some(Nan)
  | false => cuDFmax col
  end.

Lemma some_nan_refl: 
 ~ (Some Nan <> Some Nan).
Proof.
  intros contra. assert (H: Some Nan = Some Nan).
  - reflexivity.
  - apply contra in H. apply H.
Qed.

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

Lemma GPU_max_Nan_to_has_Nan: forall col,
  GPUmax col = Some Nan -> hasNan col = true.
Proof.
  intros col H. unfold GPUmax in H.
  destruct (hasNan col) eqn:E.
  - reflexivity.
  - apply cuDFmax_no_Nan_to_not_Nan in E.
    apply E in H. destruct H.
Qed. 

Lemma GPUmax_not_Nan_to_no_Nan: forall col,
  GPUmax col <> Some Nan -> hasNan col = false.
Proof.
  intros col H. unfold GPUmax in H.
  destruct (hasNan col).
  - apply some_nan_refl in H. destruct H.
  - reflexivity.
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
            apply GPU_max_Nan_to_has_Nan in IHcol.
            simpl. rewrite IHcol. reflexivity.
          ++ unfold GPUmax. simpl.
            assert (H: GPUmax col <> Some Nan).
            ** intros contra. rewrite <- IHcol in contra.
              discriminate contra.
            ** apply GPUmax_not_Nan_to_no_Nan in H.
              rewrite H. unfold GPUmax in IHcol.
              rewrite H in IHcol.
              unfold cuDFmax. simpl.
              unfold cuDFmax in IHcol.
              rewrite <- IHcol. reflexivity.
        -- unfold CPUmax in E. rewrite E.
          unfold GPUmax. simpl.
          assert (H: GPUmax col <> Some Nan).
          ++ intros contra. rewrite contra in IHcol. discriminate.
          ++ apply GPUmax_not_Nan_to_no_Nan in H.
            rewrite H. unfold cuDFmax. simpl.
            unfold GPUmax in IHcol.
            rewrite H in IHcol. unfold cuDFmax in IHcol.
            rewrite <- IHcol. reflexivity.
    + rewrite GPUmax_append_None_no_effect.
      rewrite <- IHcol. unfold CPUmax. reflexivity.
Qed.




