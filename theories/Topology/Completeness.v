Require Export MetricSpaces.
Require Import Psatz.
From Coq Require Import ProofIrrelevance.

Section Completeness.

Variable X:Type.
Variable d:X->X->R.
Hypothesis d_metric: metric d.

Definition cauchy (x:nat->X) : Prop :=
  forall eps:R, eps > 0 -> exists N:nat, forall m n:nat,
    (m >= N)%nat -> (n >= N)%nat -> d (x m) (x n) < eps.

Lemma convergent_sequence_is_cauchy:
  forall (x:Net nat_DS (MetricTopology d d_metric))
    (x0:point_set (MetricTopology d d_metric)),
  net_limit x x0 -> cauchy x.
Proof.
intros.
destruct (MetricTopology_metrized X d d_metric x0).
red; intros.
destruct (H (open_ball d x0 (eps/2))) as [N].
- Opaque In. apply open_neighborhood_basis_elements. Transparent In.
  constructor.
  lra.
- constructor.
  rewrite metric_zero; trivial.
  lra.
- simpl in N.
  exists N.
  intros.
  destruct (H1 m H2).
  destruct (H1 n H3).
  apply Rle_lt_trans with (d x0 (x m) + d x0 (x n)).
  + rewrite (metric_sym _ _ d_metric x0 (x m)); trivial.
    now apply triangle_inequality.
  + lra.
Qed.

Lemma cauchy_sequence_with_cluster_point_converges:
  forall (x:Net nat_DS (MetricTopology d d_metric))
    (x0:point_set (MetricTopology d d_metric)),
  cauchy x -> net_cluster_point x x0 -> net_limit x x0.
Proof.
intros.
apply metric_space_net_limit with d.
- apply MetricTopology_metrized.
- intros.
  red; intros.
  destruct (H (eps/2)) as [N].
  + lra.
  + pose (U := open_ball d x0 (eps/2)).
    assert (open_neighborhood U x0 (X:=MetricTopology d d_metric)).
  { apply MetricTopology_metrized.
    constructor.
    lra. }
    destruct H3.
    destruct (H0 U H3 H4 N) as [m [? []]].
    simpl in H5.
    exists N; intros n ?.
    simpl in H7.
    apply Rle_lt_trans with (d x0 (x m) + d (x m) (x n)).
    * now apply triangle_inequality.
    * cut (d (x m) (x n) < eps/2).
      ** lra.
      ** now apply H2.
Qed.

Definition complete : Prop :=
  forall x:nat->X, cauchy x ->
    exists x0:X, net_limit x x0 (I:=nat_DS)
      (X:=MetricTopology d d_metric).

End Completeness.

Arguments cauchy {X}.
Arguments complete {X}.

Section closed_subset_of_complete.

Variable X:Type.
Variable d:X->X->R.
Hypothesis d_metric:metric d.
Variable F:Ensemble X.

Let FT := { x:X | In F x }.
Let d_restriction := fun x y:FT => d (proj1_sig x) (proj1_sig y).

Lemma d_restriction_metric: metric d_restriction.
Proof.
constructor; intros; try destruct x; try destruct y; try destruct z;
  try apply subset_eq_compat; apply d_metric; trivial.
Qed.

Lemma closed_subset_of_complete_is_complete:
  complete d d_metric ->
  closed F (X:=MetricTopology d d_metric) ->
  complete d_restriction d_restriction_metric.
Proof.
intros.
red; intros.
pose (y := fun n:nat => proj1_sig (x n)).
destruct (H y) as [y0].
- red; intros.
  destruct (H1 eps H2) as [N].
  now exists N.
- intros.
  assert (In F y0).
{ rewrite <- (closure_fixes_closed _ H0); trivial.
  apply @net_limit_in_closure with (I:=nat_DS) (x:=y); trivial.
  red; intros.
  exists i; split.
  - apply le_refl.
  - unfold y.
    destruct (x i); trivial. }
  exists (exist _ y0 H3).
  apply metric_space_net_limit with d_restriction.
  + apply MetricTopology_metrized.
  + intros.
    unfold d_restriction; simpl.
    apply metric_space_net_limit_converse with
      (MetricTopology d d_metric); trivial.
    apply MetricTopology_metrized.
Qed.

Lemma complete_subset_is_closed:
  complete d_restriction d_restriction_metric ->
  closed F (X:=MetricTopology d d_metric).
Proof.
intros.
cut (Included (closure F (X:=MetricTopology d d_metric)) F).
- intros.
  assert (closure F (X:=MetricTopology d d_metric) = F).
{ apply Extensionality_Ensembles.
  split; trivial; apply closure_inflationary. }
  rewrite <- H1; apply closure_closed.
- red; intros.
  assert (exists y:Net nat_DS (MetricTopology d d_metric),
    (forall n:nat, In F (y n)) /\ net_limit y x).
{ apply first_countable_sequence_closure; trivial.
  apply metrizable_impl_first_countable.
  exists d; trivial; apply MetricTopology_metrized. }
  destruct H1 as [y []].
  pose (y' := ((fun n:nat => exist _ (y n) (H1 n)) :
               Net nat_DS (MetricTopology d_restriction d_restriction_metric))).
  assert (cauchy d y).
{ apply convergent_sequence_is_cauchy with d_metric x; trivial. }
  assert (cauchy d_restriction y').
{ red; intros.
  destruct (H3 eps H4) as [N].
  exists N; intros.
  unfold d_restriction; unfold y'; simpl.
  now apply H5. }
  destruct (H _ H4) as [[x0]].
  cut (net_limit y x0 (I:=nat_DS) (X:=MetricTopology d d_metric)).
  + intros.
    assert (x = x0).
  { assert (uniqueness (net_limit y (I:=nat_DS)
                            (X:=MetricTopology d d_metric))).
  { apply Hausdorff_impl_net_limit_unique.
    apply T3_sep_impl_Hausdorff.
    apply normal_sep_impl_T3_sep.
    apply metrizable_impl_normal_sep.
    exists d; trivial.
    apply MetricTopology_metrized. }
    now apply H7. }
    now rewrite H7.
  + apply metric_space_net_limit with d.
    * apply MetricTopology_metrized.
    * exact (metric_space_net_limit_converse
        (MetricTopology d_restriction d_restriction_metric)
        d_restriction (MetricTopology_metrized _ d_restriction
                             d_restriction_metric)
        nat_DS y' (exist _ x0 i) H5).
Qed.

End closed_subset_of_complete.
