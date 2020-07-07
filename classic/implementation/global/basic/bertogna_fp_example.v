Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform.
Require Import prosa.classic.analysis.global.basic.workload_bound
               prosa.classic.analysis.global.basic.interference_bound_fp
               prosa.classic.analysis.global.basic.bertogna_fp_comp.
Require Import prosa.classic.implementation.job prosa.classic.implementation.task
               prosa.classic.implementation.arrival_sequence.
Require Import prosa.classic.implementation.global.basic.schedule.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Module ResponseTimeAnalysisFP.

  Import Job Schedule SporadicTaskset Priority Schedulability Platform InterferenceBoundFP WorkloadBound ResponseTimeIterationFP.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler.

  (* In this section, we instantiate a simple example to show that the theorems
     contain no contradictory assumptions. *)
  Section ExampleRTA.

    Let tsk1 := {| task_id := 1; task_cost := 2; task_period := 5; task_deadline := 3|}.
    Let tsk2 := {| task_id := 2; task_cost := 4; task_period := 6; task_deadline := 5|}.
    Let tsk3 := {| task_id := 3; task_cost := 3; task_period := 12; task_deadline := 11|}.

    (* Let ts be a task set containing these three tasks (sorted by rate-monotonic priority). *)
    Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _.

    Section FactsAboutTaskset.

      Fact ts_has_valid_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.
      Proof.
        intros tsk IN.
        repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
      Qed.

      Fact ts_has_constrained_deadlines:
        forall tsk,
          tsk \in ts ->
          task_deadline tsk <= task_period tsk.
      Proof.
        intros tsk IN.
        repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
      Qed.
      
    End FactsAboutTaskset.

    (* Assume there are two processors. *)
    Let num_cpus := 2.

    (* Recall the FP RTA schedulability test. *)
    Let schedulability_test :=
      fp_schedulable task_cost task_period task_deadline num_cpus.

    (* Now we show that the schedulability test returns true. *)
    Fact schedulability_test_succeeds :
      schedulability_test ts = true.
    Proof.
      unfold schedulability_test, fp_schedulable, fp_claimed_bounds; simpl.
      unfold total_interference_bound_fp, div_floor.
      rewrite big_nil div0n addn0 /=.
      unfold div_floor; simpl.
      set I2 := total_interference_bound_fp task_cost task_period tsk2
                                            [:: (tsk1, 2)].
      assert (H1: I2 4 = 1).
      {
        by unfold I2, total_interference_bound_fp; rewrite big_cons big_nil; compute.
      }
      rewrite H1.
      have H2: 4 + 1 %/ num_cpus = 4 by compute.
      rewrite H2 H1 H2.
      have H3: 3 < 5 by compute.
      rewrite H3.
      unfold fp_bound_of_task.
      have H4: per_task_rta task_cost task_period num_cpus tsk3 [:: (tsk1, 2); (tsk2, 4)]
                            (max_steps task_cost task_deadline tsk3) = 5.
      {
        unfold per_task_rta; simpl.
        unfold total_interference_bound_fp at 9.
        rewrite !big_cons big_nil /=.
        unfold total_interference_bound_fp at 8.
        rewrite !big_cons big_nil /=.
        unfold total_interference_bound_fp at 7.
        rewrite !big_cons big_nil /=.
        unfold total_interference_bound_fp at 6.
        rewrite !big_cons big_nil /=.
        unfold total_interference_bound_fp at 5.
        rewrite !big_cons big_nil /=.
        unfold total_interference_bound_fp at 4.
        rewrite !big_cons big_nil /=.
        unfold total_interference_bound_fp at 3.
        rewrite !big_cons big_nil /=.
        unfold total_interference_bound_fp at 2.
        rewrite !big_cons big_nil /=.
        unfold total_interference_bound_fp at 1.
        by rewrite !big_cons big_nil /=; compute.
      }
      by rewrite H4.
    Qed.

    (* Let arr_seq be the periodic arrival sequence from ts. *)
    Let arr_seq := periodic_arrival_sequence ts.

    (* Assume rate-monotonic priorities. *)
    Let higher_priority := FP_to_JLDP job_task (RM task_period).

    Section FactsAboutPriorityOrder.

      Lemma ts_has_unique_priorities :
        FP_is_antisymmetric_over_task_set (RM task_period) ts.
      Proof.
        unfold RM; intros tsk tsk' IN IN' HP HP'.
        have EQ: task_period tsk = task_period tsk' by apply/eqP; rewrite eqn_leq HP HP'.
        clear HP HP'.
        rewrite !in_cons 2!in_nil 2!orbF in IN IN'; des; rewrite IN IN'; try (by done);
        subst tsk tsk'; simpl in *; by done.
      Qed.

      Lemma priority_is_total :
        FP_is_total_over_task_set (RM task_period) ts.
      Proof.
        unfold RM; intros tsk tsk' IN IN'.
        destruct (leqP (task_period tsk) (task_period tsk'));
          [by left | by right; apply ltnW].
      Qed.
      
    End FactsAboutPriorityOrder.
      
    (* Let sched be the work-conserving RM scheduler. *)
    Let sched := scheduler job_arrival job_cost num_cpus arr_seq higher_priority.

    (* Recall the definition of deadline miss. *)
    Let no_deadline_missed_by :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.

    (* Next, we prove that ts is schedulable with the result of the test. *)
    Corollary ts_is_schedulable:
      forall tsk,
        tsk \in ts ->
        no_deadline_missed_by tsk.
    Proof.
      intros tsk IN.
      have VALID := periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters.
      have TSVALID := ts_has_valid_parameters.
      unfold valid_sporadic_job, valid_realtime_job in *; des.
      apply taskset_schedulable_by_fp_rta with (task_cost := task_cost)
       (task_period := task_period) (task_deadline := task_deadline)
       (ts0 := ts) (higher_priority0 := RM task_period); try (by done).
      - by apply ts_has_constrained_deadlines.
      - by apply ts_has_unique_priorities.
      - by apply priority_is_total.
      - by apply RM_is_transitive.
      - by apply periodic_arrivals_all_jobs_from_taskset.
      - by apply periodic_arrivals_are_sporadic.
      - by apply scheduler_jobs_come_from_arrival_sequence.
      - by apply scheduler_jobs_must_arrive_to_execute.
      - apply scheduler_completed_jobs_dont_execute.
        -- by apply periodic_arrivals_are_consistent.
        -- by apply periodic_arrivals_is_a_set.
      - apply scheduler_sequential_jobs.
        -- by apply periodic_arrivals_are_consistent.
        -- by apply periodic_arrivals_is_a_set. 
      - by apply scheduler_work_conserving, periodic_arrivals_are_consistent.
      - apply scheduler_respects_policy.
        -- by apply periodic_arrivals_are_consistent.
        -- by intros t; apply RM_is_transitive.
        -- by intros t x y; apply leq_total.
      - by apply schedulability_test_succeeds.
    Qed.

  End ExampleRTA.

End ResponseTimeAnalysisFP.