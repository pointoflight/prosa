Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.schedule.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path finfun.

Module ScheduleConstruction.

  Import Job ArrivalSequence UniprocessorSchedule.

 (* In this section, we construct a schedule recursively by augmenting prefixes. *)
  Section ConstructionFromPrefixes.
    
    Context {Job: eqType}.

    (* Let arr_seq be any arrival sequence.*)
    Variable arr_seq: arrival_sequence Job.

    (* Assume we are given a function that takes an existing schedule prefix
       up to interval [0, t) and returns what should be scheduled at time t. *)
    Variable build_schedule:
      schedule Job -> time -> option Job.

    (* Then, starting from a base schedule, ... *)
    Variable base_sched: schedule Job.

    (* ...we can update individual times using the build_schedule function, ... *)
    Definition update_schedule (prev_sched: schedule Job)
                               (t_next: time) : schedule Job :=
      fun t =>
        if t == t_next then
          build_schedule prev_sched t
        else prev_sched t.

    (* ...which recursively generates schedule prefixes up to time t_max. *)
    Fixpoint schedule_prefix (t_max: time) : schedule Job :=
      if t_max is t_prev.+1 then
        update_schedule (schedule_prefix t_prev) t_prev.+1
      else
        update_schedule base_sched 0.

    (* Based on the schedule prefixes, we construct a complete schedule. *)
    Definition build_schedule_from_prefixes := fun t => schedule_prefix t t.

    (* In this section, we prove some lemmas about the construction. *)
    Section Lemmas.

      (* Let sched be the generated schedule. *)
      Let sched := build_schedule_from_prefixes.

      (* First, we show that the scheduler preserves its prefixes. *)
      Lemma prefix_construction_same_prefix:
        forall t t_max,
          t <= t_max ->
          schedule_prefix t_max t = sched t.
      Proof.
        intros t t_max LEt.
        induction t_max;
          first by rewrite leqn0 in LEt; move: LEt => /eqP EQ; subst.
        rewrite leq_eqVlt in LEt.
        move: LEt => /orP [/eqP EQ | LESS]; first by subst.
        {
          feed IHt_max; first by done.
          unfold schedule_prefix, update_schedule at 1.
          assert (FALSE: t == t_max.+1 = false).
          {
            by apply negbTE; rewrite neq_ltn LESS orTb.
          } rewrite FALSE.
          by rewrite -IHt_max.
        }
      Qed.

      Section ServiceDependent.
        
        (* If the generation function only depends on the service
         received by jobs during the schedule prefix, ...*)
        Hypothesis H_depends_only_on_service:
          forall sched1 sched2 t,
            (forall j, service sched1 j t = service sched2 j t) ->          
            build_schedule sched1 t = build_schedule sched2 t.

        (* ...then we can prove that the final schedule, at any time t,
         is exactly the result of the construction function. *)
        Lemma service_dependent_schedule_construction:
          forall t,
            sched t = build_schedule sched t.
        Proof.
          intros t.
          feed (prefix_construction_same_prefix t t); [by done | intros EQ].
          rewrite -{}EQ.
          induction t as [t IH] using strong_ind.
          destruct t.
          {
            rewrite /= /update_schedule eq_refl.
            apply H_depends_only_on_service.
              by intros j; rewrite /service /service_during big_geq // big_geq //.
          }
          {
            rewrite /= /update_schedule eq_refl.
            apply H_depends_only_on_service.
            intros j; rewrite /service /service_during.
            rewrite big_nat_recr //= big_nat_recr //=; f_equal.
            apply eq_big_nat; move => i /= LT.
            rewrite /service_at /scheduled_at.
              by rewrite prefix_construction_same_prefix; last by apply ltnW.
          }
        Qed.

      End ServiceDependent.

      Section PrefixDependent.

        (* If the generation function only depends on the schedule prefix, ... *)
        Hypothesis H_depends_only_on_prefix:
          forall (sched1 sched2: schedule Job) t,
            (forall t0, t0 < t -> sched1 t0 = sched2 t0) ->          
            build_schedule sched1 t = build_schedule sched2 t.

        (* ...then we can prove that the final schedule, at any time t,
         is exactly the result of the construction function. *)
        Lemma prefix_dependent_schedule_construction:
          forall t, sched t = build_schedule sched t.
        Proof.
          intros t.
          feed (prefix_construction_same_prefix t t); [by done | intros EQ].
          rewrite -{}EQ.
          induction t using strong_ind.
          destruct t.
          {
            rewrite /= /update_schedule eq_refl.
            apply H_depends_only_on_prefix.
            by intros t; rewrite ltn0.
          }
          {
            rewrite /= /update_schedule eq_refl.
            apply H_depends_only_on_prefix.
            intros t0 LT.
            by rewrite prefix_construction_same_prefix.
          }
        Qed.

      End PrefixDependent.

      Section ImmediateProperty.

        Variable P: option Job -> Prop.

        Hypothesis H_immediate_property:
          forall sched_prefix t, P (build_schedule sched_prefix t).

        Lemma immediate_property_of_schedule_construction:
          forall t, P (sched t).
        Proof.
          destruct t.
          {
            rewrite /sched /build_schedule_from_prefixes /schedule_prefix /update_schedule eq_refl.
            by apply H_immediate_property.
          }
          {
            rewrite /sched /build_schedule_from_prefixes /schedule_prefix /update_schedule eq_refl.
            by apply H_immediate_property.
          }
        Qed.

      End ImmediateProperty.

    End Lemmas.
      
  End ConstructionFromPrefixes.

End ScheduleConstruction.