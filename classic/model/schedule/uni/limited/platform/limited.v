Require Import prosa.classic.util.all.  
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.uni.schedule. 
Require Export prosa.classic.model.schedule.uni.limited.platform.definitions.
Require Export prosa.util.nondecreasing.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Platform for models with limited preemptions *)
(** In module uni.limited.platform we introduce the notion of whether a job can be
    preempted at a given time (using a predicate can_be_preempted). In this section,
    we instantiate can_be_preempted for the model with fixed preemption points and 
    model with floating nonpreemptive regions. *)
Module ModelWithLimitedPreemptions.

  Import Job UniprocessorSchedule LimitedPreemptionPlatform.

  (* In this section, we instantiate can_be_preempted for the model with fixed preemption points and
     the model with floating nonpreemptive regions. We also prove that the definitions are correct. *)
  Section ModelsWithLimitedPreemptions.
    
    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.
        
    (* Next, consider a function that maps a job to the sequence of its preemption points. *)
    Variable job_preemption_points: Job -> seq time.

    (* In this section, we provide a set of hypotheses for the models with limited preemptions. *)
    Section Definitions.

      (* In this section, we introduce the job-level definitions.
         They are the same for both models. *)
      Section ModelWithLimitedPreemptions.
        
        (* First, we define a function that maps a job to the 
           sequence of lengths of its nonpreemptive segments. *)
        Definition lengths_of_segments j := distances (job_preemption_points j).

        (* Next, we define a function that maps a job to the
           length of the longest nonpreemptive segment of job j. *)
        Definition job_max_nps (j : Job) := max0 (lengths_of_segments j).

        (* Similarly, job_last is a function that maps a job to the  
           length of the last nonpreemptive segment. *)
        Definition job_last_nps (j : Job) := last0 (lengths_of_segments j).

        (* Next, we describe some structural properties that
           a sequence of preemption points should satisfy. *)

        (* (1) The sequence of preemption points of a job with zero cost is equal to [0; 0]. *)
        Definition job_with_zero_cost_consists_of_one_empty_segment :=
          forall j, arrives_in arr_seq j -> job_cost j = 0 -> job_preemption_points j = [::0; 0].

        (* (2) The last nonpreemptive segment of a job with positive cost cannot be empty. *)
        Definition last_segment_is_positive :=
          forall j, arrives_in arr_seq j -> job_cost j > 0 -> job_last_nps j > 0.
        
        (* (3) We also require the sequence of preemption points to contain the beginning... *)
        Definition beginning_of_execution_in_preemption_points :=
          forall j, arrives_in arr_seq j -> first0 (job_preemption_points j) = 0.

        (* ... and (4) the end of execution for any job j.*)
        Definition end_of_execution_in_preemption_points :=
          forall j, arrives_in arr_seq j -> last0 (job_preemption_points j) = job_cost j.

        (* (5) We require the sequence of preemption points to be a nondecreasing sequence. *)
        Definition preemption_points_is_nondecreasing_sequence :=
          forall (j: Job),
            arrives_in arr_seq j -> 
            nondecreasing_sequence (job_preemption_points j).

        (* Finally, we define a job-level model with limited preemptions 
           as a concatenation of the hypotheses above.  *)
        Definition limited_preemptions_job_model :=
          job_with_zero_cost_consists_of_one_empty_segment /\
          last_segment_is_positive /\ 
          beginning_of_execution_in_preemption_points /\
          end_of_execution_in_preemption_points /\
          preemption_points_is_nondecreasing_sequence.
                  
      End ModelWithLimitedPreemptions.

      (* In this section, we define the model with fixed preemption points. *)
      Section ModelWithFixedPreemptionPoints.

        (* Consider a function that maps a task to the sequence of its preemption points. *)
        Variable task_preemption_points: Task -> seq time.

        (* Similarly to job's nonpreemptive segments, we define the length of the max
           nonpreemptive segment and lenght of the last nonpreemptive segment. *)
        Definition task_last_nps tsk := last0 (distances (task_preemption_points tsk)).
        Definition task_max_nps tsk := max0 (distances (task_preemption_points tsk)).
         
        (* Consider an arbitrary task set ts. *)     
        Variable ts: list Task.

        (* Next, we describe some structural properties that
           a sequence of preemption points of task should satisfy. *)
        
        (* (1) We require the sequence of preemption points to contain the beginning... *)
        Definition task_beginning_of_execution_in_preemption_points :=
          forall tsk, tsk \in ts -> first0 (task_preemption_points tsk) = 0.

        (* ... and (2) the end of execution for any job j.*)
        Definition task_end_of_execution_in_preemption_points :=
          forall tsk, tsk \in ts -> last0 (task_preemption_points tsk) = task_cost tsk.

        (* (3) We require the sequence of preemption points 
           to be a nondecreasing sequence. *)
        Definition task_preemption_points_is_nondecreasing_sequence :=
          forall tsk, tsk \in ts -> nondecreasing_sequence (task_preemption_points tsk).

        (* (4) Next, we require the number of nonpreemptive segments of a job to be 
           equal to the number of nonpreemptive segments of its task. Note that 
           some of nonpreemptive segments of a job can have zero length, nonetheless
           the number of segments should match. *)
        Definition job_consists_of_the_same_number_of_segments_as_task :=
          forall j,
            arrives_in arr_seq j -> 
            size (job_preemption_points j) = size (task_preemption_points (job_task j)).

        (* (5) We require lengths of nonpreemptive segments of a job to be bounded 
           by lenghts of the corresponding segments of its task.  *)
        Definition lengths_of_task_segments_bound_length_of_job_segments :=
          forall j n,
            arrives_in arr_seq j -> 
            nth 0 (distances (job_preemption_points j)) n
            <= nth 0 (distances (task_preemption_points (job_task j))) n.

        (* (6) Lastly, we ban empty nonpreemptive segments for tasks. *)
        Definition task_segments_are_nonempty :=
          forall tsk n,
            (tsk \in ts) ->
            n < size (distances (task_preemption_points tsk)) ->
            ε <= nth 0 (distances (task_preemption_points tsk)) n.

        (* We define a task-level model with fixed preemption points 
           as a concatenation of the hypotheses above. *) 
        Definition fixed_preemption_points_task_model :=
          task_beginning_of_execution_in_preemption_points /\
          task_end_of_execution_in_preemption_points /\
          task_preemption_points_is_nondecreasing_sequence /\
          job_consists_of_the_same_number_of_segments_as_task /\
          lengths_of_task_segments_bound_length_of_job_segments /\
          task_segments_are_nonempty.

        (* We define the model with fixed preemption points as 
           the model with fixed preemptions points at the task-level
           and model with limited preemptions at the job-level. *)
        Definition fixed_preemption_points_model :=
          limited_preemptions_job_model /\
          fixed_preemption_points_task_model.
        
      End ModelWithFixedPreemptionPoints.
      
      (* In this section, we define the model with floating nonpreemptive regions. *)
      Section ModelWithFloatingNonpreemptiveRegions.

        (* Consider a function task_max_nps that maps a task to 
           the lenght of its max nonpreemptive segment. *)
        Variable task_max_nps: Task -> time.
        
        (* We require [task_max_nps (job_task j)] to be an upper bound 
           of the lenght of the max nonpreemptive segment of job j. *)
        Definition job_max_np_segment_le_task_max_np_segment :=
          forall (j: Job),
            arrives_in arr_seq j ->
            job_max_nps j <= task_max_nps (job_task j).

        (* We define the model with floating nonpreemptive regions as 
           the model with floating nonpreemptive regions at the task-level
           and model with limited preemptions at the job-level.  *)
        Definition model_with_floating_nonpreemptive_regions :=
          limited_preemptions_job_model /\
          job_max_np_segment_le_task_max_np_segment.        

      End ModelWithFloatingNonpreemptiveRegions.

      (* Given a list of preemption points for each job, we define the function 
         can_be_preempted for the model with limited preemptions as follows. We say 
         that job j can be preempted at time t iff the service received by j at 
         time t belongs to the list of preemptions points. *)
      Definition can_be_preempted_for_model_with_limited_preemptions (j: Job) (progr: time) :=
        progr \in job_preemption_points j.

      (* Based on the definition of the model with limited preemptions, 
         we define a schedule with limited preemptions. *)
      Definition is_schedule_with_limited_preemptions (sched: schedule Job) := 
        forall j t,
          arrives_in arr_seq j ->
          ~~ can_be_preempted_for_model_with_limited_preemptions j (service sched j t) -> 
          scheduled_at sched j t.      
      
    End Definitions.

    (* In this section, we prove correctness of the model defined by 
       function model_with_limited_preemptions. *)
    Section Lemmas.

      (* Consider any uniprocessor schedule with limited preemptions...*)
      Variable sched: schedule Job.
      Hypothesis H_is_schedule_with_limited_preemptions:
        is_schedule_with_limited_preemptions sched.

      (* ...where jobs do not execute after their completion. *)
      Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

      (* Next, we assume that preemption points are defined by the model with 
         floating nonpreemptive regions. Note that the assumptions of the
         model with floating nonpreemptive regions are a strict subset of
         the assumptions of the model with fixed preemption points. This 
         guaranties that the results below work for both models. *)
      Variable task_max_nps: Task -> time.
      Hypothesis H_limited_preemptions_job_model: limited_preemptions_job_model.
      Hypothesis H_job_max_np_segment_le_task_max_np_segment:
        job_max_np_segment_le_task_max_np_segment task_max_nps.

      (* First, we prove a few basic auxiliary lemmas. *)
      Section AuxiliaryLemmas.

        (* Consider a job j. *)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.

        (* We prove that the list of preemption points is not empty. *)
        Lemma list_of_preemption_point_is_not_empty:
          0 < size (job_preemption_points j).
        Proof.
          move: H_limited_preemptions_job_model => [EMPT [LS [BEG [END _]]]].
          move: (posnP (job_cost j)) => [ZERO|POS].
          { by specialize (EMPT j H_j_arrives ZERO); rewrite EMPT. }
          apply/negPn/negP; rewrite -eqn0Ngt; intros CONTR; move: CONTR => /eqP CONTR.
          move: (END _ H_j_arrives) => EQ.
          move: EQ; rewrite /last0 -nth_last nth_default; last by rewrite CONTR.
          intros.
            by rewrite /job_cost_positive -EQ in POS.
        Qed.

        (* We prove that 0 is a preemption point. *)
        Lemma zero_in_preemption_points: 0 \in job_preemption_points j.
        Proof.
          move: H_limited_preemptions_job_model => [EMPT [LS [BEG [END _]]]].
          move: (BEG _ H_j_arrives) => EQ.
          rewrite -EQ; clear EQ.
          rewrite /first0 -nth0. 
          apply/(nthP 0).
          exists 0.
          - by apply list_of_preemption_point_is_not_empty.
          - by done.
        Qed.

        (* Next, we prove that the cost of a job is a preemption point. *)
        Lemma job_cost_in_nonpreemptive_points: job_cost j \in job_preemption_points j.
        Proof.
          move: H_limited_preemptions_job_model => [EMPT [LS [BEG [END _]]]].
          move: (END _ H_j_arrives) => EQ.
          rewrite -EQ; clear EQ.
          rewrite /last0 -nth_last.
          apply/(nthP 0).
          exists ((size (job_preemption_points j)).-1); last by done. 
          rewrite -(leq_add2r 1) !addn1 prednK //.
            by apply list_of_preemption_point_is_not_empty.
        Qed.

        (* As a corollary, we prove that the size of the sequence of nonpreemptive points is at least 2. *)
        Corollary number_of_preemption_points_at_least_two: 2 <= size (job_preemption_points j).
        Proof.
          move: H_limited_preemptions_job_model => [EMPT [LS [BEG [END _]]]]. 
          move: (posnP (job_cost j)) => [ZERO|POS].
          { by specialize (EMPT j H_j_arrives ZERO); rewrite EMPT. }
          have EQ: 2 = size [::0; job_cost j]; first by done. 
          rewrite EQ; clear EQ.
          apply subseq_leq_size.
          rewrite !cons_uniq.
          { apply/andP; split.
            rewrite in_cons negb_or; apply/andP; split; last by done.
            rewrite neq_ltn; apply/orP; left; eauto 2.
            apply/andP; split; by done. } 
          intros t EQ; move: EQ; rewrite !in_cons.
          move => /orP [/eqP EQ| /orP [/eqP EQ|EQ]]; last by done.
          - by rewrite EQ; apply zero_in_preemption_points.
          - by rewrite EQ; apply job_cost_in_nonpreemptive_points.
        Qed.

      End AuxiliaryLemmas.
      
      (* We prove that the fixed_preemption_point_model function defines 
         a correct preemption model. *)
      Lemma model_with_fixed_preemption_points_is_correct:
        correct_preemption_model arr_seq sched can_be_preempted_for_model_with_limited_preemptions.
      Proof.
        intros j ARR; split. 
        { move => t NPP.
            by apply H_is_schedule_with_limited_preemptions. }
        { intros t NSCHED SCHED. 
          have SERV: service sched j t = service sched j t.+1.
          { rewrite -[service sched j t]addn0 /service /service_during; apply/eqP. 
            rewrite big_nat_recr //=.
            rewrite eqn_add2l eq_sym.
              by rewrite /service_at eqb0. }
          rewrite -[can_be_preempted_for_model_with_limited_preemptions _ _]Bool.negb_involutive.
          apply/negP; intros CONTR.
          move: NSCHED => /negP NSCHED; apply: NSCHED.
          apply H_is_schedule_with_limited_preemptions; first by done.
            by rewrite SERV.
        }            
      Qed.

      (* Next we prove that the fixed_preemption_point_model function defines 
         a model with bounded nonpremtive regions. *)
      Lemma model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions:
        model_with_bounded_nonpreemptive_segments
          job_cost job_task arr_seq can_be_preempted_for_model_with_limited_preemptions
          job_max_nps task_max_nps. 
      Proof.
        intros j ARR.
        move: H_limited_preemptions_job_model => [EMPT [LS [BEG [END NDEC]]]].
        move: (posnP (job_cost j)) => [ZERO|POS]. 
        { specialize (EMPT j ARR ZERO).
          split; last split; last split.
          - by rewrite /job_cannot_become_nonpreemptive_before_execution /can_be_preempted_for_model_with_limited_preemptions EMPT.
          - by rewrite /job_cannot_be_nonpreemptive_after_completion /can_be_preempted_for_model_with_limited_preemptions EMPT ZERO.
          - by intros _; rewrite /job_max_nps /lengths_of_segments EMPT /distances; simpl; rewrite subn0. 
          - move => progr; rewrite ZERO leqn0; move => /andP [_ /eqP LE].
            exists 0; rewrite LE; split.
            + by apply/andP; split.
            + by rewrite /can_be_preempted_for_model_with_limited_preemptions EMPT.
        }
        split; last split; last split.
        { by rewrite /job_cannot_become_nonpreemptive_before_execution; eauto; apply zero_in_preemption_points. }
        { by apply job_cost_in_nonpreemptive_points. }
        { by intros ARR2; apply H_job_max_np_segment_le_task_max_np_segment. } 
        { unfold nonpreemptive_regions_have_bounded_length, can_be_preempted_for_model_with_limited_preemptions.
          move => progr /andP [_ LE]. 
          specialize (NDEC j).
          specialize (H_is_schedule_with_limited_preemptions j).
          destruct (progr \in job_preemption_points j) eqn:NotIN.
          { exists progr; split; first apply/andP; first split; try done.
              by rewrite leq_addr. 
          }
          set (preemptions := job_preemption_points j).
          set (serv := progr).
          have Fact1: job_cost j <= last0 preemptions. 
          { by apply last_is_max_in_nondecreasing_seq; eauto 2; apply job_cost_in_nonpreemptive_points. }
          have Fact2: first0 preemptions <= serv < last0 preemptions.
          { apply/andP; split.
            - by rewrite /preemptions BEG.
            - rewrite /serv /preemptions END; last by done.
              rewrite ltn_neqAle; apply/andP; split; last by done.
              apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
              rewrite CONTR in NotIN.
              move: NotIN => /eqP; rewrite eqbF_neg; move => /negP NIN; apply: NIN.
                by apply job_cost_in_nonpreemptive_points.
          }
          have EX: exists n,
              n.+1 < size preemptions /\
              nth 0 preemptions n < serv < nth 0 preemptions n.+1.
          { intros.
            move: (belonging_to_segment_of_seq_is_total
                     preemptions serv (number_of_preemption_points_at_least_two _ ARR) Fact2) => [n [SIZE2 /andP [N1 N2]]].
            exists n; split; first by done.
            apply/andP; split; last by done.
            move: N1; rewrite leq_eqVlt; move => /orP [/eqP EQ | G]; last by done.
            exfalso.
            move: NotIN => /negP CONTR; apply: CONTR.
            unfold serv, fixed_preemption_points_model in *.
            rewrite -EQ; clear EQ.
            rewrite mem_nth //.
              by apply ltnW.
          }
          move: EX => [x [SIZE2 /andP [N1 N2]]].
          set ptl := nth 0 preemptions x.
          set ptr := nth 0 preemptions x.+1.
          exists ptr.
          split.
          { apply/andP; split.
            { by apply ltnW. } 
            {
              apply leq_trans with (ptl + (job_max_nps j - ε) + 1).
              { unfold job_max_nps.
                rewrite -addnA -leq_subLR.
                rewrite -(leq_add2r 1).
                rewrite [in X in _ <= X]addnC -leq_subLR.                
                rewrite !subn1 !addn1 prednK. 
                { by rewrite -[_.+1.-1]pred_Sn; apply distance_between_neighboring_elements_le_max_distance_in_seq. }
                { apply max_distance_in_nontrivial_seq_is_positive; first by eauto 2.
                  exists 0, (job_cost j); repeat split. 
                  - by apply zero_in_preemption_points.
                  - by apply job_cost_in_nonpreemptive_points.
                  - apply/eqP; rewrite eq_sym -lt0n. 
                      by apply POS.
                } 
              } 
              { rewrite addn1. rewrite ltn_add2r. apply N1. }
            }
          }
          { by apply mem_nth. }
        }         
      Qed. 

    End Lemmas. 
      
  End ModelsWithLimitedPreemptions.
 
End ModelWithLimitedPreemptions.