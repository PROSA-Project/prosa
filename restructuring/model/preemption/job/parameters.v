Require Import rt.util.all.
Require Import rt.restructuring.behavior.all.

(** * Job Preemptable *)
(** There are many equivalent ways to represent preemption points of a job. *)

(** In Prosa Preemption points are represented with a predicate
    [job_preemptable] which maps a job and its progress to a boolean
    value saying whether this job is preemptable at its current point
    of execution. *)
Class JobPreemptable (Job : JobType) :=
  job_preemptable : Job -> work -> bool.

(** * Derived Parameters *) 
(** * Job Maximum and Last Non-preemptive Segment *)
(** In this section we define the notions of the maximal and the last
    non-preemptive segments. *)
Section MaxAndLastNonpreemptiveSegment.

  (**  Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.   
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.  
  
  (** It is useful to have a representation of preemption points of a
      job defined as an actual sequence of points where this job can
      be preempted. *)
  Definition job_preemption_points (j : Job) : seq work :=
    [seq ρ:work <- range 0 (job_cost j) | job_preemptable j ρ].
  
  (** Note that the conversion preserves the equivalence. *)
  Remark conversion_preserves_equivalence:
    forall (j : Job) (ρ : work),
      ρ <= job_cost j ->
      job_preemptable j ρ <-> ρ \in job_preemption_points j.
  Proof.
    intros ? ? LE. 
    case: (posnP (job_cost j)) => [ZERO|POS].
    { unfold job_preemption_points. 
      split; intros PP.
      - move: LE; rewrite ZERO leqn0; move => /eqP EQ; subst.
          by simpl; rewrite PP.
      - rewrite ZERO in PP; simpl in PP.
        destruct (job_preemptable j 0) eqn:EQ; last by done.
          by move: PP => /orP [/eqP A1| FF]; subst.
    }
    have F: job_cost j == 0 = false.
    { by apply/eqP/neqP; rewrite -lt0n. }
    split; intros PP.
    all: unfold job_preemption_points in *.
    - rewrite mem_filter; apply/andP; split; first by done.
        by rewrite mem_iota subn0 add0n //; apply/andP; split.  
    - by move: PP; rewrite mem_filter; move => /andP [PP _]. 
  Qed.
  
  (** We define a function that maps a job to the 
      sequence of lengths of its nonpreemptive segments. *)
  Definition lengths_of_segments (j : Job) := distances (job_preemption_points j).

  (** Next, we define a function that maps a job to the
     length of the longest nonpreemptive segment of job j. *)
  Definition job_max_nonpreemptive_segment (j : Job) := max0 (lengths_of_segments j).

  (** Similarly, we define a function that maps a job to the  
     length of the last nonpreemptive segment. *)
  Definition job_last_nonpreemptive_segment (j : Job) := last0 (lengths_of_segments j).

  (** We define the notion of job's run-to-completion threshold:
      run-to-completion threshold is the amount of service after which
      a job cannot be preempted until its completion. *)
  Definition job_run_to_completion_threshold (j : Job) :=
    job_cost j - (job_last_nonpreemptive_segment j - ε).
  
End MaxAndLastNonpreemptiveSegment. 
