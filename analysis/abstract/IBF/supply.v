Require Export prosa.analysis.abstract.abstract_rta.

(** In this module, we define _intra-supply interference_ as a kind of
    conditional interference and use it to define an _intra-supply_
    interference-bound function ([intra_IBF]). Recall that an
    interference-bound function is a function that bounds the
    interference experienced by a job of a task under analysis. This
    way, the function [intra_IBF] bounds the cumulative interference
    ignoring the interference due to a lack of supply.

    Here, the term "intra-supply" is inspired by (but not limited to)
    reservation-based schedulers, where a job only receives service
    within a corresponding reservation. Similarly, intra-supply
    interference refers to interference that occurs "inside" the time
    instances where supply is present. *)
Section IntraInterferenceBound.

  (** Consider any type of job associated with any type of tasks ... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** ... with arrival times and costs. *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Let [tsk] be any task that is to be analyzed. *)
  Variable tsk : Task.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Next, we introduce the notions of _intra-supply_ interference
      and intra-supply IBF. Using these notions, one can separate the
      interference due to the lack of supply from all the other
      sources of interference. *)

  (** We define intra-supply interference as interference conditioned
      on the fact that there is supply. That is, a job [j] experiences
      intra-supply interference at a time instant [t] if [j]
      experiences interference at time [t] _and_ there is supply at
      [t]. *)
  Definition intra_interference (j : Job) (t : instant) :=
    cond_interference (fun j t => has_supply sched t) j t.

  (** We define the cumulative intra-supply interference. *)
  Definition cumul_intra_interference j t1 t2 :=
    cumul_cond_interference (fun j t => has_supply sched t) j t1 t2.

  (** Consider an interference bound function [intra_IBF]. *)
  Variable intra_IBF : Task -> duration -> duration -> work.

  (** We say that intra-supply interference is bounded by [intra_IBF]
      iff, for any job [j] of task [tsk], cumulative _intra-supply_
      interference within the interval <<[t1, t1 + R)>> is bounded by
      [intra_IBF(tsk, A, R)].*)
  Definition intra_interference_is_bounded_by :=
    cond_interference_is_bounded_by
      arr_seq sched tsk intra_IBF
      (relative_arrival_time_of_job_is_A sched) (fun j t => has_supply sched t).

End IntraInterferenceBound.
