Require Export prosa.analysis.transform.swap.
Require Export prosa.analysis.transform.prefix.
Require Export prosa.util.search_arg.
Require Export prosa.util.list.

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require Export prosa.model.processor.ideal.

(** In this file we define the transformation from any ideal uniprocessor schedule 
    into a work-conserving one. The procedure is to patch the idle allocations
    with future job allocations. Note that a job cannot be allocated before
    its arrival, therefore there could still exist idle instants between any two
    job allocations. *)
Section WCTransformation.
  
  (** Consider any type of jobs with arrival times, costs, and deadlines... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobDeadline Job}.
  
  (** ...an ideal uniprocessor schedule... *)
  Let PState := ideal.processor_state Job.
  
  (** ...and any valid job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arr_seq_valid : valid_arrival_sequence arr_seq.
  
  (** We say that a state is relevant (for the purpose of the
      transformation) if it is not idle and if the job scheduled in it
      has arrived prior to some given reference time. *)
  Definition relevant_pstate reference_time pstate :=
    match pstate with
    | None => false
    | Some j => job_arrival j <= reference_time
    end.
  
  (** In order to patch an idle allocation, we look in the future for another allocation 
      that could be moved there. The limit of the search is the maximum deadline of
      every job arrived before the given moment. *)
  Definition max_deadline_for_jobs_arrived_before arrived_before :=
    let deadlines := map job_deadline (arrivals_up_to arr_seq arrived_before)
    in max0 deadlines.
  
  (** Next, we define a central element of the work-conserving transformation
      procedure: given an idle allocation at [t], find a job allocation in the future
      to swap with. *)
  Definition find_swap_candidate sched t :=
    let order _ _ := false (* always take the first result *)
    in 
    let max_dl := max_deadline_for_jobs_arrived_before t
    in
    let search_result := search_arg sched (relevant_pstate t) order t max_dl
    in
    if search_result is Some t_swap
    then t_swap
    else t. (* if nothing is found, swap with yourself *)
  
  (** The point-wise transformation procedure: given a schedule and a
      time [t1], ensure that the schedule is work-conserving at time
      [t1]. *)
  Definition make_wc_at sched t1 :=
    match sched t1 with
    | Some j => sched (* leave working instants alone *)
    | None =>
      let
        t2 := find_swap_candidate sched t1
      in swapped sched t1 t2
    end.
  
  (** To transform a finite prefix of a given reference schedule, apply
      [make_wc_at] to every point up to the given finite horizon. *)
  Definition wc_transform_prefix sched horizon :=
    prefix_map sched make_wc_at horizon.

  (** Finally, a fully work-conserving schedule (i.e., one that is 
      work-conserving at any time) is obtained by first computing a 
      work-conserving prefix up to and including the requested time [t], 
      and by then looking at the last point of the prefix. *)
  Definition wc_transform sched t :=
    let
      wc_prefix := wc_transform_prefix sched t.+1
    in wc_prefix t.

End WCTransformation.
