Require Export prosa.analysis.facts.behavior.service.

(** * Job Progress (or Lack Thereof) *)

(** In the following section, we define a notion of "job progress", and
    conversely a notion of a lack of progress. *)

Section Progress.
  
  (** Consider any type of jobs with a known cost... *)
  Context {Job : JobType}.
  Context `{JobCost Job}.

  (** ... and any kind of schedule. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** For a given job and a given schedule... *)
  Variable sched : schedule PState.
  Variable j : Job.

  Section NotionsOfProgress.

    (** ...and two ordered points in time... *)
    Variable t1 t2 : nat.
    Hypothesis H_t1_before_t2: t1 <= t2.

    (** ... we say that the job has progressed between the two points iff its
        total received service has increased. *)
    Definition job_has_progressed := service sched j t1 < service sched j t2.

    (** Conversely, if the accumulated service does not change, there is no
        progress. *)
    Definition no_progress := service sched j t1 == service sched j t2.

    (** We note that the negation of the former is equivalent to the latter
        definition. *)
    Lemma no_progress_equiv: ~~ job_has_progressed <-> no_progress.
    Proof.
      rewrite /job_has_progressed /no_progress.
      split.
      { rewrite -leqNgt leq_eqVlt => /orP [EQ|LT]; first by rewrite eq_sym.
        exfalso.
        have MONO: service sched j t1 <= service sched j t2
          by apply service_monotonic.
        have NOT_MONO: ~~ (service sched j t1 <= service sched j t2)
          by apply /negPf; apply ltn_geF.
        move: NOT_MONO => /negP NOT_MONO.
        contradiction. }
      { move => /eqP ->.
        rewrite -leqNgt.
        by apply service_monotonic. }
    Qed.

  End NotionsOfProgress.

  (** For convenience, we define a lack of progress also in terms of given
      reference point [t] and the length of the preceding interval of
      inactivity [delta], meaning that no progress has been made for at least
      [delta] time units. *)
  Definition no_progress_for (t : instant) (delta : duration) := no_progress (t - delta) t.

End Progress.
