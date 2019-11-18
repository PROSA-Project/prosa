(** * Model of Time *)

(** Prosa is based on a discrete model of time. Thus, time is simply defined by
    the natural numbers. To aid readability, we distinguish between time values
    that represent durations and time values that represent specific
    instants. *)
Definition duration := nat.
Definition instant  := nat.
