(** * Model of Time *)

(** Prosa is based on a discrete model of time. Thus, time is simply defined by
    the natural numbers. To aid readability, we distinguish between values of time
    that represent a duration and values of time that represent a specific
    instant. *)
Definition duration := nat.
Definition instant  := nat.
