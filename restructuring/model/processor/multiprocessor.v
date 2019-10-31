From mathcomp Require Export fintype.
From rt.restructuring.behavior Require Export all.

Section Schedule.

  Variable Job: JobType.
  Variable processor_state: Type.
  Context `{ProcessorState Job processor_state}.

  Definition processor (num_cpus: nat) := 'I_num_cpus.

  Variable num_cpus : nat.

  Definition identical_state := processor num_cpus -> processor_state.

  Global Program Instance multiproc_state : ProcessorState Job (identical_state) :=
    {
      scheduled_on j s (cpu : processor num_cpus) := scheduled_in j (s cpu);
      service_in j s := \sum_(cpu < num_cpus) service_in j (s cpu)
    }.
  Next Obligation.
    move: j s H0.
    move=> j s /existsP Hsched.
    apply/eqP.
    rewrite sum_nat_eq0.
    apply/forallP=>/= c.
    rewrite service_implies_scheduled//.
    case: (boolP (scheduled_in _ _))=>//= Habs.
    exfalso; apply: Hsched.
      by exists c.
  Defined.
End Schedule.
