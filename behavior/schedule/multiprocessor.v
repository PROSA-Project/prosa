From mathcomp Require Export fintype.
From rt.behavior.schedule Require Export schedule.

Section Schedule.

  Variable Job: eqType.
  Variable processor_state: Type.
  Context `{ProcessorState Job processor_state}.

  Definition processor (num_cpus: nat) := 'I_num_cpus.

  Variable num_cpus : nat.

  Definition identical_state := processor num_cpus -> processor_state.

  Global Instance multiproc_state : ProcessorState Job (identical_state) :=
    {
      scheduled_in j s := [exists cpu, scheduled_in j (s cpu)];
      service_in j s := \sum_(cpu < num_cpus) service_in j (s cpu)
    }.
  Proof.
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
