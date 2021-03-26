(*|
===================
A Tutorial on Prosa
===================

.. This document is compiled from a Coq file (TODO URL) using Alectryon
   `<https://github.com/cpitclaudel/alectryon>`_ by the command:
   `alectryon.py --frontend coq+rst tutorial.v --backend webpage -o
    tutorial.html`.

.. TODO: eventually add this to the CI so that this tutorial is deployed
   automatically on Prosa'website.
|*)

(*|
Introduction
============

Prosa [Prosa]_ is a framework for formulating and validating
definitions and proofs that have been developed in the context of the
real-time scheduling theory. Prosa was proposed by the MPI-SWS
institute, and the foundations of the framework have been implemented
by this group. It was first introduced in the academic setting in
2016 [prosa_paper]_. Prosa is now being improved and developed
further as part of the RT-Proofs project [rt_proofs]_.

Prosa is based on the Coq proof assistant developed by
INRIA [coq]_ and uses its functionalities to express and prove
constructs from the real-time scheduling theory.

The main motivation for Prosa is the fact that many definitions and
proofs that are available in the real-time scheduling theory are based
on intuition and lack formal steps. As such, these constructs may have
flaws. One of the most famous examples is related to the CAN bus
analysis [Davis_CAN]_. By using proof assistants, as in Prosa, the
number of flaws in the real-time scheduling theory can be
significantly reduced. Formal developments also offer other major
advantages: for instance it is easier to build on top of proofs, they
give a better understanding of assumptions and they dramatically ease
the process of trying to remove a thought useless assumption, or even
help discover them.

Therefore, it is in the common interest of the real-time community to
use proof libraries such as Prosa. To that aim, the awareness of the
real-time community regarding the existence of such tools should be
raised. In this tutorial-style document, the first user experience of
a researcher with a real-time background, but neither Coq nor Prosa
background, will be documented. The aim of this document is
twofold. First, it should help new Prosa users to become familiar with
the tool and some of its features, so as to be able to understand and
follow Prosa artifacts, as well as to be able to develop their own
Prosa extensions. Second, it should help the Prosa developers to
better understand the challenges that the new users might face, and
take that into consideration when refactoring existing and developing
new functionalities.
|*)

(*|
Getting Started
===============

In a first reading, it is possible to skip this part and go directly
to `the next one <#formulating-constructs>`_ However, for a deeper understanding of the
Prosa library, it is advisable to install the Coq system and
interactively replay the examples proposed in this document. The
current section thus provides some minimal information to get a
working Coq environment. A priori knowledge of Coq is welcome but
should not be needed to understand the current document as main
concepts will be introduced on the fly.

Installing Coq
--------------

Under Windows, the easiest solution is to resort on the `binary installer
provided on Coq's website <https://coq.inria.fr/download>`_ (although it wil
install much more than we need). On Linux or MacOS, the more versatile solution
is to use the Opam package manager and we detail below the main steps
(`more detailled instructions <https://coq.inria.fr/opam-using.html>`_
are available on Coq's website).

1. Install Opam, following `the instructions on Opam's website
   <https://opam.ocaml.org/doc/Install.html>`_

2. Check that you have Opam version 2.0.0 or above

   .. code-block:: sh

      opam --version

3. Initialize Opam

   .. code-block:: sh

      opam init
      eval $(opam env)

   `opam init` will prompt you to allow opam to set up initialization scripts,
   which is generally fine to accept. Otherwise, every time a new shell is
   opened you have to type in the `eval $(opam env)` command above
   to update environment variables. Note that this can take several minutes.

4. Install dependencies

   .. code-block:: sh

      opam install opam-depext
      opam-depext coq

   This should tell you how to install additional dependencies needed by Coq
   (if any) on your system. If needed, use the provided commands (for instance
   `sudo apt-get install m4`).

5. Install Coq

   .. code-block:: sh

      opam install coq

   This will compile Coq from source which tipically takes a few (dozen)
   minutes. You can test that Coq is properly installed by typing

   .. code-block:: sh

      coqc -v

   which should output Coq's version.

5. Install the Ssreflect library used by Prosa

   .. code-block:: sh

      opam repo add coq-released https://coq.inria.fr/opam/released
      opam install coq-mathcomp-ssreflect

Installing a Coq interface
--------------------------

Coq programs/proofs are files, with the extension `.v`, that can be compiled
by Coq compiler `coqc` but Coq proof script are usually developped in an
interactive way. Thus, one needs an editor or IDE with some Coq support.
The user of Visual Studio Code can
`install its VSCoq extension <https://github.com/coq-community/vscoq>`_
whereas Emacs' users will enjoy the
`Proof General <https://proofgeneral.github.io/>`_ mode. A `more detailled list
<https://coq.inria.fr/user-interfaces.html>`_ is available on Coq's website.

Learning about Coq
------------------

A priori knowledge of Coq should not be needed to understand the
current document. However, the reader interested in going further and
developing its own proofs will need some experience with the ssreflect tactic
language used in Prosa. A good first reading is Part1 of the
`Mathematical Components book <https://math-comp.github.io/mcb/>`_.

Getting Prosa
-------------

You can download the code of Prosa using git

.. code-block:: sh

   git clone https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs.git

Compilation then proceeds as follows

.. code-block:: sh

   ./create_makefile.sh --without-refinements
   make
   make install

Reading this Tutorial
---------------------

This tutorial is actually a Coq file that can be downloaded at (TODO
URL) so one can step through it with Coq and thus replay the examples
and experiment with them while reading the tutorial.
When Coq is installed, it is then advisable to download this file and step
through it in your editor/IDE (essential keyboard shortcuts are C-c C-n,
C-c C-u and C-c RET to go down, up ot to the cursor under Emacs,
Alt-down, Alt-up or Alt-right under VSCode).

It is first needed to load a few libraries.
|*)
From mathcomp Require Export all_ssreflect.
Require Import prosa.util.notation.

(*|
.. _formulating-constructs:

Formulating Real-time Constructs in Prosa
=========================================

In this section, an overview of the Prosa framework and some of its
core functionalities will be given. Specifically, the main focus will
be on the scheduling theory for fixed-priority tasks deployed upon
fully preemptive uniprocessors. Note that the following description
and code listings correspond to the current version of Prosa publicly
available on its `git repository
<https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/>`_.

The description of Prosa constructs will be performed in such a way
that each item will be covered *after* its constituting components
were introduced. Therefore, in this tutorial description of Prosa, we
first start with basic items, and then cover more complex ones. The
content covered should be sufficient for readers to become familiar
with Prosa, and after completing this document, readers should be able
to understand and follow other Prosa artifacts that are not covered
here. Readers interested in more advanced aspects of the scheduling
theory and their implementation in Prosa should consult the Prosa
source code itself which is highly documented in a literate
programming style.
|*)

(*|
Notion of Time
--------------

A concept of time is vital in the real-time scheduling theory, and
there exist two approaches:

1. discrete time domain, and
2. continuous time domain.

In the former approach, it is assumed
that there exists the smallest atomic unit of time (typically assigned
an integer value of 1), and all other timing constructs are specified
as multiples of that atomic unit. In the latter approach, the premise
of the atomic unit does not exist, and each process can have an
arbitrary duration.

In Prosa, a concept of time is introduced in the file `behavior/time.v
<https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/time.v>`_
rt.model.time} in which one can read
|*)
Definition duration := nat.
Definition instant  := nat.
(*|
This means the notions of duration and time instant are bot defined
as the type `nat` of natural integers from Coq standard library.

If one tries
|*)
Print nat.  (* .unfold *)
(*|
one can see that a natural number is inductively defined as `O`
or the successor `S` of a natural number. For instance, `2`
is defined as `S (S O)`.
|*)
Set Printing All.
Check 2.  (* .unfold *)
Unset Printing All.
(*|
.. note::

   The `Set Printing All` command allows to see the underlying representation,
   otherwise the much more convenient notation `2` is used.

Thus, in Prosa time is discrete (1.). At each observable moment (instant),
the time has an exact integer value. Moreover, the duration of any process
can be described as a multiple of atomic time instants, where the value
is equal to the difference between the time instant when the process
finished and the time instant when the process started.
|*)

(*|
Concrete Workload, Jobs
-----------------------

In real-time theory, and in Prosa, jobs represent an instantaneous
arrival of an amount of workload that has to be executed upon a
selected resource. In the context of the uniprocessor scheduling
theory (the focus of this tutorial), that would be a computation
performed on a processor. In Prosa, the definition is stated in
`behavior/job.v
<https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/job.v>`_.

.. note::

   In Coq syntax, everything between `(*` and `*)` is a comment,
   ignored by Coq.

This file is reproduced below.
|*)

(** * Notion of a Job Type *)

(** Throughout the library we assume that jobs have decidable equality. *)
Definition JobType := eqType.

(** * Unit of Work *)

(** We define 'work' to denote the unit of service received or needed.
   In a real system, this corresponds to the number of processor cycles. *)
Definition work  := nat.

(** * Basic Job Parameters — Cost, Arrival Time, and Absolute Deadline *)

(** Definition of a generic type of parameter relating jobs to a discrete cost. *)
Class JobCost (Job : JobType) := job_cost : Job -> work.

(** Definition of a generic type of parameter for job_arrival. *)
Class JobArrival (Job : JobType) := job_arrival : Job -> instant.

(** Definition of a generic type of parameter relating jobs to an absolute deadline. *)
Class JobDeadline (Job : JobType) := job_deadline : Job -> instant.

(*|
TODO : short explanation about Class and typeclasses

From the above listing we can see that job is an entity with several parameters:

1. `job_arrival` is the time instant when the job arrived to the system,
2. `job_cost` is the amount of time that a job requires to be fully processed
   (a computation time in the context of uniprocessors), also called the job
   execution time,
3. `job_deadline` is a deadline of a job.
|*)

(*|
Job Arrivals
------------

The arrival of jobs to the system is covered in
`behavior/arrival_sequence.v
<https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/arrival_sequence.v>`_. Of
importance is the definition of `arrival_sequence`.

Let's first introduce here the `Section` mechanism of Coq, when typing
|*)
Section ArrivalSequence.
(*|
Coq starts a `Section` (called `ArrivalSequence` here) in which one can
add variables
|*)
  (** Given any job type with decidable equality, ... *)
  Variable Job: JobType.
(*|
which can be used in further definitions in the section
|*)
  (** ..., an arrival sequence is a mapping from any time to a (finite)
      sequence of jobs. *)
  Definition arrival_sequence := instant -> seq Job.
(*|
note that currently, arrival sequence is exactly the stated definition
|*)
  Print arrival_sequence.  (* .unfold *)
(*|
At some point, the section can be closed
|*)
End ArrivalSequence.
(*|
The section variables no longer exist.
|*)
Fail Check Job.
(*|
But all objects defined in the section remain accessible as they are
automatically generalized with respect to the section variables
they refer to.
|*)
Print arrival_sequence.  (* .unfold *)
(*|
Note that `Job` is now a parameter of `arrival_sequence`.
|*)

(*|
Arrival sequences map
individual time instants to finite sequences of jobs, where each
sequence, associated to some time instant `t`, contains all jobs that
arrive at `t`. In the context of individual jobs, several definitions
are available
|*)
Section JobProperties.

  (** Consider any job arrival sequence. *)
  Context {Job: JobType}.
  Variable arr_seq: arrival_sequence Job.

  (** First, we define the sequence of jobs arriving at time t. *)
  Definition arrivals_at (t : instant) := arr_seq t.

  (** Next, we say that job j arrives at a given time t iff it belongs to the
       corresponding sequence. *)
  Definition arrives_at (j : Job) (t : instant) := j \in arrivals_at t.

  (** Similarly, we define whether job j arrives at some (unknown) time t, i.e.,
       whether it belongs to the arrival sequence. *)
  Definition arrives_in (j : Job) := exists t, j \in arrivals_at t.

End JobProperties.
(*|
TODO short explanation on Context and implicit arguments
|*)

(*|
We've seen above that a function `JobArrival` can map any job to its arrival
time, we thus need a way to state that an arrival sequence is consistent
with such a function. This is expressed by the following definitions:
|*)
Section ValidArrivalSequence.

  (** Assume that job arrival times are known. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.

  (** We say that arrival times are consistent if any job that arrives in the
     sequence has the corresponding arrival time. *)
  Definition consistent_arrival_times :=
    forall j t,
      arrives_at arr_seq j t -> job_arrival j = t.

  (** We say that the arrival sequence is a set iff it doesn't contain duplicate
     jobs at any given time. *)
  Definition arrival_sequence_uniq :=
    forall t, uniq (arrivals_at arr_seq t).

  (** We say that the arrival sequence is valid iff it is a set and arrival times
     are consistent *)
  Definition valid_arrival_sequence :=
    consistent_arrival_times /\ arrival_sequence_uniq.

End ValidArrivalSequence.
(*|
For a given `JobArrival`, one can state a few additional definitions
about individual jobs.
|*)
Section ArrivalTimeProperties.

  (** Assume that job arrival times are known. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.

  (** Let j be any job. *)
  Variable j: Job.

  (** We say that job j has arrived at time t iff it arrives at some time t_0
     with t_0 <= t. *)
  Definition has_arrived (t : instant) := job_arrival j <= t.

  (** Next, we say that job j arrived before t iff it arrives at some time t_0
     with t_0 < t. *)
  Definition arrived_before (t : instant) := job_arrival j < t.

  (** Finally, we say that job j arrives between t1 and t2 iff it arrives at
     some time t with t1 <= t < t2. *)
  Definition arrived_between (t1 t2 : instant) := t1 <= job_arrival j < t2.

End ArrivalTimeProperties.
(*|
Whereas when given an `arrival_sequence`, one can extract sequences of
jobs arriving in some time interval.
|*)
Section ArrivalSequencePrefix.

  (** Assume that job arrival times are known. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.

  (** By concatenation, we construct the list of jobs that arrived in the
     interval <<[t1, t2)>>. *)
  Definition arrivals_between (t1 t2 : instant) :=
    \cat_(t1 <= t < t2) arrivals_at arr_seq t.

  (** Based on that, we define the list of jobs that arrived up to time t, ...*)
  Definition arrivals_up_to (t : instant) := arrivals_between 0 t.+1.

  (** ... the list of jobs that arrived strictly before time t, ... *)
  Definition arrivals_before (t : instant) := arrivals_between 0 t.

  (** ... and the list of jobs that arrive in the interval <<[t1, t2)>> and
   satisfy a certain predicate [P]. *)
  Definition arrivals_between_P (P : Job -> bool) (t1 t2 : instant) :=
    [seq j <- arrivals_between t1 t2 | P j].

End ArrivalSequencePrefix.

(*|
Workload and Resource States
----------------------------

As already mentioned, jobs execute upon resources. In our uniprocessor
case, that would relate to jobs executing on a processor. Since there
may exist multiple jobs that require execution, while a processor can
provide service to only one of them, job executions must be
scheduled. In the context of job scheduling, jobs pass through
different states. For example, a job can be not released yet, or
released but without any service received from the processor yet,
fully executed, etc.

The file `behavior/schedule.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/schedule.v>`_.
defines a very generic notion of `ProcessorState` and `schedule`.
It is worth noting that a `schedule` is a function from time instants
to processor states.
|*)
Require Import prosa.behavior.schedule.

Print schedule.  (* .unfold *)
(*|
processor states returned by the schedule can then be inspected to know whether
a given job is scheduled in this state
|*)
Check scheduled_in.  (* .unfold *)
(*|
and what amount of service it is given
|*)
Check service_in.  (* .unfold *)

(*|
Equipped with this definitions, the file `behavior/service.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/service.v>`_
gives basic definitions on the service received by a job.
|*)
Section Service.

  (** * Service of a Job *)

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** First, we define whether a job [j] is scheduled at time [t], ... *)
  Definition scheduled_at (j : Job) (t : instant) := scheduled_in j (sched t).

  (** ... and the instantaneous service received by job j at time t. *)
  Definition service_at (j : Job) (t : instant) :=
    service_in j (sched t).

  (** Based on the notion of instantaneous service, we define the
      cumulative service received by job j during any interval from [t1]
      until (but not including) [t2]. *)
  Definition service_during (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) service_at j t.

  (** Using the previous definition, we define the cumulative service
      received by job [j] up to (but not including) time [t]. *)
  Definition service (j : Job) (t : instant) := service_during j 0 t.
(*|
as well as the notion of completion of a job
|*)
  (** In the following, consider jobs that have a cost, a deadline,
      and an arbitrary arrival time. *)
  Context `{JobCost Job}.
  Context `{JobDeadline Job}.
  Context `{JobArrival Job}.

  (** We say that job [j] has completed by time [t] if it received all
      required service in the interval from [0] until
      (but not including) [t]. *)
  Definition completed_by (j : Job) (t : instant) := service j t >= job_cost j.

  (** We say that job [j] completes at time [t] if it has completed
      by time [t] but not by time [t - 1]. *)
  Definition completes_at (j : Job) (t : instant) :=
    ~~ completed_by j t.-1 && completed_by j t.
(*|
of response time bound
|*)
  (** We say that a constant [R] is a response time bound of a job [j]
      if [j] has completed by [R] units after its arrival. *)
  Definition job_response_time_bound (j : Job) (R : duration) :=
    completed_by j (job_arrival j + R).

  (** We say that a job meets its deadline if it completes by
      its absolute deadline. *)
  Definition job_meets_deadline (j : Job) :=
    completed_by j (job_deadline j).
(*|
and of pending jobs
|*)
  (** Job [j] is pending at time [t] iff it has arrived
      but has not yet completed. *)
  Definition pending (j : Job) (t : instant) :=
    has_arrived j t && ~~ completed_by j t.

  (** Job [j] is pending earlier and at time [t] iff it has arrived
      before time [t] and has not been completed yet. *)
  Definition pending_earlier_and_at (j : Job) (t : instant) :=
    arrived_before j t && ~~ completed_by j t.

  (** Let's define the remaining cost of job [j] as the amount
      of service that has yet to be received for it to complete. *)
  Definition remaining_cost j t :=
    job_cost j - service j t.

End Service.
(*|
Similarly, one can find in file `behavior/ready.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/ready.v>`_
the definitions of ready and backlogged jobs
as well as a characterization of valid schedules
with respect to job arrivals costs and arrival sequences.
|*)

(*|
First Lemmas
------------

Based on the previous definitions, some lemmas can be proved.
Prosa indeed proves a lot of more or less basic lemmas.
we only present here one such simple lemma from the file
`analysis/facts/behavior/service.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/analysis/facts/behavior/service.v>`_
|*)
Require Import prosa.analysis.facts.behavior.service.

(** We establish a basic fact about the monotonicity of service. *)
Section Monotonicity.

  (** Consider any job type and any processor model. *)
  Context {Job: JobType}.
  Context {PState: Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any given schedule... *)
  Variable sched: schedule PState.

  (** ...and a given job that is to be scheduled. *)
  Variable j: Job.

  (** We observe that the amount of service received is monotonic by definition. *)
  Lemma service_monotonic:
    forall t1 t2,
      t1 <= t2 ->
      service sched j t1 <= service sched j t2.
  Proof.
    move=> t1 t2 let1t2.
    rewrite -(service_cat _ _ t1 t2) //.
    exact: leq_addr.
  Qed.

End Monotonicity.
(*|
The three lines between `Proof` and `Qed` can be ignored for now.
The instruct Coq how to perform the proof of the previously stated lemma.
The only thing to notice is that this proof is terminated by a `Qed`
(for the latin "words Quod Erat Demonstrandum") meaning that,
if Coq can compile the `Qed` it managed to check the proof and the new lemma
is now available for use in future proofs.
|*)

(*|
Job Properties
--------------

TODO: retrieve/update material from Borislav's document on fixed priority policy and EDF
|*)

(*|
Platform
--------

TODO: retrieve/update material from Borislav's document about schedulers
|*)

(*|
Groups of Jobs
--------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Job Schedulability
------------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Busy Interval
-------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Workload Abstraction and Workload Bounds
----------------------------------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Tasks with respect to schedules, priorities, workload, service and schedulers
-----------------------------------------------------------------------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Response Time Bounds
--------------------

TODO: retrieve/update material from Borislav's document
(and maybe move here the definition that was already given much earlier)
|*)

(*|
Tasks Schedulability
--------------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Task Arrival Bounds
-------------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Workload bounds
---------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Task Response-Time Bound
------------------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
Task Response-Time Bound Computation
------------------------------------

TODO: retrieve/update material from Borislav's document

test maths :math:`\sum_{i=1}^n i^2`
|*)

(*|
Task Response-Time Bound Computation
------------------------------------

TODO: retrieve/update material from Borislav's document

should we say a few words about CERTA ?
|*)

(*|
Prosa Parts not Covered in this Document
----------------------------------------

TODO: retrieve/update material from Borislav's document
|*)

(*|
References
==========

.. [Prosa] MPI-SWS Germany. Formally proven schedulability analysis PROSA. http://prosa.mpi-sws.org/

.. [prosa_paper] F. Cerqueira, F. Stutz, and B. B. Brandenburg. PROSA: A Case for Readable Mechanized Schedulability Analysis. In ECRTS 2016, 2016.

.. [coq] Inria France. The Coq Proof Assistant. http://coq.inria.fr/

.. [Davis_CAN] Robert I. Davis, Alan Burns, Reinder J. Bril, and Johan J. Lukkien. Controller Area Network (CAN) schedulability analysis: Refuted, revisited and revised. Real-Time Systems, 2007.

.. [rt_proofs] INRIA, MPI-SWS, Onera, TU Braunschweig, and Verimag. RT-Proofs Formal Proofs for Real-Time Systems. Funded by ANR/DFG, 2018 - 2020. http://rt-proofs.inria.fr/
|*)
