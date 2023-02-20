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

.. contents::

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

Real-Time specialists not familiar with Coq constitute the main audience
of this document. A priori knowledge of Coq is welcome but
should not be needed to understand the document as main
concepts will be introduced on the fly.
It should also be of interest for readers acquainted
to Coq but with less knowledge about real-time, although this is not
the main audience.
|*)

(*|
How to read this tutorial
=========================

This tutorial can be comfortably read as a webpage. However, Coq being
an interactive theorem prover, there is no better way to become
acquainted with it than actually interacting with the system. This
tutorial itself is a proper Coq file (available at
`<https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/tutorial/doc/tutorial.v>`_
(TODO update URL once merged)) and the
reader is advised to step through it with Coq. The next section thus provides
guidance to install and run the Coq system.
In a first reading, it is then possible to skip this part and go
directly to `the next one <#architecture>`_.
|*)

(*|
Getting Started
===============

The current section provides some minimal information to get a
working Coq environment.

Installing Coq
--------------

The easiest solution is to resort on the binary installers/packages
provided by the `Coq platform <https://coq.inria.fr/download>`_
for Linux, MacOS and Windows. This will install both Coq
and some common libraries, including all Prosa dependencies.

TODO: see whether we need to recommend installing Msys2 on Windows.

Installing a Coq interface
--------------------------

Coq programs/proofs are files, with the extension `.v`, that can be compiled
by the Coq compiler `coqc` but Coq proof scripts are usually developped in an
interactive way. Thus, one needs an editor or IDE with some Coq support.
The user of Visual Studio Code can install its
`VSCoq extension <https://github.com/coq-community/vscoq#readme>`_
whereas Emacs' users will enjoy the
`Proof General <https://proofgeneral.github.io/>`_ mode.
Users not familiar with any of these editors can simply rely on the `coqide`
tool installed by the Coq platform. A `more detailled list of interfaces
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

Stepping through this Tutorial
------------------------------

This tutorial is actually a Coq file that can be found in the `doc/tutorial.v`
file of Prosa's sources (as downloaded by the git command just above).
So one can step through it with Coq and thus replay the examples
and experiment with them while reading the tutorial.
Once Coq is installed, it is then advisable to download this file and step
through it in your editor/IDE (essential keyboard shortcuts are C-c C-n,
C-c C-u and C-c RET to go down, up ot to the cursor under Emacs,
Alt-down, Alt-up or Alt-right under VSCode).

It is first needed to load a few libraries.
|*)
From mathcomp Require Import all_ssreflect. (* .in *)
Require Import prosa.util.notation. (* .in *)

(*|
.. _architecture:

Architecture of Prosa
=====================

The code of the Prosa library is split in a few main directories:

* `behavior/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/behavior>`_
  defines the behavior of real-time systems, as used in the remaining
  of the library. This set of basic definitions is meant to remain as
  small as possible and will be exhaustively covered in the
  behavior_ Section below.
* `model/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/model>`_
  provides common specifications used by the real-time analyses proved
  in the remaining of the library. This is already larger and will
  be partially covered in the model_ Section below.
  Enough will be presented for this document to remain self contained.
* `analysis/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis>`_
  contains the proofs of real-time analyses themselves. This contains
  a lot of often very generic results.
* `results/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/results>`_
  instantiates some of the above results in well known settings.
  That's the place to look to understand what kind of results are in Prosa
  or find your favorite analysis. The current document will focus on
  a specific analysis, namely fixed priority tasks on a fully preemptive
  uniprocessor.
* `implementation/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/implementation>`_
  instantiates the above results for concrete inputs.
* `util/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/util>`_
  contains generic mathematical results useful in the remaining
  of the library.

Note that the following description
and code listings correspond to the current version of Prosa publicly
available on its `git repository
<https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/>`_.

|*)

(*|
.. _behavior:

Behavior
========

The `behavior/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/behavior>`_
directory of Prosa defines the behavior of real-time systems, as used
in the remaining of the library. This set of basic definitions is meant
to remain as small as possible, thus we exhaustively cover it here.

Notion of Time
--------------

A concept of time is vital in the real-time scheduling theory, and
there exist two approaches:

1. discrete time domain, and
2. continuous time domain.

In the former approach, it is assumed
a smallest atomic unit of time (typically assigned
an integer value of 1), and all other timing constructs are specified
as multiples of that atomic unit. In the latter approach, the premise
of the atomic unit does not exist, and each process can have an
arbitrary duration.

In Prosa, a concept of time is introduced in the file `behavior/time.v
<https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/time.v>`_
in which one can read
|*)
Definition duration := nat.
Definition instant  := nat.
(*|
This means the notions of duration and time instant are both defined
as the type `nat` of natural integers from the Coq standard library.

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

Thus, in Prosa, time is discrete (1.). At each observable moment (instant),
the time has an exact integer value. Moreover, the duration of any process
can be described as a multiple of atomic time instants, where the value
is equal to the difference between the time instant when the process
finished and the time instant when the process started.
|*)

(*|
Jobs
----

In real-time theory, and in Prosa, jobs represent an instantaneous
arrival of an amount of workload that has to be executed upon a
selected resource. In the context of the uniprocessor scheduling
theory (the focus of this tutorial), that would be a computation
performed on a processor. In Prosa, the definition is stated in
`behavior/job.v
<https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/job.v>`_.

.. note::

   In Coq syntax, everything between ``(*`` and ``*)`` is a comment,
   ignored by Coq.

This file is reproduced below.
|*)

(** * Notion of a Job Type *)

(** Throughout the library we assume that jobs
    have decidable equality. *)
Definition JobType := eqType.

(** * Notion of Work *)

(** We define 'work' to denote the unit of service received or needed.
    In a real system, this corresponds to the number
    of processor cycles. *)
Definition work  := nat.

(** * Basic Job Parameters — Cost, Arrival Time,
    and Absolute Deadline *)

(** Definition of a generic type of parameter relating jobs
    to a discrete cost. *)
Class JobCost (Job : JobType) := job_cost : Job -> work.

(** Definition of a generic type of parameter for job_arrival. *)
Class JobArrival (Job : JobType) := job_arrival : Job -> instant.

(** Definition of a generic type of parameter relating jobs
    to an absolute deadline. *)
Class JobDeadline (Job : JobType) := job_deadline : Job -> instant.

(*|
From the above listing we can see that job is an entity with several parameters:

1. `job_arrival` is the time instant when the job arrived to the system,
2. `job_cost` is the amount of time that a job requires to be fully processed
   (a computation time in the context of uniprocessors), also called the job
   execution time,
3. `job_deadline` is a deadline of a job.

.. note::

   The `Class` syntax is a Coq mechanism to declare
   `typeclasses <https://coq.inria.fr/distrib/current/refman/addendum/type-classes.html>`_.
   Without entering into too much details, it enables to define generic
   definitions (like the `job_cost` function of type `Job -> Work` above)
   for which we could later provide or assume specific `Instance` s
   (for a given `JobType` for instance).
   The system will then automatically instantiate the generic definitions
   with the instances lying around.
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
Coq starts a `Section` (called `ArrivalSequence` here, but that name
only serves a documentation purpose) in which one can
add variables
|*)
  (** Given any job type with decidable equality, ... *)
  Variable Job : JobType.
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
This `Section` mechanism is extensively used in Prosa to share
common variables between multiple definitions.
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
  Context {Job : JobType}.
  Variable arr_seq : arrival_sequence Job.

  (** First, we define the sequence of jobs arriving at time t. *)
  Definition arrivals_at (t : instant) := arr_seq t.

  (** Next, we say that job j arrives at a given time t
      iff it belongs to the corresponding sequence. *)
  Definition arrives_at (j : Job) (t : instant) := j \in arrivals_at t.

  (** Similarly, we define whether job j arrives at some (unknown)
      time t, i.e., whether it belongs to the arrival sequence. *)
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
  Context {Job : JobType}.
  Context `{JobArrival Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** We say that arrival times are consistent if any job that arrives
      in the sequence has the corresponding arrival time. *)
  Definition consistent_arrival_times :=
    forall j t,
      arrives_at arr_seq j t -> job_arrival j = t.

  (** We say that the arrival sequence is a set iff it doesn't contain
      duplicate jobs at any given time. *)
  Definition arrival_sequence_uniq :=
    forall t, uniq (arrivals_at arr_seq t).

  (** We say that the arrival sequence is valid iff it is a set
      and arrival times are consistent *)
  Definition valid_arrival_sequence :=
    consistent_arrival_times /\ arrival_sequence_uniq.

End ValidArrivalSequence.
(*|
For a given `JobArrival`, one can state a few additional definitions
about individual jobs.
|*)
Section ArrivalTimeProperties.

  (** Assume that job arrival times are known. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.

  (** Let j be any job. *)
  Variable j : Job.

  (** We say that job j has arrived at time t iff it arrives
      at some time t_0 with t_0 <= t. *)
  Definition has_arrived (t : instant) := job_arrival j <= t.

  (** Next, we say that job j arrived before t iff it arrives
      at some time t_0 with t_0 < t. *)
  Definition arrived_before (t : instant) := job_arrival j < t.

  (** Finally, we say that job j arrives between t1 and t2
      iff it arrives at some time t with t1 <= t < t2. *)
  Definition arrived_between (t1 t2 : instant) :=
    t1 <= job_arrival j < t2.

End ArrivalTimeProperties.
(*|
Whereas when given an `arrival_sequence`, one can extract sequences of
jobs arriving in some time interval.
|*)
Section ArrivalSequencePrefix.

  (** Assume that job arrival times are known. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** By concatenation, we construct the list of jobs that arrived
      in the interval <<[t1, t2)>>. *)
  Definition arrivals_between (t1 t2 : instant) :=
    \cat_(t1 <= t < t2) arrivals_at arr_seq t.

  (** Based on that, we define the list of jobs that arrived
      up to time t, ...*)
  Definition arrivals_up_to (t : instant) := arrivals_between 0 t.+1.

  (** ... the list of jobs that arrived strictly before time t, ... *)
  Definition arrivals_before (t : instant) := arrivals_between 0 t.

  (** ... and the list of jobs that arrive in the interval
      <<[t1, t2)>> and satisfy a certain predicate [P]. *)
  Definition arrivals_between_P (P : Job -> bool) (t1 t2 : instant) :=
    [seq j <- arrivals_between t1 t2 | P j].

End ArrivalSequencePrefix.

(*|
Schedule
--------

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
Require Import prosa.behavior.schedule. (* .in *)

Print schedule.  (* .unfold *)
(*|
Processor states returned by the schedule can then be inspected to know whether
a given job is scheduled in this state
|*)
Check scheduled_in.  (* .unfold *)
(*|
The above means that given a job ``j`` of some type ``?Job``,
a processor state ``s`` of some type ``?State``, then
``scheduled_in j s`` is a boolean telling whether the job ``j``
is scheduled in state ``s``.

The amount of service given to a job in a processor state is defined similarly
|*)
Check service_in.  (* .unfold *)

(*|
Service
-------

Equipped with this definitions, the file
`behavior/service.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/service.v>`_
gives basic definitions on the service received by a job.
|*)
Section Service.

  (** * Service of a Job *)

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** First, we define whether a job [j] is scheduled
      at time [t], ... *)
  Definition scheduled_at (j : Job) (t : instant) :=
    scheduled_in j (sched t).

  (** ... and the instantaneous service received by job j
      at time t. *)
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
  Definition completed_by (j : Job) (t : instant) :=
    service j t >= job_cost j.

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

Finally, the
`behavior/all.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/behavior/all.v>`_
file provides a simple way to load all the above definitions by just typing
|*)
Require Import prosa.behavior.all.  (* .in *)

(*|
.. _model:

Model
=====

The `model/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/model>`_
directory of Prosa provides common specifications used by the real-time
analyses proved in the remaining of the library. This directory is larger
than the previous `behavior/` directory. It will then be only partially covered
here, so that this document remains self-contained. The material detailled below
should however be enough to get a good grasp of the kind of things formalized
in this `model/` directory.

Ideal Uniprocessor
------------------

The file `model/processor/ideal.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/processor/ideal.v>`_ defines ideal uniprocessors as processors
that are at each instant either idle or executing a single job.
To do this, a processor state, as introduced in schedule_ above,
is defined using the ``option`` type of Coq's standard library
|*)
Require Import prosa.model.processor.ideal.  (* .in *)

Print processor_state.  (* .unfold *)

Print option.  (* .unfold *)
(*|
A value of type ``option Job`` is either ``Some j`` with ``j`` of type
``Job`` or ``None``, respectively meaning that the processor is executing
job ``j`` or is idle. The function ``is_idle``
|*)
Check is_idle.  (* .unfold *)
(*|
is then defined as the function which, given a schedule and an instant,
tells whether the processor is idle in the given schedule at the given instant.

.. omitted prosa.model.processor.platform_properties

Concept of Task
---------------

The file `model/task/concept.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/task/concept.v>`_
defines the concept of *task*.
A task is simply defined as a type with decidable equality.

|*)
Require Import model.task.concept.  (* .in *)

Print TaskType.  (* .unfold *)
(*|
Then, a few typeclasses are defined to be able to express the main
characteristics of tasks. First, each job can be assigned to a task
|*)
Print JobTask.  (* .unfold *)
(*|
Three other classes are defined for task deadlines, cost and minimum cost.
|*)
Print TaskDeadline.
Print TaskCost.
Print TaskMinCost.
(*|
Then a bunch of validity hypothesis that usually apply to the above
definitions are defined. For instance,
|*)
Print task_cost_positive.
(*|
One can look at the ``ModelValidity`` Section
in `model/task/concept.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/task/concept.v>`_
for the complete list. Those hypothesis usually need to be assumed
whenever assuming any instance of the above typeclasses, otherwise
they usually don't mean anything.

Finally, task sets are defined as sequences of tasks.
This is used to express the fact that all jobs in an arrival sequence
come from a given finite set of tasks.
|*)
Print all_jobs_from_taskset.
(*|

Task Arrivals
-------------

The file `model/task/arrivals.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/task/arrivals.v>`_
provides a few basic definitions about arrivals of jobs of a given task.
For instance, given an arrival sequence ``arr_seq``, a task ``tsk``
and two instants ``t1`` and ``t2``, then
``task_arrivals_between arr_seq tsk t1 t2`` is the set of all jobs
of task ``tsk`` arriving between ``t1`` and ``t2`` in ``arr_seq``.
|*)
Require Import prosa.model.task.arrivals.  (* .in *)

Print task_arrivals_between.  (* .unfold *)
(*|

Task Sequentiality
------------------

The file `model/task/sequentiality.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/task/sequentiality.v>`_
defines the notion of sequential tasks.
A task is called *sequential* when all its jobs execute
in a non overlapping manner. This is formally defined in
|*)
Require Import prosa.model.task.sequentiality.  (* .in *)

Print sequential_tasks.
(*|

.. omitted prosa.model.readiness.sequential

Priority Classes
----------------

The file `model/priority/classes.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/priority/classes.v>`_
defines main classes of priority policies.
In this document, we are interested in Fixed Priority (FP) policies,
defined by the typeclass
|*)
Require Import prosa.model.priority.classes.  (* .in *)

Print FP_policy.  (* .unfold *)
(*|
A fixed priority policy is indeed defined as a relation on tasks.
The relation is called
|*)
Check hep_task.
(*|
for Higher or Equal Priority. If ``tsk1`` and ``tsk2`` are tasks,
then ``hep_task tsk1 tsk2`` means that ``tsk1`` has higher (or equal)
priority than ``tsk2``.

The two other classes provided are Job Level Fixed Priority (JLFP) and
Job Level Dynamic Priority (JLDP).
|*)
Print JLFP_policy.
Print JLDP_policy.
(*|
The first one is a relation between jobs, whereas the second one
associates to each instant a (potentially) different relation.

Two type class instances are then defined to automatically build a JLFP
from a FP (associating the same priority for all jobs in a same task)
and to build a JLDP from a JLFP (associating the same relation to each
instant).

The remaining of the file provides the definitions of some common
hypotheses on priority policies, in particular reflexivity and transitivity
or the fact that a priority is total.

Preemption
----------

The file `model/preemption/parameter.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/preemption/parameter.v>`_
defines the notion of preemption.

In Prosa, the various preemption models are represented with a single
predicate
|*)
Require Import prosa.model.preemption.parameter.  (* .in *)

Print JobPreemptable.
(*|
that indicates, given a job and a degree of progress, whether the job
is preemptable at its current point of execution.

The validity conditions of a preemption model are then defined
|*)
Print valid_preemption_model.
(*|

A fully preemptive job is then defined as a job that is always preemptable
in file `model/preemption/fully_preemptive.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/preemption/fully_preemptive.v>`_.

The preemption model for tasks is slightly more elaborate.
The details can be found in file
`model/task/preemption/parameters.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/task/preemption/parameters.v>`_.
and the fully preemptive implementation lies in
`model/task/preemption/fully_preemptive.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/task/preemption/fully_preemptive.v>`_.

.. omitted prosa.model.task.absolute_deadline

Arrival Curves
--------------

The file `model/task/arrival/curves.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/task/arrival/curves.v>`_
defines (min and max) arrival curves.
The typeclass ``MaxArrivals`` gives the type of arrival curves.
|*)
Require Import prosa.model.task.arrival.curves.  (* .in *)

Print MaxArrivals.  (* .unfold *)
(*|
Arrival curves associate to each task and duration a natural number.
This number will be the maximum number of jobs of the given task that
can arrive in any interval of time of the given duration.

Valid arrival curves are the functions that start at 0 and are monotone
|*)
Print valid_arrival_curve.  (* .unfold *)
(*|

Finally, the semantics of arrival curves, is given by
|*)
Print respects_max_arrivals.  (* .unfold *)
(*|

In the same file, one can find similar definitions for minimal arrival curves,
as well as min and max separations.

Schedule Model
--------------

In file `model/schedule/preemption_time.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/schedule/preemption_time.v>`_,
the notion of preemption time in a schedule is defined according
to the scheduled job at each instant, if any.
|*)
Require Import prosa.model.schedule.preemption_time.  (* .in *)

Print preemption_time.  (* .unfold *)
(*|
This allows to, finally, define what it means for a schedule to
respect a given priority policy in file
`model/schedule/priority_driven.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/model/schedule/priority_driven.v>`_
|*)
Require Import prosa.model.schedule.priority_driven.  (* .in *)

Print respects_JLDP_policy_at_preemption_point.  (* .unfold *)
(*|
This means that when a job ``j`` is backlogged at some preemption instant ``t``,
all scheduled jobs ``j_hp`` at that instant ``t`` have higher or equal priority.

.. omitted prosa.model.schedule.work_conserving
   omitted prosa.model.aggregate.workload
   omitted prosa.model.aggregate.service_of_jobs

.. test maths :math:`\sum_{i=1}^n i^2`
|*)

(*|
.. _analysis:

Analysis
========

The `analysis/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis>`_
directory contains the proofs of real-time analyses themselves.
Even more than pen&paper proofs, formal proofs need to be appropriately
factored out into small reusable lemmas. Thus, the `analysis/` directory
also contains many basic lemmas about all the definitions introduced above.
Since this document only attempts to present a specific analysis, namely
fixed priority tasks on a fully preemptive uniprocessor, we only introduce
here the lemmas used in that analysis. However, at the end of the section,
the reader should be able to navigate herself through all the lemmas
of the directory.

First Lemmas
------------

Some definitions are used only internally into `analysis/`,
thus they aren't located in `behavior/` nor `model/`.
Among them, let's mention
|*)
Require Import prosa.analysis.definitions.job_properties.  (* .in *)

Print job_cost_positive.
(*|
and
|*)
Require Import prosa.analysis.definitions.schedule_prefix.  (* .in *)

Print identical_prefix.
(*|

Equipped with all these definitions, we can finally introduce
our first lemmas. The files in the directory
`analysis/facts/behavior/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/behavior>`_
contain many lemmas establishing basic facts about all the definitions
introduced in the behavior_ section above.
The user can load all those lemmas by simply requiring
|*)
Require Import prosa.analysis.facts.behavior.all.  (* .in *)
(*|
The files in `analysis/facts/behavior/` are developed in a literate
programming style like the remaining of Prosa. Thus, they can be read
inextenso like any other file in the library. However, lemmas are mostly
made to be used inside proofs and such reading is a very ineffective way to
find the lemma one needs when carrying a proof. Indeed, once one gets a Coq
interface up and running, it is much more convenient to just load the files
with the above `Require` command and use the `Search` utility of Coq.
For instance, to find all lemmas about `scheduled_at` and `service_at`,
one can type
|*)
Search scheduled_at service_at.
(*|
The `Search` command can also be used with a pattern, for instance
to look for lemmas of the shape
`service at some point <= service at some other point`, one can type
|*)
Search (service _ _ _ <= service _ _ _).  (* .unfold *)
(*|
The `Search` command is even more powerful, as documented in
`Coq's reference manual <https://coq.inria.fr/distrib/current/refman/proof-engine/vernacular-commands.html#coq:cmd.Search>`_.

.. note::
   The `reference manual of Coq <https://coq.inria.fr/distrib/current/refman/>`_
   is of high quality nowadays. It is a good first place to learn about the
   details of any Coq feature.

Back to the `service_monotonic` lemma found above, if one looks in
the file
`analysis/facts/behavior/service.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/behavior/service.v>`_,
one will find the following text
|*)
(** We establish a basic fact about the monotonicity of service. *)
Section Monotonicity.

  (** Consider any job type and any processor model. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Consider any given schedule... *)
  Variable sched : schedule PState.

  (** ...and a given job that is to be scheduled. *)
  Variable j : Job.

  (** We observe that the amount of service received
      is monotonic by definition. *)
  Lemma service_monotonic : forall t1 t2, t1 <= t2 ->
    service sched j t1 <= service sched j t2.
  Proof.
    by move=> t1 t2 ?; rewrite -(service_cat _ _ t1 t2)// leq_addr.
  Qed.

End Monotonicity.
(*|
The whole `Section` business should now be familiar to the reader.
The `Lemma` keyword is new. It is used to introduce a lemma,
followed by its name, a colon sign and the statement of the result itself,
ending with a dot, as any Coq sentence.
The cryptic line between `Proof` and `Qed` can be ignored for now.
It instructs Coq how to perform the proof of the previously stated lemma.
The only thing to notice is that this proof is terminated by a `Qed`
(for the latin words "Quod Erat Demonstrandum") meaning that,
if Coq can compile the `Qed` it managed to check the proof and the new lemma
is now available for use in future proofs.

.. note::
   Naming lemmas is a delicate business. Some libraries have very specific
   and elaborated naming schemes, usually based on the statement of the
   theorem itself. Although there is no such strict naming scheme in Prosa,
   one can find a few generic advices in
   `doc/guidelines.md <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/doc/guidelines.md#naming-conventions>`_.

.. note::
   Coq has many synonyms of `Lemma`. The commands `Lemma`, `Theorem`, `Fact`,
   `Remark`, `Corollary` and `Proposition` all behave in the exact
   same way. The user is free to choose any of them to better comment her code.

Similarly to behavior, the files
`ideal/schedule.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/model/ideal/schedule.v>`_,
`task_arrivals.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/model/task_arrivals.v>`_,
`sequential.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/model/sequential.v>`_,
`service_of_jobs.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/model/service_of_jobs.v>`_,
`preemption.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/model/preemption.v>`_
and
`workload.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/model/workload.v>`_,
in the 
`analysis/facts/model/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/model/>`_
directory provide basic lemmas about definitions introduced in the model_
section above.

The files
`job/preemptive.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/preemption/job/preemptive.v>`_,
`task/preemptive.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/preemption/task/preemptive.v>`_,
`rtc_threshold/job_preemptable.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/preemption/rtc_threshold/job_preemptable.v>`_
and
`rtc_threshold/preemptive.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/preemption/rtc_threshold/preemptive.v>`_,
in the
`analysis/facts/preemption/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/preemption/>`_
directory provide basic lemmas about preemption.

.. omitted definitions.request_bound_function
   omitted facts.model.rbf

Readiness
---------

The file 
`analysis/definitions/readiness.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/definitions/readiness.v>`_
contains definitions of `nonclairvoyant_readiness`
and `nonpreemptive_readiness` while the file
`analysis/definitions/work_bearing_readiness.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/definitions/work_bearing_readiness.v>`_
defines `work_bearing_readiness`.
Basic facts about the sequential task readiness model can be found in
`analysis/facts/readiness/sequential.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/readiness/sequential.v>`_.

Busy Intervals
--------------

Busy Intervals constitute a central tool in classic real time analyses.
They are defined in
`definitions/busy_interval.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/definitions/busy_interval.v>`_
and
`definitions/priority_inversion.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/definitions/priority_inversion.v>`_
and basic lemmas about them are to be found in
`facts/busy_interval/busy_interval.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/busy_interval/busy_interval.v>`_
and
`facts/busy_interval/priority_inversion.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/facts/busy_interval/priority_inversion.v>`_.

Abstract RTA
------------

The directory
`analysis/abstract/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/abstract/>`_
contains proofs of classic real time analyses in a setting as abstract
as possible. These proofs will later be instantiated in more concrete settings.

First, a few more definitions are needed and can be found in the file
`analysis/abstract/definitions.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/abstract/definitions.v>`_

Then the notion of *search space* is exploited to refine the set of behaviors
that can exhibit worst case response times.
These results can be found in
`analysis/abstract/search_space.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/abstract/search_space.v>`_

The fact that jobs that jobs with bounded interference receive at least some amount of service is proved in
`analysis/abstract/lower_bound_on_service.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/abstract/lower_bound_on_service.v>`_

The response time of tasks is defined as `task_response_time_bound` in
`analysis/definitions/schedulability.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/definitions/schedulability.v>`_
which enables to state and prove the main theorem
`uniprocessor_response_time_bound` in
`analysis/abstract/abstract_rta.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/abstract/abstract_rta.v>`_.
Basically, this theorem states that under a bunch of hypotheses,
if some `R` satisfies the inequality in hypothesis `H_R_is_maximum`,
then `R` is a response time bound.

The file
`analysis/abstract/ideal/abstract_seq_rta.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/abstract/ideal/abstract_seq_rta.v>`_.
offers a more precise theorem `uniprocessor_response_time_bound_seq`
for sequential tasks.

.. omitted definitions.task_schedule

Finally, the file
`analysis/abstract/ideal/iw_instantiation.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/analysis/abstract/ideal/iw_instantiation.v>`_.
provides lemmas for Job Level Fixed Priority policies for ideal
uniprocessors.
|*)

(*|
.. _results:

Results
=======

The `results/ <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/results>`_
directory instantiates some of the above results in well known settings.
For instance, the main result for fixed priority tasks on a fully preemptive uniprocessor.
lies in the file
`results/fixed_priority/rta/fully_preemptive.v <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/tree/master/results/fixed_priority/rta/fully_preemptive.v>`_.
After about hundred lines to state the fixed priority fully preemptive
setting on ideal uniprocessors (this could probably be way shorter,
were the definitions more structured, but for the sake of flexibility, Prosa choses a flat model
with lot of individual hypotheses), the main hypothesis are the ones about `L` and `R`
and they enable to prove the theorem
`uniprocessor_response_time_bound_fully_preemptive_fp`
that simply states that `R` is a response time bound.

.. omitted fixed_priority.rta.bounded_pi
   omitted fixed_priority.rta.bounded_nps
|*)

(*|
.. _contributing:

Contributing
============

The reader should now be able to navigate through the extensive
documentation of the Prosa library. The library being developped in a literate
programming style, one can simply read the source files, although
when looking for precise results, the querying commands of Coq
`Check`, `Print`, `About` and `Search` can be of great help
(particularly considering that Prosa makes extensive use of the `Section`
mechanism which may sometimes obfuscate what are the exact hypotheses of
a given lemma).

Prosa follows an open source development process.
Contributions are welcomed, as stated at the end of its
`README <https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/#commit-and-development-rules>`_.
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
