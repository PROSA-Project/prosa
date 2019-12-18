Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.schedulability.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Sustainability.

  Import ArrivalSequence UniprocessorSchedule Schedulability.

  Section SustainabilityDefs.

    (* Consider any job type. *)
    Context {Job: eqType}.

    Section DefiningParameters.

      (** Defining Parameter Type *)
      Section ParameterType.

        (* We begin by defining the set of possible parameter labels, ... *)
        Inductive parameter_label :=
        | JOB_ARRIVAL
        | JOB_COST
        | JOB_DEADLINE
        | JOB_JITTER
        | JOB_SUSPENSION.

        (* ...which can be compared with the built-in decidable equality. *)
        Scheme Equality for parameter_label.
        Lemma eqlabelP: Equality.axiom parameter_label_beq.
        Proof.
          intros x y.
          by destruct x; destruct y; try (by apply ReflectT); try (by apply ReflectF).
        Qed.
        Canonical label_eqMixin := EqMixin eqlabelP.
        Canonical label_eqType := Eval hnf in EqType parameter_label label_eqMixin.
        
        (* Next, we associate to each label a type of function over jobs. *)
        Definition type_of_label (l: parameter_label) : Type :=
          match l with
          | JOB_ARRIVAL => Job -> instant
          | JOB_COST => Job -> time
          | JOB_DEADLINE => Job -> time
          | JOB_JITTER => Job -> time
          | JOB_SUSPENSION => Job -> time -> duration
          end.

        (* For each function type, we also define a default value to simplify lookups. *)
        Definition default_val (l : parameter_label) : type_of_label l :=
          match l with
          | JOB_ARRIVAL => fun _ => 0
          | JOB_COST => fun _ => 0
          | JOB_DEADLINE => fun _ => 0
          | JOB_JITTER => fun _ => 0
          | JOB_SUSPENSION => fun _ _ => 0
          end.

        (* Finally, we define a job parameter as a pair containing a label and a function. *)
        Record job_parameter := param
        {
          p_label : parameter_label;
          p_function : type_of_label p_label
        }.

        (* With the definitions above, we can declare parameter lists as follows. *)
        Variable example_job_cost: Job -> time.
        Variable example_job_suspension: Job -> time -> duration.
        Let example_params :=
          [:: param JOB_COST example_job_cost; param JOB_SUSPENSION example_job_suspension].

      End ParameterType.

      (** Looking up parameters *)
      Section ParameterLookup.
        
        (* By comparing labels, we define a function that finds a parameter in a list. *)
        Definition find_param (l : parameter_label) (s : seq job_parameter) :=
          nth (param l (default_val l)) s
              (find (fun x => p_label x == l) s).

        (* Next, we define a function that converts a given parameter p to the
           type of label l, given a proof EQ that the labels are the same. *)
        Let convert_parameter_type (p: job_parameter) (l: parameter_label)
                                   (EQ_PROOF: p_label p = l) :=
          eq_rect (p_label p) (fun x => type_of_label x) (p_function p) l EQ_PROOF.

        (* This allows returning the function of (type_of_label l) from a parameter p.
           (If the label of p is not l, we return a dummy default value instead.) *)
        Definition get_param_function (l: parameter_label) (p: job_parameter) : type_of_label l :=
          if (parameter_label_eq_dec (p_label p) l) is left EQ_PROOF then
            convert_parameter_type p l EQ_PROOF
          else (default_val l).

        (* To conclude, we define a function that returns the function with label l from a parameter list. *)
        Definition return_param (l: parameter_label) (s: seq job_parameter) : type_of_label l :=
          get_param_function l (find_param l s).

        (* To illustrate how these functions work, consider this simple parameter list. *)
        Variable example_job_cost: Job -> time.
        Variable example_job_suspension: Job -> time -> duration.
        Let example_params :=
          [:: param JOB_COST example_job_cost; param JOB_SUSPENSION example_job_suspension].

        (* In that case, JOB_COST returns the function example_job_cost, ...*)
        Example return_param_works1:
          return_param JOB_COST example_params = example_job_cost.
        Proof. by done. Qed.

        (* ...and JOB_SUSPENSION_DURATION returns the function example_job_suspension. *)
        Example return_param_works2:
          return_param JOB_SUSPENSION example_params = example_job_suspension.
        Proof. by done. Qed.

      End ParameterLookup.
      
      (** Additional properties of parameter lists *)
      Section Properties.

        (* Given a set of labels, we define whether two parameter lists differ only
           by the parameters with those labels.
           Note: This predicate assumes that both lists have similar, unique labels.  *)
        Definition differ_only_by (variable_labels: seq parameter_label) (s1 s2: seq job_parameter) :=
          forall (param param': job_parameter),
            List.In param s1 ->
            List.In param' s2 ->
            p_label param = p_label param' ->
            p_label param \notin variable_labels ->
            param = param'.

        (* Next, we define a function that returns the labels of a parameter list. *)
        Definition labels_of (params: seq job_parameter) := [seq p_label p | p <- params].
        
        (* Next, we define whether a parameter list has unique labels. *)
        Definition has_unique_labels (params: seq job_parameter) := uniq (labels_of params).

        (* We also define whether a parameter list corresponds to a given set of labels. *)
        Definition corresponding_labels (params: seq job_parameter) (labels: seq parameter_label) :=
          forall l, l \in labels_of params <-> l \in labels.
        
        (* Finally, we prove that in any list of unique parameters, return_param always
           returns the corresponding parameter. *)
        Lemma found_param_label:
          forall (params: seq job_parameter) (p: job_parameter) (label: parameter_label),
            has_unique_labels params ->
            List.In p params ->
            p_label p = label ->
            p = param label (return_param label params).
        Proof.
          induction params as [| p0 params']; first by done.
          move => p label /= /andP [NOTIN UNIQ] IN EQ /=.
          move: IN => [EQ0 | IN].
          {
            subst p0; rewrite /return_param /find_param /= EQ eq_refl /=.
            by destruct p, label; simpl in *; subst.
          }
          {
            rewrite /return_param /find_param /=.
            case EQ': (_ == _); last by apply IHparams'.
            move: EQ' => /eqP EQ'; rewrite EQ' in NOTIN.
            move: NOTIN => /negP NOTIN; exfalso; apply NOTIN.
            by apply/mapP2; exists p.
          }
        Qed.
        
      End Properties.

    End DefiningParameters.

    (** Definition of sustainability for scheduling policies. *)
    Section SustainabilityPolicy.

      (* First, we define the set of possible labels for the job parameters. *)
      Variable all_labels: seq parameter_label.
      
      (* Next, let's consider any good schedulability property of a job, such as
         "no deadline miss" or "response time bounded by R".
         Given a sequence of job parameters, a schedule and a job j in this schedule,
         the predicate indicates whether j satisfies the schedulability property. *)
      Variable is_schedulable:
        seq job_parameter -> schedule Job -> Job -> bool.

      (* Also, consider any predicate that, given a parameter list, states whether the arrival
         sequence and schedule belong to a certain task model. *)
      Variable belongs_to_task_model:
        seq job_parameter -> arrival_sequence Job -> schedule Job -> Prop.
      
      (* Let sustainable_param denote the label of the parameter for which we claim sustainability. *)
      Variable sustainable_param: parameter_label.

      (* Let better_params denote any total order relation over the old and new values of the
         sustainable parameter, i.e., it indicates: "the second parameter is better than the first".
         For example, in many task models, lower job costs lead to better schedules, so a valid
         predicate would be: (fun job_cost job_cost' => forall j, job_cost j >= job_cost' j).  *)
      Variable has_better_params: (type_of_label sustainable_param) ->
                                  (type_of_label sustainable_param) -> Prop.

      (* Next, we define whether the sustainable parameter becomes better when moving from list
         params to params'. *)
      Definition sustainable_param_becomes_better (params params': seq job_parameter) :=
        let P := return_param sustainable_param params in
        let P' := return_param sustainable_param params' in
          has_better_params P P'.

      Section VaryingParameters.
        
        (* Let variable_params denote the set of parameters that are allowed to vary. *)
        Variable variable_params: seq parameter_label.

        (* Now we define whether both the sustainable and the variable parameters belong to a parameter list. *)
        Definition sustainable_and_varying_params_in (params: seq job_parameter) :=
          forall label,
            label \in sustainable_param :: variable_params ->
            label \in labels_of params.
        
      (* Next, we define whether a parameter list has consistent labels. Since
         we'll have to quantify over many parameter lists, this prevents issues
         with empty/invalid parameter lists. *)
      Definition has_consistent_labels (params: seq job_parameter) :=
        has_unique_labels params /\
        corresponding_labels params all_labels /\
        sustainable_and_varying_params_in params.
        
        (* Next, we define whether all jobs sets with given params are schedulable... *)
        Definition jobs_are_schedulable_with (params: seq job_parameter) :=
          forall arr_seq sched j,
            belongs_to_task_model params arr_seq sched ->
            is_schedulable params sched j.

        (* ...and also define whether the job sets that only differ from the given params
           by the 'set of variable parameters' are all schedulable. *)
        Definition jobs_are_V_schedulable_with (params: seq job_parameter) :=
          forall (similar_params: seq job_parameter),
            has_consistent_labels similar_params ->
            differ_only_by variable_params params similar_params ->
            jobs_are_schedulable_with similar_params.

        (* Then, we say that the scheduling policy is weakly-sustainable with sustainable_param
           and variable_params iff the following holds:
              if jobs are V-schedulable with the original parameters, then they are also
              schedulable with better parameters (according to the has_better_params relation). *)
        Definition weakly_sustainable :=
          forall (params better_params: seq job_parameter),
            has_consistent_labels params ->
            has_consistent_labels better_params ->
            differ_only_by [::sustainable_param] params better_params ->
            sustainable_param_becomes_better params better_params ->
            jobs_are_V_schedulable_with params ->
            jobs_are_schedulable_with better_params.

        (* Next, using the contrapositive of weakly_sustainable, we provide
           an alternative definition of weak sustainability. *)
        Section AlternativeDefinition.

          (* First, let's define whether the sustainable parameter becomes
             worse when switching from params to params'. *)
          Definition sustainable_param_becomes_worse (params params': seq job_parameter) :=
            let P := return_param sustainable_param params in
            let P' := return_param sustainable_param params' in
              has_better_params P' P.

          (* Next, we define whether jobs are not schedulable with a given set of parameters. *)
          Definition jobs_are_not_schedulable_with (params: seq job_parameter) :=
            exists arr_seq sched j,
              belongs_to_task_model params arr_seq sched /\
              ~~ is_schedulable params sched j.

          (* Based on that, we formalize the alternative definition of weakly sustainable. *)
          Definition weakly_sustainable_contrapositive :=
            forall params params_worse,
              has_consistent_labels params ->
              has_consistent_labels params_worse ->
              jobs_are_not_schedulable_with params ->
              differ_only_by [:: sustainable_param] params params_worse ->
              sustainable_param_becomes_worse params params_worse ->
              exists params_worse',
                has_consistent_labels params_worse' /\
                differ_only_by variable_params params_worse params_worse' /\
                jobs_are_not_schedulable_with params_worse'.

          (* Assume De Morgan's law for propositional and predicate logic. *)
          Hypothesis H_classical_forall_exists:
            forall (T: Type) (P: T -> Prop),
              ~ (forall x, ~ P x) -> exists x, P x.
          Hypothesis H_classical_and_or:
            forall (P Q: Prop), ~ (P /\ Q) -> ~ P \/ ~ Q.

          (* Then, we can prove the equivalence of the two definitions. *)
          Theorem weak_sustainability_equivalence:
            weakly_sustainable <-> weakly_sustainable_contrapositive.
          Proof.
            rename H_classical_forall_exists into NOTALL, H_classical_and_or into ANDOR.
            split.
            {
              intros WEAK params params_worse CONS CONSworse NOTSCHED DIFF WORSE.
              apply NOTALL; intro ALL.
              unfold weakly_sustainable in *.
              specialize (WEAK params_worse params CONSworse CONS).
              feed WEAK.
              {
                intros p p' IN IN' EQ NOTIN; symmetry.
                apply DIFF; try by done.
                by rewrite -EQ.
              }
              feed WEAK; first by done.
              feed WEAK.
              {
                intros params' CONS' DIFF'; specialize (ALL params').
                apply ANDOR in ALL; move: ALL => [BUG | ALL] //.
                apply ANDOR in ALL; move: ALL => [BUG | ALL] //.
                unfold jobs_are_not_schedulable_with in *.
                intros arr_seq sched j BELONGS; apply contraT; intro NOTSCHED'.
                by exfalso; apply ALL; exists arr_seq, sched, j.
              }
              unfold jobs_are_schedulable_with, jobs_are_not_schedulable_with in *.
              clear -WEAK NOTSCHED.
              move: NOTSCHED => [arr_seq [sched [j [BELONGS NOTSCHED]]]].
              specialize (WEAK arr_seq sched j BELONGS).
              by rewrite WEAK in NOTSCHED.
            }
            {
              intros WEAK params better_params CONS CONSbetter DIFF BETTER VSCHED.
              intros arr_seq sched j BELONGS; apply contraT; intros NOTSCHED.
              unfold weakly_sustainable_contrapositive in *.
              feed (WEAK better_params params); first by done.
              feed WEAK; first by done.
              feed WEAK; first by exists arr_seq, sched, j.
              feed WEAK.
              {
                intros p p' IN IN' EQ NOTIN; symmetry.
                apply DIFF; try by done.
                by rewrite -EQ.
              }
              feed WEAK; first by done.
              move: WEAK => [params_worse' [CONS' [DIFF' NOTSCHED']]].
              unfold jobs_are_V_schedulable_with in *.
              specialize (VSCHED params_worse' CONS' DIFF').
              move: NOTSCHED' => [arr_seq' [sched' [j' [BELONGS' NOTSCHED']]]].
              specialize (VSCHED arr_seq' sched' j' BELONGS').
              by rewrite VSCHED in NOTSCHED'.
            }
          Qed.
          
        End AlternativeDefinition.

      End VaryingParameters.

      (* Also, we say that the scheduling policy is strongly-sustainable
         with sustainable_param iff it is weakly-sustainable with
         sustainable_param and the set of variable parameters is empty. *)
      Definition strongly_sustainable := weakly_sustainable [::].
      
    End SustainabilityPolicy.
    
  End SustainabilityDefs.

  Global Arguments job_parameter: clear implicits.

End Sustainability.