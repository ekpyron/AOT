(*<*)
theory AOT_PLM
  imports AOT_axioms
begin
(*>*)

section\<open>The Deductive System PLM\<close>

(* constrain sledgehammer to the abstraction layer *)
unbundle AOT_no_atp

(* To enable meta syntax: *)
(*interpretation AOT_meta_syntax.*)
(* To disable meta syntax: *)
interpretation AOT_no_meta_syntax.

(* To enable AOT syntax (takes precedence over meta syntax; can be done locally using "including" or "include"): *)
unbundle AOT_syntax
(* To disable AOT syntax (restoring meta syntax or no syntax; can be done locally using "including" or "include"): *)
(* unbundle AOT_no_syntax *)

AOT_theorem "modus-ponens": assumes \<open>\<phi>\<close> and \<open>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<psi>\<close>
  using assms by (simp add: AOT_sem_imp) (* NOTE: semantics needed *)
lemmas MP = "modus-ponens"

AOT_theorem "non-con-thm-thm": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<^bold>\<turnstile> \<phi>\<close>
  using assms by simp

AOT_theorem "vdash-properties:1[1]": assumes \<open>\<phi> \<in> \<Lambda>\<close> shows \<open>\<^bold>\<turnstile> \<phi>\<close>
  using assms unfolding AOT_model_act_axiom_def by blast (* NOTE: semantics needed *)

attribute_setup act_axiom_inst =
  \<open>Scan.succeed (Thm.rule_attribute [] (K (fn thm => thm RS @{thm "vdash-properties:1[1]"})))\<close>
  "Instantiate modally fragile axiom as modally fragile theorem."

AOT_theorem "vdash-properties:1[2]": assumes \<open>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close>
  using assms unfolding AOT_model_axiom_def by blast (* NOTE: semantics needed *)

attribute_setup axiom_inst =
  \<open>Scan.succeed (Thm.rule_attribute [] (K (fn thm => thm RS @{thm "vdash-properties:1[2]"})))\<close>
  "Instantiate axiom as theorem."

method cqt_2_lambda_inst_prover = (fast intro: AOT_instance_of_cqt_2_intro)
method "cqt:2[lambda]" = (rule "cqt:2[lambda]"[axiom_inst]; cqt_2_lambda_inst_prover)

AOT_theorem "vdash-properties:3": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<Gamma> \<^bold>\<turnstile> \<phi>\<close>
  using assms by blast

AOT_theorem "vdash-properties:5": assumes \<open>\<Gamma>\<^sub>1 \<^bold>\<turnstile> \<phi>\<close> and \<open>\<Gamma>\<^sub>2 \<^bold>\<turnstile> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<Gamma>\<^sub>1, \<Gamma>\<^sub>2 \<^bold>\<turnstile> \<psi>\<close>
  using MP assms by blast

AOT_theorem "vdash-properties:6": assumes \<open>\<phi>\<close> and \<open>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<psi>\<close>
  using MP assms by blast

AOT_theorem "vdash-properties:8": assumes \<open>\<Gamma> \<^bold>\<turnstile> \<phi>\<close> and \<open>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<Gamma> \<^bold>\<turnstile> \<psi>\<close>
  using assms by argo

AOT_theorem "vdash-properties:9": assumes \<open>\<phi>\<close> shows \<open>\<psi> \<rightarrow> \<phi>\<close>
  using MP "pl:1"[axiom_inst] assms by blast

AOT_theorem "vdash-properties:10": assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<phi>\<close> shows \<open>\<psi>\<close>
  using MP assms by blast
lemmas "\<rightarrow>E" = "vdash-properties:10"

AOT_theorem "rule-gen": assumes \<open>for arbitrary \<alpha>: \<phi>{\<alpha>}\<close> shows \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
  using assms by (metis AOT_var_of_term_inverse AOT_sem_denotes AOT_sem_forall) (* NOTE: semantics needed *)
lemmas GEN = "rule-gen"

AOT_theorem "RN[prem]": assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi>\<close>
  by (meson AOT_sem_box assms image_iff) (* NOTE: semantics needed *)
AOT_theorem RN: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<box>\<phi>\<close>
  using "RN[prem]" assms by blast

AOT_axiom "df-rules-formulas[1]": assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using assms by (simp_all add: AOT_model_axiomI AOT_model_equiv_def AOT_sem_imp) (* NOTE: semantics needed *)
AOT_axiom "df-rules-formulas[2]": assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<psi> \<rightarrow> \<phi>\<close>
  using assms by (simp_all add: AOT_model_axiomI AOT_model_equiv_def AOT_sem_imp) (* NOTE: semantics needed *)
(* NOTE: for convenience also state the above as regular theorems *)
AOT_theorem "df-rules-formulas[3]": assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using "df-rules-formulas[1]"[axiom_inst, OF assms].
AOT_theorem "df-rules-formulas[4]": assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<psi> \<rightarrow> \<phi>\<close>
  using "df-rules-formulas[2]"[axiom_inst, OF assms].


AOT_axiom "df-rules-terms[1]":
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close>
  shows \<open>(\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}) & (\<not>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<not>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>)\<close>
  using assms by (simp add: AOT_model_axiomI AOT_sem_conj AOT_sem_imp AOT_sem_eq AOT_sem_not AOT_sem_denotes AOT_model_id_def) (* NOTE: semantics needed *)
AOT_axiom "df-rules-terms[2]":
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close>
  shows \<open>(\<sigma>\<down> \<rightarrow> \<tau> = \<sigma>) & (\<not>\<sigma>\<down> \<rightarrow> \<not>\<tau>\<down>)\<close>
  by (metis "df-rules-terms[1]" case_unit_Unity assms)
(* NOTE: for convenience also state the above as regular theorems *)
AOT_theorem "df-rules-terms[3]":
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close>
  shows \<open>(\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}) & (\<not>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<not>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>)\<close>
  using "df-rules-terms[1]"[axiom_inst, OF assms].
AOT_theorem "df-rules-terms[4]":
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close>
  shows \<open>(\<sigma>\<down> \<rightarrow> \<tau> = \<sigma>) & (\<not>\<sigma>\<down> \<rightarrow> \<not>\<tau>\<down>)\<close>
  using "df-rules-terms[2]"[axiom_inst, OF assms].


AOT_theorem "if-p-then-p": \<open>\<phi> \<rightarrow> \<phi>\<close>
  by (meson "pl:1"[axiom_inst] "pl:2"[axiom_inst] MP)

AOT_theorem "deduction-theorem": assumes \<open>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using assms by (simp add: AOT_sem_imp) (* NOTE: semantics needed *)
lemmas CP = "deduction-theorem"
lemmas "\<rightarrow>I" = "deduction-theorem"

AOT_theorem "ded-thm-cor:1": assumes \<open>\<Gamma>\<^sub>1 \<^bold>\<turnstile> \<phi> \<rightarrow> \<psi>\<close> and \<open>\<Gamma>\<^sub>2 \<^bold>\<turnstile> \<psi> \<rightarrow> \<chi>\<close> shows \<open>\<Gamma>\<^sub>1, \<Gamma>\<^sub>2 \<^bold>\<turnstile> \<phi> \<rightarrow> \<chi>\<close>
  using "\<rightarrow>E" "\<rightarrow>I" assms by blast
AOT_theorem "ded-thm-cor:2": assumes \<open>\<Gamma>\<^sub>1 \<^bold>\<turnstile> \<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)\<close> and \<open>\<Gamma>\<^sub>2 \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<Gamma>\<^sub>1, \<Gamma>\<^sub>2 \<^bold>\<turnstile> \<phi> \<rightarrow> \<chi>\<close>
  using "\<rightarrow>E" "\<rightarrow>I" assms by blast

AOT_theorem "ded-thm-cor:3": assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<psi> \<rightarrow> \<chi>\<close> shows \<open>\<phi> \<rightarrow> \<chi>\<close>
  using "\<rightarrow>E" "\<rightarrow>I" assms by blast
declare "ded-thm-cor:3"[trans]
AOT_theorem "ded-thm-cor:4": assumes \<open>\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)\<close> and \<open>\<psi>\<close> shows \<open>\<phi> \<rightarrow> \<chi>\<close>
  using "\<rightarrow>E" "\<rightarrow>I" assms by blast

lemmas "Hypothetical Syllogism" = "ded-thm-cor:3"

AOT_theorem "useful-tautologies:1": \<open>\<not>\<not>\<phi> \<rightarrow> \<phi>\<close>
  by (metis "pl:3"[axiom_inst] "\<rightarrow>I" "Hypothetical Syllogism")
AOT_theorem "useful-tautologies:2": \<open>\<phi> \<rightarrow> \<not>\<not>\<phi>\<close>
  by (metis "pl:3"[axiom_inst] "\<rightarrow>I" "ded-thm-cor:4")
AOT_theorem "useful-tautologies:3": \<open>\<not>\<phi> \<rightarrow> (\<phi> \<rightarrow> \<psi>)\<close>
  by (meson "ded-thm-cor:4" "pl:3"[axiom_inst] "\<rightarrow>I")
AOT_theorem "useful-tautologies:4": \<open>(\<not>\<psi> \<rightarrow> \<not>\<phi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>)\<close>
  by (meson "pl:3"[axiom_inst] "Hypothetical Syllogism" "\<rightarrow>I")
AOT_theorem "useful-tautologies:5": \<open>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<not>\<psi> \<rightarrow> \<not>\<phi>)\<close>
  by (metis "useful-tautologies:4" "Hypothetical Syllogism" "\<rightarrow>I")

AOT_theorem "useful-tautologies:6": \<open>(\<phi> \<rightarrow> \<not>\<psi>) \<rightarrow> (\<psi> \<rightarrow> \<not>\<phi>)\<close>
  by (metis "\<rightarrow>I" MP "useful-tautologies:4")

AOT_theorem "useful-tautologies:7": \<open>(\<not>\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<not>\<psi> \<rightarrow> \<phi>)\<close>
  by (metis "\<rightarrow>I" MP "useful-tautologies:3" "useful-tautologies:5")

AOT_theorem "useful-tautologies:8": \<open>\<phi> \<rightarrow> (\<not>\<psi> \<rightarrow> \<not>(\<phi> \<rightarrow> \<psi>))\<close>
  by (metis "\<rightarrow>I" MP "useful-tautologies:5")

AOT_theorem "useful-tautologies:9": \<open>(\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<not>\<phi> \<rightarrow> \<psi>) \<rightarrow> \<psi>)\<close>
  by (metis "\<rightarrow>I" MP "useful-tautologies:6")

AOT_theorem "useful-tautologies:10": \<open>(\<phi> \<rightarrow> \<not>\<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> \<not>\<phi>)\<close>
  by (metis "\<rightarrow>I" MP "pl:3"[axiom_inst])

AOT_theorem "dn-i-e:1": assumes \<open>\<phi>\<close> shows \<open>\<not>\<not>\<phi>\<close>
  using MP "useful-tautologies:2" assms by blast
lemmas "\<not>\<not>I" = "dn-i-e:1"
AOT_theorem "dn-i-e:2": assumes \<open>\<not>\<not>\<phi>\<close> shows \<open>\<phi>\<close>
  using MP "useful-tautologies:1" assms by blast
lemmas "\<not>\<not>E" = "dn-i-e:2"

AOT_theorem "modus-tollens:1": assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<not>\<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using MP "useful-tautologies:5" assms by blast
AOT_theorem "modus-tollens:2": assumes \<open>\<phi> \<rightarrow> \<not>\<psi>\<close> and \<open>\<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using "\<not>\<not>I" "modus-tollens:1" assms by blast
lemmas MT = "modus-tollens:1" "modus-tollens:2"

AOT_theorem "contraposition:1[1]": assumes \<open>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<not>\<psi> \<rightarrow> \<not>\<phi>\<close>
  using "\<rightarrow>I" MT(1) assms by blast
AOT_theorem "contraposition:1[2]": assumes \<open>\<not>\<psi> \<rightarrow> \<not>\<phi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using "\<rightarrow>I" "\<not>\<not>E" MT(2) assms by blast

AOT_theorem "contraposition:2": assumes \<open>\<phi> \<rightarrow> \<not>\<psi>\<close> shows \<open>\<psi> \<rightarrow> \<not>\<phi>\<close>
  using "\<rightarrow>I" MT(2) assms by blast

(* TODO: this is actually a mixture of the two variants given in PLM; adjust. *)
AOT_theorem "reductio-aa:1":
  assumes \<open>\<not>\<phi> \<^bold>\<turnstile> \<not>\<psi>\<close> and \<open>\<not>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<phi>\<close>
  using "\<rightarrow>I" "\<not>\<not>E" MT(2) assms by blast
AOT_theorem "reductio-aa:2":
  assumes \<open>\<phi> \<^bold>\<turnstile> \<not>\<psi>\<close> and \<open>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using "reductio-aa:1" assms by blast
lemmas "RAA" = "reductio-aa:1" "reductio-aa:2"

AOT_theorem "exc-mid": \<open>\<phi> \<or> \<not>\<phi>\<close>
  using "df-rules-formulas[4]" "if-p-then-p" MP AOT_disj by blast

AOT_theorem "non-contradiction": \<open>\<not>(\<phi> & \<not>\<phi>)\<close>
  using "df-rules-formulas[3]" MT(2) "useful-tautologies:2" AOT_conj by blast

AOT_theorem "con-dis-taut:1": \<open>(\<phi> & \<psi>) \<rightarrow> \<phi>\<close>
  by (meson "\<rightarrow>I" "df-rules-formulas[3]" MP RAA(1) AOT_conj)
AOT_theorem "con-dis-taut:2": \<open>(\<phi> & \<psi>) \<rightarrow> \<psi>\<close>
  by (metis "\<rightarrow>I" "df-rules-formulas[3]" MT(2) RAA(2) "\<not>\<not>E" AOT_conj)
lemmas "Conjunction Simplification" = "con-dis-taut:1" "con-dis-taut:2"

AOT_theorem "con-dis-taut:3": \<open>\<phi> \<rightarrow> (\<phi> \<or> \<psi>)\<close>
  by (meson "contraposition:1[2]" "df-rules-formulas[4]" MP "\<rightarrow>I" AOT_disj)
AOT_theorem "con-dis-taut:4": \<open>\<psi> \<rightarrow> (\<phi> \<or> \<psi>)\<close>
  using "Hypothetical Syllogism" "df-rules-formulas[4]" "pl:1"[axiom_inst] AOT_disj by blast
lemmas "Disjunction Addition" = "con-dis-taut:3" "con-dis-taut:4"

AOT_theorem "con-dis-taut:5": \<open>\<phi> \<rightarrow> (\<psi> \<rightarrow> (\<phi> & \<psi>))\<close>
  by (metis "contraposition:2" "Hypothetical Syllogism" "\<rightarrow>I" "df-rules-formulas[4]" AOT_conj)
lemmas Adjunction = "con-dis-taut:5"

AOT_theorem "con-dis-taut:6": \<open>(\<phi> & \<phi>) \<equiv> \<phi>\<close>
  by (metis Adjunction "\<rightarrow>I" "df-rules-formulas[4]" MP "Conjunction Simplification"(1) AOT_equiv)
lemmas "Idempotence of &" = "con-dis-taut:6"

AOT_theorem "con-dis-taut:7": \<open>(\<phi> \<or> \<phi>) \<equiv> \<phi>\<close>
proof -
  {
    AOT_assume \<open>\<phi> \<or> \<phi>\<close>
    AOT_hence \<open>\<not>\<phi> \<rightarrow> \<phi>\<close>
      using AOT_disj[THEN "df-rules-formulas[3]"] MP by blast
    AOT_hence \<open>\<phi>\<close> using "if-p-then-p" RAA(1) MP by blast
  }
  moreover {
    AOT_assume \<open>\<phi>\<close>
    AOT_hence \<open>\<phi> \<or> \<phi>\<close> using "Disjunction Addition"(1) MP by blast
  }
  ultimately AOT_show \<open>(\<phi> \<or> \<phi>) \<equiv> \<phi>\<close>
    using AOT_equiv[THEN "df-rules-formulas[4]"] MP
    by (metis Adjunction "\<rightarrow>I")
qed
lemmas "Idempotence of \<or>" = "con-dis-taut:7"


AOT_theorem "con-dis-i-e:1": assumes \<open>\<phi>\<close> and \<open>\<psi>\<close> shows \<open>\<phi> & \<psi>\<close>
  using Adjunction MP assms by blast
lemmas "&I" = "con-dis-i-e:1"

AOT_theorem "con-dis-i-e:2:a": assumes \<open>\<phi> & \<psi>\<close> shows \<open>\<phi>\<close>
  using "Conjunction Simplification"(1) MP assms by blast
AOT_theorem "con-dis-i-e:2:b": assumes \<open>\<phi> & \<psi>\<close> shows \<open>\<psi>\<close>
  using "Conjunction Simplification"(2) MP assms by blast
lemmas "&E" = "con-dis-i-e:2:a" "con-dis-i-e:2:b"

AOT_theorem "con-dis-i-e:3:a": assumes \<open>\<phi>\<close> shows \<open>\<phi> \<or> \<psi>\<close>
  using "Disjunction Addition"(1) MP assms by blast
AOT_theorem "con-dis-i-e:3:b": assumes \<open>\<psi>\<close> shows \<open>\<phi> \<or> \<psi>\<close>
  using "Disjunction Addition"(2) MP assms by blast
AOT_theorem "con-dis-i-e:3:c": assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<phi> \<rightarrow> \<chi>\<close> and \<open>\<psi> \<rightarrow> \<Theta>\<close> shows \<open>\<chi> \<or> \<Theta>\<close>
  by (metis "con-dis-i-e:3:a" "Disjunction Addition"(2) "df-rules-formulas[3]" MT(1) RAA(1) AOT_disj assms)
lemmas "\<or>I" = "con-dis-i-e:3:a" "con-dis-i-e:3:b" "con-dis-i-e:3:c"

AOT_theorem "con-dis-i-e:4:a": assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<phi> \<rightarrow> \<chi>\<close> and \<open>\<psi> \<rightarrow> \<chi>\<close> shows \<open>\<chi>\<close>
  by (metis MP RAA(2) "df-rules-formulas[3]" AOT_disj assms)
AOT_theorem "con-dis-i-e:4:b": assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<not>\<phi>\<close> shows \<open>\<psi>\<close>
  using "con-dis-i-e:4:a" RAA(1) "\<rightarrow>I" assms by blast
AOT_theorem "con-dis-i-e:4:c": assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<not>\<psi>\<close> shows \<open>\<phi>\<close>
  using "con-dis-i-e:4:a" RAA(1) "\<rightarrow>I" assms by blast
lemmas "\<or>E" = "con-dis-i-e:4:a" "con-dis-i-e:4:b" "con-dis-i-e:4:c"

AOT_theorem "raa-cor:1": assumes \<open>\<not>\<phi> \<^bold>\<turnstile> \<psi> & \<not>\<psi>\<close> shows \<open>\<phi>\<close>
  using "&E" "\<or>E"(3) "\<or>I"(2) RAA(2) assms by blast
AOT_theorem "raa-cor:2": assumes \<open>\<phi> \<^bold>\<turnstile> \<psi> & \<not>\<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using "raa-cor:1" assms by blast
AOT_theorem "raa-cor:3": assumes \<open>\<phi>\<close> and \<open>\<not>\<psi> \<^bold>\<turnstile> \<not>\<phi>\<close> shows \<open>\<psi>\<close>
  using RAA assms by blast
AOT_theorem "raa-cor:4": assumes \<open>\<not>\<phi>\<close> and \<open>\<not>\<psi> \<^bold>\<turnstile> \<phi>\<close> shows \<open>\<psi>\<close>
  using RAA assms by blast
AOT_theorem "raa-cor:5": assumes \<open>\<phi>\<close> and \<open>\<psi> \<^bold>\<turnstile> \<not>\<phi>\<close> shows \<open>\<not>\<psi>\<close>
  using RAA assms by blast
AOT_theorem "raa-cor:6": assumes \<open>\<not>\<phi>\<close> and \<open>\<psi> \<^bold>\<turnstile> \<phi>\<close> shows \<open>\<not>\<psi>\<close>
  using RAA assms by blast

(* TODO: note these need manual introduction rules *)
AOT_theorem "oth-class-taut:1:a": \<open>(\<phi> \<rightarrow> \<psi>) \<equiv> \<not>(\<phi> & \<not>\<psi>)\<close>
  by (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"])
     (metis "&E" "&I" "raa-cor:3" "\<rightarrow>I" MP)
AOT_theorem "oth-class-taut:1:b": \<open>\<not>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<phi> & \<not>\<psi>)\<close>
  by (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"])
     (metis "&E" "&I" "raa-cor:3" "\<rightarrow>I" MP)
AOT_theorem "oth-class-taut:1:c": \<open>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<not>\<phi> \<or> \<psi>)\<close>
  by (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"])
     (metis "&I" "\<or>I"(1, 2) "\<or>E"(3) "\<rightarrow>I" MP "raa-cor:1")

AOT_theorem "oth-class-taut:2:a": \<open>(\<phi> & \<psi>) \<equiv> (\<psi> & \<phi>)\<close>
  by (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"])
     (meson "&I" "&E" "\<rightarrow>I")
lemmas "Commutativity of &" = "oth-class-taut:2:a"
AOT_theorem "oth-class-taut:2:b": \<open>(\<phi> & (\<psi> & \<chi>)) \<equiv> ((\<phi> & \<psi>) & \<chi>)\<close>
  by (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"])
     (metis "&I" "&E" "\<rightarrow>I")
lemmas "Associativity of &" = "oth-class-taut:2:b"
AOT_theorem "oth-class-taut:2:c": \<open>(\<phi> \<or> \<psi>) \<equiv> (\<psi> \<or> \<phi>)\<close>
  by (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"])
     (metis "&I" "\<or>I"(1, 2) "\<or>E"(1) "\<rightarrow>I")
lemmas "Commutativity of \<or>" = "oth-class-taut:2:c"
AOT_theorem "oth-class-taut:2:d": \<open>(\<phi> \<or> (\<psi> \<or> \<chi>)) \<equiv> ((\<phi> \<or> \<psi>) \<or> \<chi>)\<close>
  by (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"])
     (metis "&I" "\<or>I"(1, 2) "\<or>E"(1) "\<rightarrow>I")
lemmas "Associativity of \<or>" = "oth-class-taut:2:d"
AOT_theorem "oth-class-taut:2:e": \<open>(\<phi> \<equiv> \<psi>) \<equiv> (\<psi> \<equiv> \<phi>)\<close>
  by (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"]; rule "&I";
      metis "&I" "df-rules-formulas[4]" AOT_equiv "&E" "Hypothetical Syllogism" "\<rightarrow>I" "df-rules-formulas[3]")
lemmas "Commutativity of \<equiv>" = "oth-class-taut:2:e"
AOT_theorem "oth-class-taut:2:f": \<open>(\<phi> \<equiv> (\<psi> \<equiv> \<chi>)) \<equiv> ((\<phi> \<equiv> \<psi>) \<equiv> \<chi>)\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I"
  by metis
lemmas "Associativity of \<equiv>" = "oth-class-taut:2:f"

AOT_theorem "oth-class-taut:3:a": \<open>\<phi> \<equiv> \<phi>\<close>
  using "&I" "vdash-properties:6" "if-p-then-p" "df-rules-formulas[4]" AOT_equiv by blast
AOT_theorem "oth-class-taut:3:b": \<open>\<phi> \<equiv> \<not>\<not>\<phi>\<close>
  using "&I" "useful-tautologies:1" "useful-tautologies:2" "vdash-properties:6" "df-rules-formulas[4]" AOT_equiv by blast
AOT_theorem "oth-class-taut:3:c": \<open>\<not>(\<phi> \<equiv> \<not>\<phi>)\<close>
  by (metis "&E" "\<rightarrow>E" RAA "df-rules-formulas[3]" AOT_equiv)

AOT_theorem "oth-class-taut:4:a": \<open>(\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>))\<close>
  by (metis "\<rightarrow>E" "\<rightarrow>I")
AOT_theorem "oth-class-taut:4:b": \<open>(\<phi> \<equiv> \<psi>) \<equiv> (\<not>\<phi> \<equiv> \<not>\<psi>)\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" RAA by metis
AOT_theorem "oth-class-taut:4:c": \<open>(\<phi> \<equiv> \<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<chi>) \<equiv> (\<psi> \<rightarrow> \<chi>))\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
AOT_theorem "oth-class-taut:4:d": \<open>(\<phi> \<equiv> \<psi>) \<rightarrow> ((\<chi> \<rightarrow> \<phi>) \<equiv> (\<chi> \<rightarrow> \<psi>))\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
AOT_theorem "oth-class-taut:4:e": \<open>(\<phi> \<equiv> \<psi>) \<rightarrow> ((\<phi> & \<chi>) \<equiv> (\<psi> & \<chi>))\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
AOT_theorem "oth-class-taut:4:f": \<open>(\<phi> \<equiv> \<psi>) \<rightarrow> ((\<chi> & \<phi>) \<equiv> (\<chi> & \<psi>))\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
(* TODO: nicer proof *)
AOT_theorem "oth-class-taut:4:g": \<open>(\<phi> \<equiv> \<psi>) \<equiv> ((\<phi> & \<psi>) \<or> (\<not>\<phi> & \<not>\<psi>))\<close>
  apply (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"]; rule "&I"; rule "\<rightarrow>I")
   apply (drule AOT_equiv[THEN "df-rules-formulas[3]", THEN "\<rightarrow>E"])
   apply (metis "&I" "&E" "\<or>I"(1,2) MT(1) "raa-cor:3")
  apply (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"]; rule "&I"; rule "\<rightarrow>I")
  using "&E" "\<or>E"(2) "raa-cor:3" by blast+
AOT_theorem "oth-class-taut:4:h": \<open>\<not>(\<phi> \<equiv> \<psi>) \<equiv> ((\<phi> & \<not>\<psi>) \<or> (\<not>\<phi> & \<psi>))\<close>
  apply (rule AOT_equiv[THEN "df-rules-formulas[4]", THEN "\<rightarrow>E"]; rule "&I"; rule "\<rightarrow>I")
  apply (metis "&I" "\<or>I"(1, 2) "\<rightarrow>I" MT(1) "df-rules-formulas[4]" "raa-cor:3" AOT_equiv)
  by (metis "&E" "\<or>E"(2) "\<rightarrow>E" "df-rules-formulas[3]" "raa-cor:3" AOT_equiv)
AOT_theorem "oth-class-taut:5:a": \<open>(\<phi> & \<psi>) \<equiv> \<not>(\<not>\<phi> \<or> \<not>\<psi>)\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis
AOT_theorem "oth-class-taut:5:b": \<open>(\<phi> \<or> \<psi>) \<equiv> \<not>(\<not>\<phi> & \<not>\<psi>)\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis
AOT_theorem "oth-class-taut:5:c": \<open>\<not>(\<phi> & \<psi>) \<equiv> (\<not>\<phi> \<or> \<not>\<psi>)\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis
AOT_theorem "oth-class-taut:5:d": \<open>\<not>(\<phi> \<or> \<psi>) \<equiv> (\<not>\<phi> & \<not>\<psi>)\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis

lemmas DeMorgan = "oth-class-taut:5:c" "oth-class-taut:5:d"

AOT_theorem "oth-class-taut:6:a": \<open>(\<phi> & (\<psi> \<or> \<chi>)) \<equiv> ((\<phi> & \<psi>) \<or> (\<phi> & \<chi>))\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis
AOT_theorem "oth-class-taut:6:b": \<open>(\<phi> \<or> (\<psi> & \<chi>)) \<equiv> ((\<phi> \<or> \<psi>) & (\<phi> \<or> \<chi>))\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis

AOT_theorem "oth-class-taut:7:a": \<open>((\<phi> & \<psi>) \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>))\<close>
  by (metis "&I" "\<rightarrow>E" "\<rightarrow>I")
lemmas Exportation = "oth-class-taut:7:a"
AOT_theorem "oth-class-taut:7:b": \<open>(\<phi> \<rightarrow> (\<psi> \<rightarrow>\<chi>)) \<rightarrow> ((\<phi> & \<psi>) \<rightarrow> \<chi>)\<close>
  by (metis "&E" "\<rightarrow>E" "\<rightarrow>I")
lemmas Importation = "oth-class-taut:7:b"

AOT_theorem "oth-class-taut:8:a": \<open>(\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)) \<equiv> (\<psi> \<rightarrow> (\<phi> \<rightarrow> \<chi>))\<close>
  using AOT_equiv[THEN "df-rules-formulas[4]"] "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
lemmas Permutation = "oth-class-taut:8:a"
AOT_theorem "oth-class-taut:8:b": \<open>(\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> (\<psi> & \<chi>)))\<close>
  by (metis "&I" "\<rightarrow>E" "\<rightarrow>I")
lemmas Composition = "oth-class-taut:8:b"
AOT_theorem "oth-class-taut:8:c": \<open>(\<phi> \<rightarrow> \<chi>) \<rightarrow> ((\<psi> \<rightarrow> \<chi>) \<rightarrow> ((\<psi> \<or> \<chi>) \<rightarrow> \<chi>))\<close>
  by (metis "\<or>E"(2) "\<rightarrow>E" "\<rightarrow>I" RAA(1))
AOT_theorem "oth-class-taut:8:d": \<open>((\<phi> \<rightarrow> \<psi>) & (\<chi> \<rightarrow> \<Theta>)) \<rightarrow> ((\<phi> & \<chi>) \<rightarrow> (\<psi> & \<Theta>))\<close>
  by (metis "&E" "&I" "\<rightarrow>E" "\<rightarrow>I")
lemmas "Double Composition" = "oth-class-taut:8:d"
AOT_theorem "oth-class-taut:8:e": \<open>((\<phi> & \<psi>) \<equiv> (\<phi> & \<chi>)) \<equiv> (\<phi> \<rightarrow> (\<psi> \<equiv> \<chi>))\<close>
  by (metis AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I")
AOT_theorem "oth-class-taut:8:f": \<open>((\<phi> & \<psi>) \<equiv> (\<chi> & \<psi>)) \<equiv> (\<psi> \<rightarrow> (\<phi> \<equiv> \<chi>))\<close>
  by (metis AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I")
AOT_theorem "oth-class-taut:8:g": \<open>(\<psi> \<equiv> \<chi>) \<rightarrow> ((\<phi> \<or> \<psi>) \<equiv> (\<phi> \<or> \<chi>))\<close>
  by (metis AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E"(1))
AOT_theorem "oth-class-taut:8:h": \<open>(\<psi> \<equiv> \<chi>) \<rightarrow> ((\<psi> \<or> \<phi>) \<equiv> (\<chi> \<or> \<phi>))\<close>
  by (metis AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E"(1))
AOT_theorem "oth-class-taut:8:i": \<open>(\<phi> \<equiv> (\<psi> & \<chi>)) \<rightarrow> (\<psi> \<rightarrow> (\<phi> \<equiv> \<chi>))\<close>
  by (metis AOT_equiv[THEN "df-rules-formulas[4]"] AOT_equiv[THEN "df-rules-formulas[3]"]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I")

AOT_theorem "intro-elim:1": assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<phi> \<equiv> \<chi>\<close> and \<open>\<psi> \<equiv> \<Theta>\<close> shows \<open>\<chi> \<or> \<Theta>\<close>
  by (metis assms "\<or>I"(1, 2) "\<or>E"(1) AOT_equiv[THEN "df-rules-formulas[3]"] "\<rightarrow>I" "\<rightarrow>E" "&E"(1))

AOT_theorem "intro-elim:2": assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<psi> \<rightarrow> \<phi>\<close> shows \<open>\<phi> \<equiv> \<psi>\<close>
  by (meson "&I" AOT_equiv "df-rules-formulas[4]" MP assms)
lemmas "\<equiv>I" = "intro-elim:2"

AOT_theorem "intro-elim:3:a": assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<phi>\<close> shows \<open>\<psi>\<close>
  by (metis "\<or>I"(1) "\<rightarrow>I" "\<or>E"(1) "intro-elim:1" assms)
AOT_theorem "intro-elim:3:b": assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<psi>\<close> shows \<open>\<phi>\<close>
  using "intro-elim:3:a" "Commutativity of \<equiv>" assms by blast
AOT_theorem "intro-elim:3:c": assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<not>\<phi>\<close> shows \<open>\<not>\<psi>\<close>
  using "intro-elim:3:b" "raa-cor:3" assms by blast
AOT_theorem "intro-elim:3:d": assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<not>\<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using "intro-elim:3:a" "raa-cor:3" assms by blast
AOT_theorem "intro-elim:3:e": assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<psi> \<equiv> \<chi>\<close> shows \<open>\<phi> \<equiv> \<chi>\<close>
  by (metis "\<equiv>I" "\<rightarrow>I" "intro-elim:3:a" "intro-elim:3:b" assms)
declare "intro-elim:3:e"[trans]
AOT_theorem "intro-elim:3:f": assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<phi> \<equiv> \<chi>\<close> shows \<open>\<chi> \<equiv> \<psi>\<close>
  by (metis "\<equiv>I" "\<rightarrow>I" "intro-elim:3:a" "intro-elim:3:b" assms)
lemmas "\<equiv>E" = "intro-elim:3:a" "intro-elim:3:b" "intro-elim:3:c" "intro-elim:3:d" "intro-elim:3:e" "intro-elim:3:f"

declare "Commutativity of \<equiv>"[THEN "\<equiv>E"(1), sym]

AOT_theorem "rule-eq-df:1": assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<phi> \<equiv> \<psi>\<close>
  by (simp add: "\<equiv>I" "df-rules-formulas[3]" "df-rules-formulas[4]" assms)
lemmas "\<equiv>Df" = "rule-eq-df:1"
AOT_theorem "rule-eq-df:2": assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> and \<open>\<phi>\<close> shows \<open>\<psi>\<close>
  using "\<equiv>Df" "\<equiv>E"(1) assms by blast
lemmas "\<equiv>\<^sub>d\<^sub>fE" = "rule-eq-df:2"
AOT_theorem "rule-eq-df:3": assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> and \<open>\<psi>\<close> shows \<open>\<phi>\<close>
  using "\<equiv>Df" "\<equiv>E"(2) assms by blast
lemmas "\<equiv>\<^sub>d\<^sub>fI" = "rule-eq-df:3"

AOT_theorem  "df-simplify:1": assumes \<open>\<phi> \<equiv> (\<psi> & \<chi>)\<close> and \<open>\<psi>\<close> shows \<open>\<phi> \<equiv> \<chi>\<close>
  by (metis "&E"(2) "&I" "\<equiv>E"(1, 2) "\<equiv>I" "\<rightarrow>I" assms)
(* TODO: this is a slight variation from PLM *)
AOT_theorem  "df-simplify:2": assumes \<open>\<phi> \<equiv> (\<psi> & \<chi>)\<close> and \<open>\<chi>\<close> shows \<open>\<phi> \<equiv> \<psi>\<close>
  by (metis "&E"(1) "&I" "\<equiv>E"(1, 2) "\<equiv>I" "\<rightarrow>I" assms)
lemmas "\<equiv>S" = "df-simplify:1"  "df-simplify:2"

AOT_theorem "rule-ui:1": assumes \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> and \<open>\<tau>\<down>\<close> shows \<open>\<phi>{\<tau>}\<close>
  using "\<rightarrow>E" "cqt:1"[axiom_inst] assms by blast
AOT_theorem "rule-ui:2[const_var]": assumes \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> shows \<open>\<phi>{\<beta>}\<close>
  by (simp add: "rule-ui:1" "cqt:2[const_var]"[axiom_inst] assms)
(* TODO: precise proviso in PLM *)
AOT_theorem "rule-ui:2[lambda]":
  assumes \<open>\<forall>F \<phi>{F}\<close> and \<open>INSTANCE_OF_CQT_2(\<psi>)\<close>
  shows \<open>\<phi>{[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]}\<close>
  by (simp add: "rule-ui:1" "cqt:2[lambda]"[axiom_inst] assms)
AOT_theorem "rule-ui:3": assumes \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> shows \<open>\<phi>{\<alpha>}\<close>
  by (simp add: "rule-ui:2[const_var]" assms)
lemmas "\<forall>E" = "rule-ui:1" "rule-ui:2[const_var]" "rule-ui:2[lambda]" "rule-ui:3"

AOT_theorem "cqt-orig:1[const_var]": \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>}\<close> by (simp add: "\<forall>E"(2) "\<rightarrow>I")
AOT_theorem "cqt-orig:1[lambda]":
  assumes \<open>INSTANCE_OF_CQT_2(\<psi>)\<close>
  shows \<open>\<forall>F \<phi>{F} \<rightarrow> \<phi>{[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]}\<close>
  by (simp add: "\<forall>E"(3) "\<rightarrow>I" assms)
AOT_theorem "cqt-orig:2": \<open>\<forall>\<alpha> (\<phi> \<rightarrow> \<psi>{\<alpha>}) \<rightarrow> (\<phi> \<rightarrow> \<forall>\<alpha> \<psi>{\<alpha>})\<close>
  by (metis "\<rightarrow>I" GEN "vdash-properties:6" "\<forall>E"(4))
AOT_theorem "cqt-orig:3": \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}\<close> using "cqt-orig:1[const_var]" .

(* TODO: work out difference to GEN *)
AOT_theorem universal: assumes \<open>for arbitrary \<beta>: \<phi>{\<beta>}\<close> shows \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
  using GEN assms .
lemmas "\<forall>I" = universal

(* Generalized mechanism for "\<forall>I" followed by \<forall>E *)
ML\<open>
fun get_instantiated_allI ctxt varname thm = let
val trm = Thm.concl_of thm
val trm = case trm of (@{const Trueprop} $ (@{const AOT_model_valid_in} $ _ $ x)) => x
                      | _ => raise Term.TERM ("Expected simple theorem.", [trm])
fun extractVars (Const (\<^const_name>\<open>AOT_term_of_var\<close>, _) $ Var v) =
    (if fst (fst v) = fst varname then [Var v] else []) (* TODO: care about the index? *)
  | extractVars (t1 $ t2) = extractVars t1 @ extractVars t2
  | extractVars (Abs (_, _, t)) = extractVars t
  | extractVars _ = []
val vars = extractVars trm
val vars = fold Term.add_vars vars []
val var = hd vars
val trmty = case (snd var) of (Type (\<^type_name>\<open>AOT_var\<close>, [t])) => (t)
              | _ => raise Term.TYPE ("Expected variable type.", [snd var], [Var var])
val trm = Abs (Term.string_of_vname (fst var), trmty, Term.abstract_over (
      Const (\<^const_name>\<open>AOT_term_of_var\<close>, Type ("fun", [snd var, trmty]))
       $ Var var, trm))
val trm = Thm.cterm_of (Context.proof_of ctxt) trm
val ty = hd (Term.add_tvars (Thm.prop_of @{thm "\<forall>I"}) [])
val typ = Thm.ctyp_of (Context.proof_of ctxt) trmty
val allthm = Drule.instantiate_normalize ([(ty, typ)],[]) @{thm "\<forall>I"}
val phi = hd (Term.add_vars (Thm.prop_of allthm) [])
val allthm = Drule.instantiate_normalize ([],[(phi,trm)]) allthm
in
allthm
end
\<close>

attribute_setup "\<forall>I" =
  \<open>Scan.lift (Scan.repeat1 Args.var) >> (fn args => Thm.rule_attribute []
  (fn ctxt => fn thm => fold (fn arg => fn thm => thm RS get_instantiated_allI ctxt arg thm) args thm))\<close>
  "Quantify over a variable in a theorem using GEN."

attribute_setup "unvarify" =
  \<open>Scan.lift (Scan.repeat1 Args.var) >> (fn args => Thm.rule_attribute []
  (fn ctxt => fn thm =>
    let
    val thm = fold (fn arg => fn thm => thm RS get_instantiated_allI ctxt arg thm) args thm
    val thm = fold (fn _ => fn thm => thm RS @{thm "\<forall>E"(1)}) args thm
    in
     thm
    end))\<close>
  "Generalize a statement about variables to a statement about denoting terms."

(* TODO: rereplace-lem does not apply to the embedding *)

AOT_theorem "cqt-basic:1": \<open>\<forall>\<alpha>\<forall>\<beta> \<phi>{\<alpha>,\<beta>} \<equiv> \<forall>\<beta>\<forall>\<alpha> \<phi>{\<alpha>,\<beta>}\<close>
  by (metis "\<equiv>I" "\<forall>E"(2) "\<forall>I" "\<rightarrow>I")

AOT_theorem "cqt-basic:2": \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) \<equiv> (\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}))\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  AOT_hence \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) by blast
  AOT_hence \<open>\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}\<close> and \<open>\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}\<close> for \<alpha>
    using "\<equiv>E"(1,2) "\<rightarrow>I" by blast+
  AOT_thus \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
    by (auto intro: "&I" "\<forall>I")
next
  AOT_assume \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
  AOT_hence \<open>\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}\<close> and \<open>\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}\<close> for \<alpha>
    using "\<forall>E"(2) "&E" by blast+
  AOT_hence \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> for \<alpha>
    using "\<equiv>I" by blast
  AOT_thus \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> by (auto intro: "\<forall>I")
qed

AOT_theorem "cqt-basic:3": \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<alpha> \<psi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  AOT_hence 1: \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) by blast
  {
    AOT_assume \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
    AOT_hence \<open>\<forall>\<alpha> \<psi>{\<alpha>}\<close> using 1 "\<forall>I" "\<forall>E"(4) "\<equiv>E" by metis
  }
  moreover {
    AOT_assume \<open>\<forall>\<alpha> \<psi>{\<alpha>}\<close>
    AOT_hence \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> using 1 "\<forall>I" "\<forall>E"(4) "\<equiv>E" by metis
  }
  ultimately AOT_show \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<alpha> \<psi>{\<alpha>}\<close>
    using "\<equiv>I" "\<rightarrow>I" by auto
qed

AOT_theorem "cqt-basic:4": \<open>\<forall>\<alpha>(\<phi>{\<alpha>} & \<psi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> \<phi>{\<alpha>} & \<forall>\<alpha> \<psi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} & \<psi>{\<alpha>})\<close>
  AOT_have \<open>\<phi>{\<alpha>}\<close> and \<open>\<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) 0 "&E" by blast+
  AOT_thus \<open>\<forall>\<alpha> \<phi>{\<alpha>} & \<forall>\<alpha> \<psi>{\<alpha>}\<close>
    by (auto intro: "\<forall>I" "&I")
qed

AOT_theorem "cqt-basic:5": \<open>(\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n(\<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n})) \<rightarrow> \<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close>
  using "cqt-orig:3" by blast

AOT_theorem "cqt-basic:6": \<open>\<forall>\<alpha>\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<alpha> \<phi>{\<alpha>}\<close>
  by (meson "\<equiv>I" "\<rightarrow>I" GEN "cqt-orig:1[const_var]")

AOT_theorem "cqt-basic:7": \<open>(\<phi> \<rightarrow> \<forall>\<alpha> \<psi>{\<alpha>}) \<equiv> \<forall>\<alpha>(\<phi> \<rightarrow> \<psi>{\<alpha>})\<close>
  by (metis "\<rightarrow>I" "vdash-properties:6" "rule-ui:3" "\<equiv>I" GEN)

AOT_theorem "cqt-basic:8": \<open>(\<forall>\<alpha> \<phi>{\<alpha>} \<or> \<forall>\<alpha> \<psi>{\<alpha>}) \<rightarrow> \<forall>\<alpha> (\<phi>{\<alpha>} \<or> \<psi>{\<alpha>})\<close>
  by (simp add: "\<or>I"(3) "\<rightarrow>I" GEN "cqt-orig:1[const_var]")

AOT_theorem "cqt-basic:9": \<open>(\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})) \<rightarrow> \<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})\<close>
proof -
  {
    AOT_assume \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>})\<close>
    moreover AOT_assume \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})\<close>
    ultimately AOT_have \<open>\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}\<close> and \<open>\<psi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast+
    AOT_hence \<open>\<phi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>}\<close> for \<alpha> by (metis "\<rightarrow>E" "\<rightarrow>I")
    AOT_hence \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})\<close> using "\<forall>I" by fast
  }
  thus ?thesis using "&I" "\<rightarrow>I" "&E" by meson
qed

AOT_theorem "cqt-basic:10": \<open>(\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})) \<rightarrow> \<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I"; rule "\<forall>I")
  fix \<beta>
  AOT_assume \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
  AOT_hence \<open>\<phi>{\<beta>} \<equiv> \<psi>{\<beta>}\<close> and \<open>\<psi>{\<beta>} \<equiv> \<chi>{\<beta>}\<close> using "&E" "\<forall>E" by blast+
  AOT_thus \<open>\<phi>{\<beta>} \<equiv> \<chi>{\<beta>}\<close> using "\<equiv>I" "\<equiv>E" by blast
qed

AOT_theorem "cqt-basic:11": \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) \<equiv> \<forall>\<alpha> (\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  {
    fix \<alpha>
    AOT_have \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> using 0 "\<forall>E" by blast
    AOT_hence \<open>\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>}\<close> using "\<equiv>I" "\<equiv>E" "\<rightarrow>I" "\<rightarrow>E" by metis
  }
  AOT_thus \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close> using "\<forall>I" by fast
next
  AOT_assume 0: \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close>
  {
    fix \<alpha>
    AOT_have \<open>\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>}\<close> using 0 "\<forall>E" by blast
    AOT_hence \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> using "\<equiv>I" "\<equiv>E" "\<rightarrow>I" "\<rightarrow>E" by metis
  }
  AOT_thus \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> using "\<forall>I" by fast
qed

AOT_theorem "cqt-basic:12": \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
  by (simp add: "\<forall>E"(2) "\<rightarrow>I" GEN)

AOT_theorem "cqt-basic:13": \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<beta> \<phi>{\<beta>}\<close>
  using "\<equiv>I" "\<rightarrow>I" by blast

AOT_theorem "cqt-basic:14": \<open>(\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n (\<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} \<rightarrow> \<psi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n})) \<rightarrow> ((\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}) \<rightarrow> (\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<psi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}))\<close>
  using "cqt:3"[axiom_inst] by auto

AOT_theorem "cqt-basic:15": \<open>(\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n (\<phi> \<rightarrow> \<psi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n})) \<rightarrow> (\<phi> \<rightarrow> (\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<psi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}))\<close>
  using "cqt-orig:2" by auto

(* TODO: once more the same in the embedding... need to distinguish these better *)
AOT_theorem "universal-cor": assumes \<open>for arbitrary \<beta>: \<phi>{\<beta>}\<close>  shows \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
  using GEN assms .

AOT_theorem "existential:1": assumes \<open>\<phi>{\<tau>}\<close> and \<open>\<tau>\<down>\<close> shows \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
proof(rule "raa-cor:1")
  AOT_assume \<open>\<not>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  AOT_hence \<open>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
    using "\<equiv>\<^sub>d\<^sub>fI" AOT_exists RAA "&I" by blast
  AOT_hence \<open>\<not>\<phi>{\<tau>}\<close> using assms(2) "\<forall>E"(1) "\<rightarrow>E" by blast
  AOT_thus \<open>\<phi>{\<tau>} & \<not>\<phi>{\<tau>}\<close> using assms(1) "&I" by blast
qed

AOT_theorem "existential:2[const_var]": assumes \<open>\<phi>{\<beta>}\<close> shows \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  using "existential:1" "cqt:2[const_var]"[axiom_inst] assms by blast

AOT_theorem "existential:2[lambda]":
  assumes \<open>\<phi>{[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]}\<close> and \<open>INSTANCE_OF_CQT_2(\<psi>)\<close>
  shows \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  using "existential:1" "cqt:2[lambda]"[axiom_inst] assms by blast
lemmas "\<exists>I" = "existential:1" "existential:2[const_var]" "existential:2[lambda]" 

AOT_theorem "instantiation":
  assumes \<open>for arbitrary \<beta>: \<phi>{\<beta>} \<^bold>\<turnstile> \<psi>\<close> and \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  shows \<open>\<psi>\<close>
  by (metis (no_types, lifting) "\<equiv>\<^sub>d\<^sub>fE" GEN "raa-cor:3" AOT_exists assms)
lemmas "\<exists>E" = "instantiation"

AOT_theorem "cqt-further:1": \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<exists>\<alpha> \<phi>{\<alpha>}\<close>
  using "\<forall>E"(4) "\<exists>I"(2) "\<rightarrow>I" by metis

AOT_theorem "cqt-further:2": \<open>\<not>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<exists>\<alpha> \<not>\<phi>{\<alpha>}\<close>
  using "\<forall>I" "\<exists>I"(2) "\<rightarrow>I" RAA by metis

AOT_theorem "cqt-further:3": \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<not>\<exists>\<alpha> \<not>\<phi>{\<alpha>}\<close>
  using "\<forall>E"(4) "\<exists>E" "\<rightarrow>I" RAA
  by (metis "cqt-further:2" "\<equiv>I" "modus-tollens:1")

AOT_theorem "cqt-further:4": \<open>\<not>\<exists>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
  using "\<forall>I" "\<exists>I"(2)"\<rightarrow>I" RAA by metis

AOT_theorem "cqt-further:5": \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<psi>{\<alpha>}) \<rightarrow> (\<exists>\<alpha> \<phi>{\<alpha>} & \<exists>\<alpha> \<psi>{\<alpha>})\<close>
  by (metis (no_types, lifting) "&E" "&I" "\<exists>E" "\<exists>I"(2) "\<rightarrow>I")

AOT_theorem "cqt-further:6": \<open>\<exists>\<alpha> (\<phi>{\<alpha>} \<or> \<psi>{\<alpha>}) \<rightarrow> (\<exists>\<alpha> \<phi>{\<alpha>} \<or> \<exists>\<alpha> \<psi>{\<alpha>})\<close>
  by (metis (mono_tags, lifting) "\<exists>E" "\<exists>I"(2) "\<or>E"(3) "\<or>I"(1, 2) "\<rightarrow>I" RAA(2))

AOT_theorem "cqt-further:7": \<open>\<exists>\<alpha> \<phi>{\<alpha>} \<equiv> \<exists>\<beta> \<phi>{\<beta>}\<close> (* TODO: vacuous in the embedding *)
  by (simp add: "oth-class-taut:3:a")

AOT_theorem "cqt-further:8": \<open>(\<forall>\<alpha> \<phi>{\<alpha>} & \<forall>\<alpha> \<psi>{\<alpha>}) \<rightarrow> \<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  by (metis (mono_tags, lifting) "&E" "\<equiv>I" "\<forall>E"(2) "\<rightarrow>I" GEN)

AOT_theorem "cqt-further:9": \<open>(\<not>\<exists>\<alpha> \<phi>{\<alpha>} & \<not>\<exists>\<alpha> \<psi>{\<alpha>}) \<rightarrow> \<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  by (metis (mono_tags, lifting) "&E" "\<equiv>I" "\<exists>I"(2) "\<rightarrow>I" GEN "raa-cor:4")

AOT_theorem "cqt-further:10": \<open>(\<exists>\<alpha> \<phi>{\<alpha>} & \<not>\<exists>\<alpha> \<psi>{\<alpha>}) \<rightarrow> \<not>\<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_assume 0: \<open>\<exists>\<alpha> \<phi>{\<alpha>} & \<not>\<exists>\<alpha> \<psi>{\<alpha>}\<close>
  then AOT_obtain \<alpha> where \<open>\<phi>{\<alpha>}\<close> using "\<exists>E" "&E"(1) by metis
  moreover AOT_assume \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  ultimately AOT_have \<open>\<psi>{\<alpha>}\<close> using "\<forall>E"(4) "\<equiv>E"(1) by blast
  AOT_hence \<open>\<exists>\<alpha> \<psi>{\<alpha>}\<close> using "\<exists>I" by blast
  AOT_thus \<open>\<exists>\<alpha> \<psi>{\<alpha>} & \<not>\<exists>\<alpha> \<psi>{\<alpha>}\<close> using 0 "&E"(2) "&I" by blast
qed

AOT_theorem "cqt-further:11": \<open>\<exists>\<alpha>\<exists>\<beta> \<phi>{\<alpha>,\<beta>} \<equiv> \<exists>\<beta>\<exists>\<alpha> \<phi>{\<alpha>,\<beta>}\<close>
  using "\<equiv>I" "\<rightarrow>I" "\<exists>I"(2) "\<exists>E" by metis

AOT_theorem "log-prop-prop:1": \<open>[\<lambda> \<phi>]\<down>\<close>
  using "cqt:2[lambda0]"[axiom_inst] by auto

AOT_theorem "log-prop-prop:2": \<open>\<phi>\<down>\<close>
  by (rule "\<equiv>\<^sub>d\<^sub>fI"[OF "existence:3"]) "cqt:2[lambda]"

AOT_theorem "exist-nec": \<open>\<tau>\<down> \<rightarrow> \<box>\<tau>\<down>\<close>
proof -
  AOT_have \<open>\<forall>\<beta> \<box>\<beta>\<down>\<close>
    by (simp add: GEN RN "cqt:2[const_var]"[axiom_inst])
  AOT_thus \<open>\<tau>\<down> \<rightarrow> \<box>\<tau>\<down>\<close>
    using "cqt:1"[axiom_inst] "\<rightarrow>E" by blast
qed

(* TODO: replace this mechanism by a "proof by types" command *)
class AOT_Term_id = AOT_Term +
  assumes "t=t-proper:1"[AOT]: \<open>[v \<Turnstile> \<tau> = \<tau>' \<rightarrow> \<tau>\<down>]\<close>
      and "t=t-proper:2"[AOT]: \<open>[v \<Turnstile> \<tau> = \<tau>' \<rightarrow> \<tau>'\<down>]\<close>

instance \<kappa> :: AOT_Term_id
proof
  AOT_modally_strict {
    AOT_show \<open>\<kappa> = \<kappa>' \<rightarrow> \<kappa>\<down>\<close> for \<kappa> \<kappa>'
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<kappa> = \<kappa>'\<close>
      AOT_hence \<open>O!\<kappa> \<or> A!\<kappa>\<close>
        by (rule "\<or>I"(3)[OF "\<equiv>\<^sub>d\<^sub>fE"[OF "identity:1"]])
           (meson "\<rightarrow>I" "\<or>I"(1) "&E"(1))+
      AOT_thus \<open>\<kappa>\<down>\<close>
        by (rule "\<or>E"(1))
           (metis "cqt:5:a"[axiom_inst] "\<rightarrow>I" "\<rightarrow>E" "&E"(2))+
    qed
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<kappa> = \<kappa>' \<rightarrow> \<kappa>'\<down>\<close> for \<kappa> \<kappa>'
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<kappa> = \<kappa>'\<close>
      AOT_hence \<open>O!\<kappa>' \<or> A!\<kappa>'\<close>
        by (rule "\<or>I"(3)[OF "\<equiv>\<^sub>d\<^sub>fE"[OF "identity:1"]])
           (meson "\<rightarrow>I" "\<or>I" "&E")+
      AOT_thus \<open>\<kappa>'\<down>\<close>
        by (rule "\<or>E"(1))
           (metis "cqt:5:a"[axiom_inst] "\<rightarrow>I" "\<rightarrow>E" "&E"(2))+
    qed
  }
qed

instance rel :: (AOT_\<kappa>s) AOT_Term_id
proof
  AOT_modally_strict {
    AOT_show \<open>\<Pi> = \<Pi>' \<rightarrow> \<Pi>\<down>\<close> for \<Pi> \<Pi>' :: \<open><'a>\<close> (* TODO: how to get rid of the fixes? *)
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<Pi> = \<Pi>'\<close>
      AOT_thus \<open>\<Pi>\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF "identity:3"[of \<Pi> \<Pi>']] "&E" by blast
    qed
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<Pi> = \<Pi>' \<rightarrow> \<Pi>'\<down>\<close> for \<Pi> \<Pi>' :: \<open><'a>\<close> (* TODO: how to get rid of the fixes? *)
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<Pi> = \<Pi>'\<close>
      AOT_thus \<open>\<Pi>'\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF "identity:3"[of \<Pi> \<Pi>']] "&E" by blast
    qed
  }
qed

instance \<o> :: AOT_Term_id
proof
  AOT_modally_strict {
    fix \<phi> \<psi>
    AOT_show \<open>\<phi> = \<psi> \<rightarrow> \<phi>\<down>\<close>
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<phi> = \<psi>\<close>
      AOT_thus \<open>\<phi>\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF "identity:4"[of \<phi> \<psi>]] "&E" by blast
    qed
  }
next
  AOT_modally_strict {
    fix \<phi> \<psi>
    AOT_show \<open>\<phi> = \<psi> \<rightarrow> \<psi>\<down>\<close>
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<phi> = \<psi>\<close>
      AOT_thus \<open>\<psi>\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF "identity:4"[of \<phi> \<psi>]] "&E" by blast
    qed
  }
qed

instance prod :: (AOT_Term_id, AOT_Term_id) AOT_Term_id
proof
  AOT_modally_strict {
    fix \<tau> \<tau>' :: \<open>'a\<times>'b\<close>
    AOT_show \<open>\<tau> = \<tau>' \<rightarrow> \<tau>\<down>\<close>
    proof (induct \<tau>; induct \<tau>'; rule "\<rightarrow>I")
      fix \<tau>\<^sub>1 \<tau>\<^sub>1' :: 'a and \<tau>\<^sub>2  \<tau>\<^sub>2' :: 'b
      AOT_assume \<open>\<guillemotleft>(\<tau>\<^sub>1, \<tau>\<^sub>2)\<guillemotright> = \<guillemotleft>(\<tau>\<^sub>1', \<tau>\<^sub>2')\<guillemotright>\<close>
      AOT_hence \<open>(\<tau>\<^sub>1 = \<tau>\<^sub>1') & (\<tau>\<^sub>2 = \<tau>\<^sub>2')\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" tuple_identity_1)
      AOT_hence \<open>\<tau>\<^sub>1\<down>\<close> and \<open>\<tau>\<^sub>2\<down>\<close> using "t=t-proper:1" "&E" "vdash-properties:10" by blast+
      AOT_thus \<open>\<guillemotleft>(\<tau>\<^sub>1, \<tau>\<^sub>2)\<guillemotright>\<down>\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" tuple_denotes)
    qed
  }
next
  AOT_modally_strict {
    fix \<tau> \<tau>' :: \<open>'a\<times>'b\<close>
    AOT_show \<open>\<tau> = \<tau>' \<rightarrow> \<tau>'\<down>\<close>
    proof (induct \<tau>; induct \<tau>'; rule "\<rightarrow>I")
      fix \<tau>\<^sub>1 \<tau>\<^sub>1' :: 'a and \<tau>\<^sub>2  \<tau>\<^sub>2' :: 'b
      AOT_assume \<open>\<guillemotleft>(\<tau>\<^sub>1, \<tau>\<^sub>2)\<guillemotright> = \<guillemotleft>(\<tau>\<^sub>1', \<tau>\<^sub>2')\<guillemotright>\<close>
      AOT_hence \<open>(\<tau>\<^sub>1 = \<tau>\<^sub>1') & (\<tau>\<^sub>2 = \<tau>\<^sub>2')\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" tuple_identity_1)
      AOT_hence \<open>\<tau>\<^sub>1'\<down>\<close> and \<open>\<tau>\<^sub>2'\<down>\<close> using "t=t-proper:2" "&E" "vdash-properties:10" by blast+
      AOT_thus \<open>\<guillemotleft>(\<tau>\<^sub>1', \<tau>\<^sub>2')\<guillemotright>\<down>\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" tuple_denotes)
    qed
  }
qed

(* TODO: this is the end of the "proof by types" and makes the results available on new theorems *)
AOT_register_type_constraints
  Term: \<open>_::AOT_Term_id\<close> \<open>_::AOT_Term_id\<close>
AOT_register_type_constraints
  Individual: \<open>\<kappa>\<close> \<open>_::{AOT_\<kappa>s, AOT_Term_id}\<close>
AOT_register_type_constraints
  Relation: \<open><_::{AOT_\<kappa>s, AOT_Term_id}>\<close>

AOT_theorem "id-rel-nec-equiv:1": \<open>\<Pi> = \<Pi>' \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>']x\<^sub>1...x\<^sub>n)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume assumption: \<open>\<Pi> = \<Pi>'\<close>
  AOT_hence \<open>\<Pi>\<down>\<close> and \<open>\<Pi>'\<down>\<close>
    using "t=t-proper:1" "t=t-proper:2" MP by blast+
  moreover AOT_have \<open>\<forall>F\<forall>G (F = G \<rightarrow> ((\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]x\<^sub>1...x\<^sub>n)) \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> [G]x\<^sub>1...x\<^sub>n)))\<close>
    apply (rule GEN)+ using "l-identity"[axiom_inst] by force
  ultimately AOT_have \<open>\<Pi> = \<Pi>' \<rightarrow> ((\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>]x\<^sub>1...x\<^sub>n)) \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>']x\<^sub>1...x\<^sub>n))\<close>
    using "\<forall>E"(1) by blast
  AOT_hence \<open>(\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>]x\<^sub>1...x\<^sub>n)) \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>']x\<^sub>1...x\<^sub>n)\<close>
    using assumption "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>]x\<^sub>1...x\<^sub>n)\<close>
    by (simp add: RN "oth-class-taut:3:a" "universal-cor")
  ultimately AOT_show \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>']x\<^sub>1...x\<^sub>n)\<close>
    using "\<rightarrow>E" by blast
qed

AOT_theorem "id-rel-nec-equiv:2": \<open>\<phi> = \<psi> \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume assumption: \<open>\<phi> = \<psi>\<close>
  AOT_hence \<open>\<phi>\<down>\<close> and \<open>\<psi>\<down>\<close>
    using "t=t-proper:1" "t=t-proper:2" MP by blast+
  moreover AOT_have \<open>\<forall>p\<forall>q (p = q \<rightarrow> ((\<box>(p \<equiv> p) \<rightarrow> \<box>(p \<equiv> q))))\<close>
    apply (rule GEN)+ using "l-identity"[axiom_inst] by force
  ultimately AOT_have \<open>\<phi> = \<psi> \<rightarrow> (\<box>(\<phi> \<equiv> \<phi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>))\<close>
    using "\<forall>E"(1) by blast
  AOT_hence \<open>\<box>(\<phi> \<equiv> \<phi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
    using assumption "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<box>(\<phi> \<equiv> \<phi>)\<close>
    by (simp add: RN "oth-class-taut:3:a" "universal-cor")
  ultimately AOT_show \<open>\<box>(\<phi> \<equiv> \<psi>)\<close>
    using "\<rightarrow>E" by blast
qed

AOT_theorem "rule=E": assumes \<open>\<phi>{\<tau>}\<close> and \<open>\<tau> = \<sigma>\<close> shows \<open>\<phi>{\<sigma>}\<close>
proof -
  AOT_have \<open>\<tau>\<down>\<close> and \<open>\<sigma>\<down>\<close> using assms(2) "t=t-proper:1" "t=t-proper:2" "\<rightarrow>E" by blast+
  moreover AOT_have \<open>\<forall>\<alpha>\<forall>\<beta>(\<alpha> = \<beta> \<rightarrow> (\<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>}))\<close>
    apply (rule GEN)+ using "l-identity"[axiom_inst] by blast
  ultimately AOT_have \<open>\<tau> = \<sigma> \<rightarrow> (\<phi>{\<tau>} \<rightarrow> \<phi>{\<sigma>})\<close>
    using "\<forall>E"(1) by blast
  AOT_thus \<open>\<phi>{\<sigma>}\<close> using assms "\<rightarrow>E" by blast
qed
lemmas "=E" = "rule=E"

AOT_theorem "propositions-lemma:1": \<open>[\<lambda> \<phi>] = \<phi>\<close>
proof -
  AOT_have \<open>\<phi>\<down>\<close> by (simp add: "log-prop-prop:2")
  moreover AOT_have \<open>\<forall>p [\<lambda> p] = p\<close> using "lambda-predicates:3[zero]"[axiom_inst] "\<forall>I" by fast
  ultimately AOT_show \<open>[\<lambda> \<phi>] = \<phi>\<close>
    using "\<forall>E" by blast
qed

AOT_theorem "propositions-lemma:2": \<open>[\<lambda> \<phi>] \<equiv> \<phi>\<close>
proof -
  AOT_have \<open>[\<lambda> \<phi>] \<equiv> [\<lambda> \<phi>]\<close> by (simp add: "oth-class-taut:3:a")
  AOT_thus \<open>[\<lambda> \<phi>] \<equiv> \<phi>\<close> using "propositions-lemma:1" "=E" by blast
qed

(* propositions-lemma:3 through propositions-lemma:5 do not apply *)

AOT_theorem "propositions-lemma:6": \<open>(\<phi> \<equiv> \<psi>) \<equiv> ([\<lambda> \<phi>] \<equiv> [\<lambda> \<psi>])\<close>
  by (metis "\<equiv>E"(1) "\<equiv>E"(5) "Associativity of \<equiv>" "propositions-lemma:2")

(* dr-alphabetic-rules does not apply *)

AOT_theorem "oa-exist:1": \<open>O!\<down>\<close>
proof -
  AOT_have \<open>[\<lambda>x \<diamond>[E!]x]\<down>\<close> by "cqt:2[lambda]"
  AOT_hence 1: \<open>O! = [\<lambda>x \<diamond>[E!]x]\<close> using "df-rules-terms[4]"[OF "oa:1", THEN "&E"(1)] "\<rightarrow>E" by blast
  AOT_show \<open>O!\<down>\<close> using "t=t-proper:1"[THEN "\<rightarrow>E", OF 1] by simp
qed

AOT_theorem "oa-exist:2": \<open>A!\<down>\<close>
proof -
  AOT_have \<open>[\<lambda>x \<not>\<diamond>[E!]x]\<down>\<close> by "cqt:2[lambda]"
  AOT_hence 1: \<open>A! = [\<lambda>x \<not>\<diamond>[E!]x]\<close> using "df-rules-terms[4]"[OF "oa:2", THEN "&E"(1)] "\<rightarrow>E" by blast
  AOT_show \<open>A!\<down>\<close> using "t=t-proper:1"[THEN "\<rightarrow>E", OF 1] by simp
qed

AOT_theorem "oa-exist:3": \<open>O!x \<or> A!x\<close>
proof(rule "raa-cor:1")
  AOT_assume \<open>\<not>(O!x \<or> A!x)\<close>
  AOT_hence A: \<open>\<not>O!x\<close> and B: \<open>\<not>A!x\<close>
    using "Disjunction Addition"(1) "modus-tollens:1" "\<or>I"(2) "raa-cor:5" by blast+
  AOT_have C: \<open>O! = [\<lambda>x \<diamond>[E!]x]\<close>
    by (rule "df-rules-terms[4]"[OF "oa:1", THEN "&E"(1), THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  AOT_have D: \<open>A! = [\<lambda>x \<not>\<diamond>[E!]x]\<close>
    by (rule "df-rules-terms[4]"[OF "oa:2", THEN "&E"(1), THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  AOT_have E: \<open>\<not>[\<lambda>x \<diamond>[E!]x]x\<close>
    using A C "=E" by fast
  AOT_have F: \<open>\<not>[\<lambda>x \<not>\<diamond>[E!]x]x\<close>
    using B D "=E" by fast
  AOT_have G: \<open>[\<lambda>x \<diamond>[E!]x]x \<equiv> \<diamond>[E!]x\<close>
    by (rule "lambda-predicates:2"[axiom_inst, THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  AOT_have H: \<open>[\<lambda>x \<not>\<diamond>[E!]x]x \<equiv> \<not>\<diamond>[E!]x\<close>
    by (rule "lambda-predicates:2"[axiom_inst, THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  AOT_show \<open>\<not>\<diamond>[E!]x & \<not>\<not>\<diamond>[E!]x\<close> using G E "\<equiv>E" H F "\<equiv>E" "&I" by metis
qed

AOT_theorem "p-identity-thm2:1": \<open>F = G \<equiv> \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
    using "identity:2" "df-rules-formulas[3]" "df-rules-formulas[4]" "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: "cqt:2[const_var]"[axiom_inst])
  ultimately AOT_show \<open>F = G \<equiv> \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
    using "\<equiv>S"(1) "&I" by blast
qed

AOT_theorem "p-identity-thm2:2[2]": \<open>F = G \<equiv> \<forall>y\<^sub>1([\<lambda>x [F]xy\<^sub>1] = [\<lambda>x [G]xy\<^sub>1] & [\<lambda>x [F]y\<^sub>1x] = [\<lambda>x [G]y\<^sub>1x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1([\<lambda>x [F]xy\<^sub>1] = [\<lambda>x [G]xy\<^sub>1] & [\<lambda>x [F]y\<^sub>1x] = [\<lambda>x [G]y\<^sub>1x])\<close>
    using "identity:3[2]" "df-rules-formulas[3]" "df-rules-formulas[4]" "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: "cqt:2[const_var]"[axiom_inst])
  ultimately show ?thesis
    using "\<equiv>S"(1) "&I" by blast
qed
    
AOT_theorem "p-identity-thm2:2[3]": \<open>F = G \<equiv> \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>x [F]xy\<^sub>1y\<^sub>2] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2] & [\<lambda>x [F]y\<^sub>1y\<^sub>2x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>x [F]xy\<^sub>1y\<^sub>2] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2] & [\<lambda>x [F]y\<^sub>1y\<^sub>2x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2x])\<close>
    using "identity:3[3]" "df-rules-formulas[3]" "df-rules-formulas[4]" "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: "cqt:2[const_var]"[axiom_inst])
  ultimately show ?thesis
    using "\<equiv>S"(1) "&I" by blast
qed

AOT_theorem "p-identity-thm2:2[4]": \<open>F = G \<equiv> \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>x [F]xy\<^sub>1y\<^sub>2y\<^sub>3] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2y\<^sub>3] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2xy\<^sub>3] = [\<lambda>x [G]y\<^sub>1y\<^sub>2xy\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2y\<^sub>3x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2y\<^sub>3x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>x [F]xy\<^sub>1y\<^sub>2y\<^sub>3] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2y\<^sub>3] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2xy\<^sub>3] = [\<lambda>x [G]y\<^sub>1y\<^sub>2xy\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2y\<^sub>3x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2y\<^sub>3x])\<close>
    using "identity:3[4]" "df-rules-formulas[3]" "df-rules-formulas[4]" "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: "cqt:2[const_var]"[axiom_inst])
  ultimately show ?thesis
    using "\<equiv>S"(1) "&I" by blast
qed

AOT_theorem "p-identity-thm2:2":
  \<open>F = G \<equiv> \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . \<guillemotleft>[F]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[G]\<tau>\<guillemotright>)\<guillemotright>\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . \<guillemotleft>[F]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[G]\<tau>\<guillemotright>)\<guillemotright>\<close>
    using "identity:3" "df-rules-formulas[3]" "df-rules-formulas[4]" "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: "cqt:2[const_var]"[axiom_inst])
  ultimately show ?thesis
    using "\<equiv>S"(1) "&I" by blast
qed

AOT_theorem "p-identity-thm2:3":
  \<open>p = q \<equiv> [\<lambda>x p] = [\<lambda>x q]\<close>
proof -
  AOT_have \<open>p = q \<equiv> p\<down> & q\<down> & [\<lambda>x p] = [\<lambda>x q]\<close>
    using "identity:4" "df-rules-formulas[3]" "df-rules-formulas[4]" "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>p\<down>\<close> and \<open>q\<down>\<close>
    by (auto simp: "cqt:2[const_var]"[axiom_inst])
  ultimately show ?thesis
    using "\<equiv>S"(1) "&I" by blast
qed

class AOT_Term_id_2 = AOT_Term_id + assumes "id-eq:1": \<open>[v \<Turnstile> \<alpha> = \<alpha>]\<close>

instance \<kappa> :: AOT_Term_id_2
proof
  AOT_modally_strict {
    fix x
    {
      AOT_assume \<open>O!x\<close>
      moreover AOT_have \<open>\<box>\<forall>F([F]x \<equiv> [F]x)\<close>
        using RN GEN "oth-class-taut:3:a" by fast
      ultimately AOT_have \<open>O!x & O!x & \<box>\<forall>F([F]x \<equiv> [F]x)\<close> using "&I" by simp
    }
    moreover {
      AOT_assume \<open>A!x\<close>
      moreover AOT_have \<open>\<box>\<forall>F(x[F] \<equiv> x[F])\<close>
        using RN GEN "oth-class-taut:3:a" by fast
      ultimately AOT_have \<open>A!x & A!x & \<box>\<forall>F(x[F] \<equiv> x[F])\<close> using "&I" by simp
    }
    ultimately AOT_have \<open>(O!x & O!x & \<box>\<forall>F([F]x \<equiv> [F]x)) \<or> (A!x & A!x & \<box>\<forall>F(x[F] \<equiv> x[F]))\<close>
      using "oa-exist:3" "\<or>I"(1) "\<or>I"(2) "\<or>E"(3) "raa-cor:1" by blast
    AOT_thus \<open>x = x\<close>
      using "identity:1"[THEN "df-rules-formulas[4]"] "\<rightarrow>E" by blast
  }
qed

instance rel :: ("{AOT_\<kappa>s,AOT_Term_id_2}") AOT_Term_id_2
proof
  AOT_modally_strict {
    fix F :: "<'a> AOT_var"
    AOT_have 0: \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n] = F\<close>
      by (simp add: "lambda-predicates:3"[axiom_inst])
    AOT_have \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n]\<down>\<close>
      by "cqt:2[lambda]"
    AOT_hence \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n] = [\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n]\<close>
      using "lambda-predicates:1"[axiom_inst] "\<rightarrow>E" by blast
    AOT_show \<open>F = F\<close> using "=E" 0 by force 
  }
qed

instance \<o> :: AOT_Term_id_2
proof
  AOT_modally_strict {
    fix p
    AOT_have 0: \<open>[\<lambda> p] = p\<close>
      by (simp add: "lambda-predicates:3[zero]"[axiom_inst])
    AOT_have \<open>[\<lambda> p]\<down>\<close>
      by (rule "cqt:2[lambda0]"[axiom_inst])
    AOT_hence \<open>[\<lambda> p] = [\<lambda> p]\<close>
      using "lambda-predicates:1[zero]"[axiom_inst] "\<rightarrow>E" by blast
    AOT_show \<open>p = p\<close> using "=E" 0 by force
  }
qed

instance prod :: (AOT_Term_id_2, AOT_Term_id_2) AOT_Term_id_2
proof
  AOT_modally_strict {
    fix \<alpha> :: \<open>('a\<times>'b) AOT_var\<close>
    AOT_show \<open>\<alpha> = \<alpha>\<close>
    proof (induct)
      AOT_show \<open>\<tau> = \<tau>\<close> if \<open>\<tau>\<down>\<close> for \<tau> :: \<open>'a\<times>'b\<close>
        using that
      proof (induct \<tau>)
        fix \<tau>\<^sub>1 :: 'a and \<tau>\<^sub>2 :: 'b
        AOT_assume \<open>\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>\<down>\<close>
        AOT_hence \<open>\<tau>\<^sub>1\<down>\<close> and \<open>\<tau>\<^sub>2\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE" "&E" tuple_denotes by blast+
        AOT_hence \<open>\<tau>\<^sub>1 = \<tau>\<^sub>1\<close> and \<open>\<tau>\<^sub>2 = \<tau>\<^sub>2\<close> using "id-eq:1"[unvarify \<alpha>] by blast+
        AOT_thus \<open>\<guillemotleft>(\<tau>\<^sub>1, \<tau>\<^sub>2)\<guillemotright> = \<guillemotleft>(\<tau>\<^sub>1, \<tau>\<^sub>2)\<guillemotright>\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" tuple_identity_1)
      qed
    qed
  }
qed

AOT_register_type_constraints
  Term: \<open>_::AOT_Term_id_2\<close> \<open>_::AOT_Term_id_2\<close>
AOT_register_type_constraints
  Individual: \<open>\<kappa>\<close> \<open>_::{AOT_\<kappa>s, AOT_Term_id_2}\<close>
AOT_register_type_constraints
  Relation: \<open><_::{AOT_\<kappa>s, AOT_Term_id_2}>\<close>

(* TODO: Interestingly, this doesn't depend on "id-eq:1" at all! *)
AOT_theorem "id-eq:2": \<open>\<alpha> = \<beta> \<rightarrow> \<beta> = \<alpha>\<close>
(*
  TODO: look at this proof generated using:
        including AOT_no_atp sledgehammer[isar_proofs = true]
proof -
  have "(\<exists>\<phi>. [v \<Turnstile> ~\<beta> = \<alpha> \<rightarrow> ~\<phi>] \<and> [v \<Turnstile> \<alpha> = \<beta> \<rightarrow> \<phi>]) \<or> (\<exists>\<phi>. \<not> [v \<Turnstile> \<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>}])"
    by meson
  then show ?thesis
    by (meson "contraposition:2" "Hypothetical Syllogism" "deduction-theorem" l_"identity:1" "useful-tautologies:1")
qed
*)
(*  by (meson "rule=E" "deduction-theorem") *)
proof (rule "\<rightarrow>I")
  AOT_assume \<open>\<alpha> = \<beta>\<close>
  moreover AOT_have \<open>\<beta> = \<beta>\<close> using calculation "=E"[of _ "\<lambda> \<tau> . \<guillemotleft>\<tau> = \<beta>\<guillemotright>" "AOT_term_of_var \<alpha>" "AOT_term_of_var \<beta>"] by blast
  moreover AOT_have \<open>\<alpha> = \<alpha> \<rightarrow> \<alpha> = \<alpha>\<close> using "if-p-then-p" by blast
  ultimately AOT_show \<open>\<beta> = \<alpha>\<close>
    using "\<rightarrow>E" "\<rightarrow>I" "=E"[of _ "\<lambda> \<tau> . \<guillemotleft>(\<tau> = \<tau>) \<rightarrow> (\<tau> = \<alpha>)\<guillemotright>" "AOT_term_of_var \<alpha>" "AOT_term_of_var \<beta>"] by blast
qed

AOT_theorem "id-eq:3": \<open>\<alpha> = \<beta> & \<beta> = \<gamma> \<rightarrow> \<alpha> = \<gamma>\<close>
  using "rule=E" "\<rightarrow>I" "&E" by blast

AOT_theorem "id-eq:4": \<open>\<alpha> = \<beta> \<equiv> \<forall>\<gamma> (\<alpha> = \<gamma> \<equiv> \<beta> = \<gamma>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<alpha> = \<beta>\<close>
  AOT_hence 1: \<open>\<beta> = \<alpha>\<close> using "id-eq:2" "\<rightarrow>E" by blast
  AOT_show \<open>\<forall>\<gamma> (\<alpha> = \<gamma> \<equiv> \<beta> = \<gamma>)\<close>
    by (rule GEN) (metis "\<equiv>I" "\<rightarrow>I" 0 "1" "rule=E")
next
  AOT_assume \<open>\<forall>\<gamma> (\<alpha> = \<gamma> \<equiv> \<beta> = \<gamma>)\<close>
  AOT_hence \<open>\<alpha> = \<alpha> \<equiv> \<beta> = \<alpha>\<close> using "\<forall>E"(2) by blast
  AOT_hence \<open>\<alpha> = \<alpha> \<rightarrow> \<beta> = \<alpha>\<close> using "\<equiv>E"(1) "\<rightarrow>I" by blast
  AOT_hence \<open>\<beta> = \<alpha>\<close> using "id-eq:1" "\<rightarrow>E" by blast
  AOT_thus \<open>\<alpha> = \<beta>\<close> using "id-eq:2" "\<rightarrow>E" by blast
qed

AOT_theorem "rule=I:1": assumes \<open>\<tau>\<down>\<close> shows \<open>\<tau> = \<tau>\<close>
proof -
  AOT_have \<open>\<forall>\<alpha> (\<alpha> = \<alpha>)\<close>
    by (rule GEN) (metis "id-eq:1")
  AOT_thus \<open>\<tau> = \<tau>\<close> using assms "\<forall>E" by blast
qed

AOT_theorem "rule=I:2[const_var]": "\<alpha> = \<alpha>"
  using "id-eq:1".

AOT_theorem "rule=I:2[lambda]": assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close> shows "[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]"
proof -
  AOT_have \<open>\<forall>\<alpha> (\<alpha> = \<alpha>)\<close>
    by (rule GEN) (metis "id-eq:1")
  moreover AOT_have \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close> using assms by (rule "cqt:2[lambda]"[axiom_inst])
  ultimately AOT_show \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<close> using assms "\<forall>E" by blast
qed

lemmas "=I" = "rule=I:1" "rule=I:2[const_var]" "rule=I:2[lambda]"

AOT_theorem "rule-id-def:1":
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close> and \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>\<close>
  shows \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
proof -
  AOT_have \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
    using "df-rules-terms[3]" assms(1) "&E" by blast
  AOT_thus \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
    using assms(2) "\<rightarrow>E" by blast
qed

AOT_theorem "rule-id-def:1[zero]":
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close> and \<open>\<sigma>\<down>\<close>
  shows \<open>\<tau> = \<sigma>\<close>
proof -
  AOT_have \<open>\<sigma>\<down> \<rightarrow> \<tau> = \<sigma>\<close>
    using "df-rules-terms[4]" assms(1) "&E" by blast
  AOT_thus \<open>\<tau> = \<sigma>\<close>
    using assms(2) "\<rightarrow>E" by blast
qed

AOT_theorem "rule-id-def:2:a":
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close> and \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>\<close> and \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
  shows \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
proof -
  AOT_have \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close> using "rule-id-def:1" assms(1,2) by blast
  AOT_thus \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close> using assms(3) "=E" by blast
qed

(* TODO: get rid of this, ideally *)
AOT_theorem "rule-id-def:2:a[2]":
  assumes \<open>\<tau>{\<guillemotleft>(\<alpha>\<^sub>1,\<alpha>\<^sub>2)\<guillemotright>} =\<^sub>d\<^sub>f \<sigma>{\<guillemotleft>(\<alpha>\<^sub>1,\<alpha>\<^sub>2)\<guillemotright>}\<close> and \<open>\<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<down>\<close> and \<open>\<phi>{\<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}}\<close>
  shows \<open>\<phi>{\<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}}\<close>
proof -
  AOT_have \<open>\<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>} = \<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<close>
  proof -
    AOT_have \<open>\<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<down> \<rightarrow> \<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>} = \<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<close>
      using assms by (simp add: AOT_sem_conj AOT_sem_imp AOT_sem_eq AOT_sem_not AOT_sem_denotes AOT_model_id_def) (* NOTE: semantics needed *)
    AOT_thus \<open>\<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>} = \<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<close>
      using assms(2) "\<rightarrow>E" by blast
  qed
  AOT_thus \<open>\<phi>{\<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}}\<close> using assms(3) "=E" by blast
qed

AOT_theorem "rule-id-def:2:a[zero]":
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close> and \<open>\<sigma>\<down>\<close> and \<open>\<phi>{\<tau>}\<close>
  shows \<open>\<phi>{\<sigma>}\<close>
proof -
  AOT_have \<open>\<tau> = \<sigma>\<close> using "rule-id-def:1[zero]" assms(1,2) by blast
  AOT_thus \<open>\<phi>{\<sigma>}\<close> using assms(3) "=E" by blast
qed

lemmas "=\<^sub>d\<^sub>fE" = "rule-id-def:2:a" "rule-id-def:2:a[zero]"

AOT_theorem "rule-id-def:2:b":
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close> and \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>\<close> and \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
  shows \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
proof -
  AOT_have \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close> using "rule-id-def:1" assms(1,2) by blast
  AOT_hence \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
    using "=E" "=I"(1) "t=t-proper:1" "\<rightarrow>E" by fast
  AOT_thus \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close> using assms(3) "=E" by blast
qed

(* TODO: get rid of this, ideally *)
AOT_theorem "rule-id-def:2:b[2]":
  assumes \<open>\<tau>{\<guillemotleft>(\<alpha>\<^sub>1,\<alpha>\<^sub>2)\<guillemotright>} =\<^sub>d\<^sub>f \<sigma>{\<guillemotleft>(\<alpha>\<^sub>1,\<alpha>\<^sub>2)\<guillemotright>}\<close> and \<open>\<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<down>\<close> and \<open>\<phi>{\<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}}\<close>
  shows \<open>\<phi>{\<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}}\<close>
proof -
  AOT_have \<open>\<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>} = \<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<close>
  proof -
    AOT_have \<open>\<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<down> \<rightarrow> \<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>} = \<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<close>
      using assms by (simp add: AOT_sem_conj AOT_sem_imp AOT_sem_eq AOT_sem_not AOT_sem_denotes AOT_model_id_def) (* NOTE: semantics needed *)
    AOT_thus \<open>\<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>} = \<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<close>
      using assms(2) "\<rightarrow>E" by blast
  qed
  AOT_hence \<open>\<sigma>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>} = \<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}\<close>
    using "=E" "=I"(1) "t=t-proper:1" "\<rightarrow>E" by fast
  AOT_thus \<open>\<phi>{\<tau>{\<guillemotleft>(\<tau>\<^sub>1,\<tau>\<^sub>2)\<guillemotright>}}\<close> using assms(3) "=E" by blast
qed

AOT_theorem "rule-id-def:2:b[zero]":
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close> and \<open>\<sigma>\<down>\<close> and \<open>\<phi>{\<sigma>}\<close>
  shows \<open>\<phi>{\<tau>}\<close>
proof -
  AOT_have \<open>\<tau> = \<sigma>\<close> using "rule-id-def:1[zero]" assms(1,2) by blast
  AOT_hence \<open>\<sigma> = \<tau>\<close>
    using "=E" "=I"(1) "t=t-proper:1" "\<rightarrow>E" by fast
  AOT_thus \<open>\<phi>{\<tau>}\<close> using assms(3) "=E" by blast
qed

lemmas "=\<^sub>d\<^sub>fI" = "rule-id-def:2:b" "rule-id-def:2:b[zero]"

AOT_theorem "free-thms:1": \<open>\<tau>\<down> \<equiv> \<exists>\<beta> (\<beta> = \<tau>)\<close>
  by (metis "\<exists>E" "rule=I:1" "t=t-proper:2" "\<rightarrow>I" "\<exists>I"(1) "\<equiv>I" "\<rightarrow>E")

AOT_theorem "free-thms:2": \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> (\<exists>\<beta> (\<beta> = \<tau>) \<rightarrow> \<phi>{\<tau>})\<close>
  by (metis "\<exists>E" "rule=E" "cqt:2[const_var]"[axiom_inst] "\<rightarrow>I" "\<forall>E"(1))

AOT_theorem "free-thms:3[const_var]": \<open>\<exists>\<beta> (\<beta> = \<alpha>)\<close>
  by (meson "\<exists>I"(2) "id-eq:1")

AOT_theorem "free-thms:3[lambda]": assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close> shows \<open>\<exists>\<beta> (\<beta> = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}])\<close>
  by (meson "=I"(3) assms "cqt:2[lambda]"[axiom_inst] "existential:1")

AOT_theorem "free-thms:4[rel]": \<open>([\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<or> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I:1" "&E"(1) "\<or>E"(1) "cqt:5:a"[axiom_inst] "cqt:5:b"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))

(* TODO: this is a rather weird way to formulate this and we don't have tuple-existential-elimination
         or tuple-equality-elimination in the theory... Splitting them is also a bit unfortunate, though.*)
AOT_theorem "free-thms:4[vars]": \<open>([\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<or> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]) \<rightarrow> \<exists>\<beta>\<^sub>1...\<exists>\<beta>\<^sub>n (\<beta>\<^sub>1...\<beta>\<^sub>n = \<kappa>\<^sub>1...\<kappa>\<^sub>n)\<close>
  by (metis "rule=I:1" "&E"(2) "\<or>E"(1) "cqt:5:a"[axiom_inst] "cqt:5:b"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))

AOT_theorem "free-thms:4[1,rel]": \<open>([\<Pi>]\<kappa> \<or> \<kappa>[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I:1" "&E"(1) "\<or>E"(1) "cqt:5:a"[axiom_inst] "cqt:5:b"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[1,1]": \<open>([\<Pi>]\<kappa> \<or> \<kappa>[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>)\<close>
  by (metis "rule=I:1" "&E"(2) "\<or>E"(1) "cqt:5:a"[axiom_inst] "cqt:5:b"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))

AOT_theorem "free-thms:4[2,rel]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I:1" "&E"(1) "\<or>E"(1) "cqt:5:a[2]"[axiom_inst] "cqt:5:b[2]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[2,1]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>1)\<close>
  by (metis "rule=I:1" "&E" "\<or>E"(1) "cqt:5:a[2]"[axiom_inst] "cqt:5:b[2]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[2,2]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>2)\<close>
  by (metis "rule=I:1" "&E"(2) "\<or>E"(1) "cqt:5:a[2]"[axiom_inst] "cqt:5:b[2]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[3,rel]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I:1" "&E"(1) "\<or>E"(1) "cqt:5:a[3]"[axiom_inst] "cqt:5:b[3]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[3,1]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>1)\<close>
  by (metis "rule=I:1" "&E" "\<or>E"(1) "cqt:5:a[3]"[axiom_inst] "cqt:5:b[3]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[3,2]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>2)\<close>
  by (metis "rule=I:1" "&E" "\<or>E"(1) "cqt:5:a[3]"[axiom_inst] "cqt:5:b[3]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[3,3]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>3)\<close>
  by (metis "rule=I:1" "&E"(2) "\<or>E"(1) "cqt:5:a[3]"[axiom_inst] "cqt:5:b[3]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[4,rel]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I:1" "&E"(1) "\<or>E"(1) "cqt:5:a[4]"[axiom_inst] "cqt:5:b[4]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[4,1]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>1)\<close>
  by (metis "rule=I:1" "&E" "\<or>E"(1) "cqt:5:a[4]"[axiom_inst] "cqt:5:b[4]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[4,2]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>2)\<close>
  by (metis "rule=I:1" "&E" "\<or>E"(1) "cqt:5:a[4]"[axiom_inst] "cqt:5:b[4]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[4,3]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>3)\<close>
  by (metis "rule=I:1" "&E" "\<or>E"(1) "cqt:5:a[4]"[axiom_inst] "cqt:5:b[4]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem "free-thms:4[4,4]": \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>4)\<close>
  by (metis "rule=I:1" "&E"(2) "\<or>E"(1) "cqt:5:a[4]"[axiom_inst] "cqt:5:b[4]"[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))

AOT_theorem "ex:1:a": \<open>\<forall>\<alpha> \<alpha>\<down>\<close>
  by (rule GEN) (fact "cqt:2[const_var]"[axiom_inst])
AOT_theorem "ex:1:b": \<open>\<forall>\<alpha>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule GEN) (fact "free-thms:3[const_var]")

AOT_theorem "ex:2:a": \<open>\<box>\<alpha>\<down>\<close>
  by (rule RN) (fact "cqt:2[const_var]"[axiom_inst])
AOT_theorem "ex:2:b": \<open>\<box>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule RN) (fact "free-thms:3[const_var]")

AOT_theorem "ex:3:a": \<open>\<box>\<forall>\<alpha> \<alpha>\<down>\<close>
  by (rule RN) (fact "ex:1:a")
AOT_theorem "ex:3:b": \<open>\<box>\<forall>\<alpha>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule RN) (fact "ex:1:b")

AOT_theorem "ex:4:a": \<open>\<forall>\<alpha> \<box>\<alpha>\<down>\<close>
  by (rule GEN; rule RN) (fact "cqt:2[const_var]"[axiom_inst])
AOT_theorem "ex:4:b": \<open>\<forall>\<alpha>\<box>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule GEN; rule RN) (fact "free-thms:3[const_var]")

AOT_theorem "ex:5:a": \<open>\<box>\<forall>\<alpha> \<box>\<alpha>\<down>\<close>
  by (rule RN) (simp add: "ex:4:a")
AOT_theorem "ex:5:b": \<open>\<box>\<forall>\<alpha>\<box>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule RN) (simp add: "ex:4:b")

AOT_theorem "all-self=:1": \<open>\<box>\<forall>\<alpha>(\<alpha> = \<alpha>)\<close>
  by (rule RN; rule GEN) (fact "id-eq:1")
AOT_theorem "all-self=:2": \<open>\<forall>\<alpha>\<box>(\<alpha> = \<alpha>)\<close>
  by (rule GEN; rule RN) (fact "id-eq:1")

AOT_theorem "id-nec:1": \<open>\<alpha> = \<beta> \<rightarrow> \<box>(\<alpha> = \<beta>)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<alpha> = \<beta>\<close>
  moreover AOT_have \<open>\<box>(\<alpha> = \<alpha>)\<close>
    by (rule RN) (fact "id-eq:1")
  ultimately AOT_show \<open>\<box>(\<alpha> = \<beta>)\<close> using "=E" by fast
qed

AOT_theorem "id-nec:2": \<open>\<tau> = \<sigma> \<rightarrow> \<box>(\<tau> = \<sigma>)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume asm: \<open>\<tau> = \<sigma>\<close>
  moreover AOT_have \<open>\<tau>\<down>\<close>
    using calculation "t=t-proper:1" "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<box>(\<tau> = \<tau>)\<close>
    using calculation "all-self=:2" "\<forall>E"(1) by blast
  ultimately AOT_show \<open>\<box>(\<tau> = \<sigma>)\<close> using "=E" by fast
qed

AOT_theorem "term-out:1": \<open>\<phi>{\<alpha>} \<equiv> \<exists>\<beta> (\<beta> = \<alpha> & \<phi>{\<beta>})\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume asm: \<open>\<phi>{\<alpha>}\<close>
  AOT_show \<open>\<exists>\<beta> (\<beta> = \<alpha> & \<phi>{\<beta>})\<close>
    by (rule "\<exists>I"(2)[where \<beta>=\<alpha>]; rule "&I")
       (auto simp: "id-eq:1" asm)
next
  AOT_assume 0: \<open>\<exists>\<beta> (\<beta> = \<alpha> & \<phi>{\<beta>})\<close>
  (* TODO: have another look at this instantiation. Ideally AOT_obtain would resolve directly to the existential
           statement as proof obligation *)
  AOT_obtain \<beta> where \<open>\<beta> = \<alpha> & \<phi>{\<beta>}\<close> using "instantiation"[rotated, OF 0] by blast
  AOT_thus \<open>\<phi>{\<alpha>}\<close> using "&E" "=E" by blast
qed

AOT_theorem "term-out:2": \<open>\<tau>\<down> \<rightarrow> (\<phi>{\<tau>} \<equiv> \<exists>\<alpha>(\<alpha> = \<tau> & \<phi>{\<alpha>}))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<tau>\<down>\<close>
  moreover AOT_have \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<exists>\<beta> (\<beta> = \<alpha> & \<phi>{\<beta>}))\<close>
    by (rule GEN) (fact "term-out:1")
  ultimately AOT_show \<open>\<phi>{\<tau>} \<equiv> \<exists>\<alpha>(\<alpha> = \<tau> & \<phi>{\<alpha>})\<close>
    using "\<forall>E" by blast
qed

(* TODO: example of an apply-style proof. Keep or reformulate? *)
AOT_theorem "term-out:3": \<open>(\<phi>{\<alpha>} & \<forall>\<beta>(\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)) \<equiv> \<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I")
   apply (frule "&E"(1)) apply (drule "&E"(2))
   apply (rule GEN; rule "\<equiv>I"; rule "\<rightarrow>I")
  using "rule-ui:2[const_var]" "vdash-properties:5" apply blast
  apply (meson "rule=E" "id-eq:1")
  apply (rule "&I")
  using "id-eq:1" "\<equiv>E"(2) "rule-ui:3" apply blast
  apply (rule GEN; rule "\<rightarrow>I")
  using "\<equiv>E"(1) "rule-ui:2[const_var]" by blast

AOT_theorem "term-out:4": \<open>(\<phi>{\<beta>} & \<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<alpha> = \<beta>)) \<equiv> \<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<alpha> = \<beta>)\<close>
  using "term-out:3" . (* TODO: same as above - another instance of the generalized alphabetic variant rule... *)

(* TODO: would of course be nice to define it without the syntax magic *)
AOT_define AOT_exists_unique :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close>
  "uniqueness:1": \<open>\<guillemotleft>AOT_exists_unique \<phi>\<guillemotright> \<equiv>\<^sub>d\<^sub>f \<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close>
syntax "_AOT_exists_unique" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> ("\<exists>!_ _" [1,40])
AOT_syntax_print_translations
  "_AOT_exists_unique \<tau> \<phi>" <= "CONST AOT_exists_unique (_abs \<tau> \<phi>)"
syntax
   "_AOT_exists_unique_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<exists>!_...\<exists>!_ _\<close> [1,40])
parse_ast_translation\<open>[(\<^syntax_const>\<open>_AOT_exists_unique_ellipse\<close>, fn ctx => fn [a,b,c] =>
  Ast.mk_appl (Ast.Constant "AOT_exists_unique") [parseEllipseList "_AOT_vars" ctx [a,b],c]),
(\<^syntax_const>\<open>_AOT_exists_unique\<close>,AOT_restricted_binder \<^const_name>\<open>AOT_exists_unique\<close> \<^const_syntax>\<open>AOT_conj\<close>)]\<close>
print_translation\<open>AOT_syntax_print_translations
  [Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_exists_unique\<close> \<^syntax_const>\<open>_AOT_exists_unique\<close>,
  AOT_binder_trans @{theory} @{binding "AOT_exists_unique_binder"} \<^syntax_const>\<open>_AOT_exists_unique\<close>]
\<close>


context AOT_meta_syntax
begin
notation AOT_exists_unique (binder "\<^bold>\<exists>\<^bold>!" 20)
end
context AOT_no_meta_syntax
begin
no_notation AOT_exists_unique (binder "\<^bold>\<exists>\<^bold>!" 20)
end

AOT_theorem "uniqueness:2": \<open>\<exists>!\<alpha> \<phi>{\<alpha>} \<equiv> \<exists>\<alpha>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>\<exists>!\<alpha> \<phi>{\<alpha>}\<close>
    AOT_hence \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close>
      using "uniqueness:1" "\<equiv>\<^sub>d\<^sub>fE" by blast
    then AOT_obtain \<alpha> where \<open>\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)\<close> using "instantiation"[rotated] by blast
    AOT_hence \<open>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close> using "term-out:3" "\<equiv>E" by blast
    AOT_thus \<open>\<exists>\<alpha>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
      using "\<exists>I" by fast
next
    AOT_assume \<open>\<exists>\<alpha>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    then AOT_obtain \<alpha> where \<open>\<forall>\<beta> (\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close> using "instantiation"[rotated] by blast
    AOT_hence \<open>\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)\<close> using "term-out:3" "\<equiv>E" by blast
    AOT_hence \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close>
      using "\<exists>I" by fast
    AOT_thus \<open>\<exists>!\<alpha> \<phi>{\<alpha>}\<close>
      using "uniqueness:1" "\<equiv>\<^sub>d\<^sub>fI" by blast
qed

AOT_theorem "uni-most": \<open>\<exists>!\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<beta>\<forall>\<gamma>((\<phi>{\<beta>} & \<phi>{\<gamma>}) \<rightarrow> \<beta> = \<gamma>)\<close>
proof(rule "\<rightarrow>I"; rule GEN; rule GEN; rule "\<rightarrow>I")
  fix \<beta> \<gamma>
  AOT_assume \<open>\<exists>!\<alpha> \<phi>{\<alpha>}\<close>
  AOT_hence \<open>\<exists>\<alpha>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    using "uniqueness:2" "\<equiv>E" by blast
  then AOT_obtain \<alpha> where \<open>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    using "instantiation"[rotated] by blast
  moreover AOT_assume \<open>\<phi>{\<beta>} & \<phi>{\<gamma>}\<close>
  ultimately AOT_have \<open>\<beta> = \<alpha>\<close> and \<open>\<gamma> = \<alpha>\<close>
    using "\<forall>E"(2) "&E" "\<equiv>E"(1,2) by blast+
  AOT_thus \<open>\<beta> = \<gamma>\<close>
    by (metis "rule=E" "id-eq:2" "\<rightarrow>E")
qed

AOT_theorem "nec-exist-!": \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>}) \<rightarrow> (\<exists>!\<alpha> \<phi>{\<alpha>} \<rightarrow> \<exists>!\<alpha> \<box>\<phi>{\<alpha>})\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume a: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>})\<close>
  AOT_assume \<open>\<exists>!\<alpha> \<phi>{\<alpha>}\<close>
  AOT_hence \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close> using "uniqueness:1" "\<equiv>\<^sub>d\<^sub>fE" by blast
  then AOT_obtain \<alpha> where \<xi>: \<open>\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)\<close> using "instantiation"[rotated] by blast
  AOT_have \<open>\<box>\<phi>{\<alpha>}\<close>
    using \<xi> a "&E" "\<forall>E" "\<rightarrow>E" by fast
  moreover AOT_have \<open>\<forall>\<beta> (\<box>\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)\<close>
    apply (rule GEN; rule "\<rightarrow>I")
    using \<xi>[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
  ultimately AOT_have \<open>(\<box>\<phi>{\<alpha>} & \<forall>\<beta> (\<box>\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close>
    using "&I" by blast
  AOT_thus \<open>\<exists>!\<alpha> \<box>\<phi>{\<alpha>}\<close>
    using "uniqueness:1" "\<equiv>\<^sub>d\<^sub>fI" "\<exists>I" by fast
qed

AOT_theorem "act-cond": \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>\<psi>)\<close>
  using "\<rightarrow>I" "\<equiv>E"(1) "logic-actual-nec:2"[axiom_inst] by blast

AOT_theorem "nec-imp-act": \<open>\<box>\<phi> \<rightarrow> \<^bold>\<A>\<phi>\<close>
  by (metis "act-cond" "contraposition:1[2]" "\<equiv>E"(4) "qml:2"[THEN act_closure, axiom_inst] "qml-act:2"[axiom_inst] RAA(1) "\<rightarrow>E" "\<rightarrow>I")

AOT_theorem "act-conj-act:1": \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<rightarrow> \<phi>)\<close>
  using "\<rightarrow>I" "\<equiv>E"(2) "logic-actual-nec:2"[axiom_inst] "logic-actual-nec:4"[axiom_inst] by blast

AOT_theorem "act-conj-act:2": \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<^bold>\<A>\<phi>)\<close>
  by (metis "\<rightarrow>I" "\<equiv>E"(2, 4) "logic-actual-nec:2"[axiom_inst] "logic-actual-nec:4"[axiom_inst] RAA(1))

AOT_theorem "act-conj-act:3": \<open>(\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>) \<rightarrow> \<^bold>\<A>(\<phi> & \<psi>)\<close>
proof -
  AOT_have \<open>\<box>(\<phi> \<rightarrow> (\<psi> \<rightarrow> (\<phi> & \<psi>)))\<close>
    by (rule RN) (fact Adjunction)
  AOT_hence \<open>\<^bold>\<A>(\<phi> \<rightarrow> (\<psi> \<rightarrow> (\<phi> & \<psi>)))\<close>
    using "nec-imp-act" "\<rightarrow>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>(\<psi> \<rightarrow> (\<phi> & \<psi>))\<close>
    using "act-cond" "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<^bold>\<A>(\<psi> \<rightarrow> (\<phi> & \<psi>)) \<rightarrow> (\<^bold>\<A>\<psi> \<rightarrow> \<^bold>\<A>(\<phi> & \<psi>))\<close>
    by (fact "act-cond")
  ultimately AOT_have \<open>\<^bold>\<A>\<phi> \<rightarrow> (\<^bold>\<A>\<psi> \<rightarrow> \<^bold>\<A>(\<phi> & \<psi>))\<close>
    using "\<rightarrow>I" "\<rightarrow>E" by metis
  AOT_thus \<open>(\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>) \<rightarrow> \<^bold>\<A>(\<phi> & \<psi>)\<close>
    by (metis Importation "\<rightarrow>E")
qed

AOT_theorem "act-conj-act:4": \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close>
proof -
  AOT_have \<open>(\<^bold>\<A>(\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & \<^bold>\<A>(\<phi> \<rightarrow> \<^bold>\<A>\<phi>)) \<rightarrow> \<^bold>\<A>((\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & (\<phi> \<rightarrow> \<^bold>\<A>\<phi>))\<close>
    by (fact "act-conj-act:3")
  moreover AOT_have \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & \<^bold>\<A>(\<phi> \<rightarrow> \<^bold>\<A>\<phi>)\<close>
    using "&I" "act-conj-act:1" "act-conj-act:2" by simp
  ultimately AOT_have \<zeta>: \<open>\<^bold>\<A>((\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & (\<phi> \<rightarrow> \<^bold>\<A>\<phi>))\<close>
    using "\<rightarrow>E" by blast
  AOT_have \<open>\<^bold>\<A>(((\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & (\<phi> \<rightarrow> \<^bold>\<A>\<phi>)) \<rightarrow> (\<^bold>\<A>\<phi> \<equiv> \<phi>))\<close>
    using AOT_equiv[THEN "df-rules-formulas[2]", THEN act_closure, axiom_inst] by blast
  AOT_hence \<open>\<^bold>\<A>((\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & (\<phi> \<rightarrow> \<^bold>\<A>\<phi>)) \<rightarrow> \<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close>
    using "act-cond" "\<rightarrow>E" by blast
  AOT_thus \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close> using \<zeta> "\<rightarrow>E" by blast
qed

(* TODO: consider introducing AOT_inductive *)
inductive arbitrary_actualization for \<phi> where
  \<open>arbitrary_actualization \<phi> \<guillemotleft>\<^bold>\<A>\<phi>\<guillemotright>\<close>
| \<open>arbitrary_actualization \<phi> \<guillemotleft>\<^bold>\<A>\<psi>\<guillemotright>\<close> if \<open>arbitrary_actualization \<phi> \<psi>\<close>
declare arbitrary_actualization.cases[AOT] arbitrary_actualization.induct[AOT]
        arbitrary_actualization.simps[AOT] arbitrary_actualization.intros[AOT]
syntax arbitrary_actualization :: \<open>\<phi>' \<Rightarrow> \<phi>' \<Rightarrow> AOT_prop\<close> ("ARBITRARY'_ACTUALIZATION'(_,_')")

notepad
begin
  AOT_modally_strict {
    fix \<phi>
    AOT_have \<open>ARBITRARY_ACTUALIZATION(\<^bold>\<A>\<phi> \<equiv> \<phi>, \<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>))\<close>
      using AOT_PLM.arbitrary_actualization.intros by metis
    AOT_have \<open>ARBITRARY_ACTUALIZATION(\<^bold>\<A>\<phi> \<equiv> \<phi>, \<^bold>\<A>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>))\<close>
      using AOT_PLM.arbitrary_actualization.intros by metis
    AOT_have \<open>ARBITRARY_ACTUALIZATION(\<^bold>\<A>\<phi> \<equiv> \<phi>, \<^bold>\<A>\<^bold>\<A>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>))\<close>
      using AOT_PLM.arbitrary_actualization.intros by metis
  }
end


AOT_theorem "closure-act:1": assumes \<open>ARBITRARY_ACTUALIZATION(\<^bold>\<A>\<phi> \<equiv> \<phi>, \<psi>)\<close> shows \<open>\<psi>\<close>
using assms proof(induct)
  case 1
  AOT_show \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close>
    by (simp add: "act-conj-act:4")
next
  case (2 \<psi>)
  AOT_thus \<open>\<^bold>\<A>\<psi>\<close>
    by (metis arbitrary_actualization.simps "\<equiv>E"(1) "logic-actual-nec:4"[axiom_inst])
qed

AOT_theorem "closure-act:2": \<open>\<forall>\<alpha> \<^bold>\<A>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close>
  by (simp add: "act-conj-act:4" "\<forall>I")

AOT_theorem "closure-act:3": \<open>\<^bold>\<A>\<forall>\<alpha> \<^bold>\<A>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close>
  by (metis (no_types, lifting) "act-conj-act:4" "\<equiv>E"(1,2) "logic-actual-nec:3"[axiom_inst] "logic-actual-nec:4"[axiom_inst] "\<forall>I")

AOT_theorem "closure-act:4": \<open>\<^bold>\<A>\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<^bold>\<A>(\<^bold>\<A>\<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} \<equiv> \<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n})\<close>
  using "closure-act:3" .

(* TODO: examine these proofs *)
AOT_theorem "RA[1]": assumes \<open>\<^bold>\<turnstile> \<phi>\<close> shows \<open>\<^bold>\<turnstile> \<^bold>\<A>\<phi>\<close>
  (* This proof is the one rejected in remark (136) (meta-rule) *)
  using "\<not>\<not>E" assms "\<equiv>E"(3) "logic-actual"[act_axiom_inst] "logic-actual-nec:1"[axiom_inst] "modus-tollens:2" by blast
AOT_theorem "RA[2]": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<^bold>\<A>\<phi>\<close>
  (* This is actually \<Gamma> \<turnstile>\<^sub>\<box> \<phi> \<Longrightarrow> \<box>\<Gamma> \<turnstile>\<^sub>\<box> \<A>\<phi>*)
  using RN assms "nec-imp-act" "vdash-properties:5" by blast
AOT_theorem "RA[3]": assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<^bold>\<A>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<phi>\<close>
  using assms by (meson AOT_sem_act imageI)
  (* This is not exactly right either. *)

AOT_act_theorem "ANeg:1": \<open>\<not>\<^bold>\<A>\<phi> \<equiv> \<not>\<phi>\<close>
  by (simp add: "RA[1]" "contraposition:1[1]" "deduction-theorem" "\<equiv>I" "logic-actual"[act_axiom_inst])

AOT_act_theorem "ANeg:2": \<open>\<not>\<^bold>\<A>\<not>\<phi> \<equiv> \<phi>\<close>
  using "ANeg:1" "\<equiv>I" "\<equiv>E"(5) "useful-tautologies:1" "useful-tautologies:2" by blast

AOT_theorem "Act-Basic:1": \<open>\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<not>\<phi>\<close>
  by (meson "\<or>I"(1,2) "\<equiv>E"(2) "logic-actual-nec:1"[axiom_inst] "raa-cor:1")

AOT_theorem "Act-Basic:2": \<open>\<^bold>\<A>(\<phi> & \<psi>) \<equiv> (\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>(\<phi> & \<psi>)\<close>
  moreover AOT_have \<open>\<^bold>\<A>((\<phi> & \<psi>) \<rightarrow> \<phi>)\<close>
    by (simp add: "RA[2]" "Conjunction Simplification"(1))
  moreover AOT_have \<open>\<^bold>\<A>((\<phi> & \<psi>) \<rightarrow> \<psi>)\<close>
    by (simp add: "RA[2]" "Conjunction Simplification"(2))
  ultimately AOT_show \<open>\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>\<close>
    using "act-cond"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I" by metis
next
  AOT_assume \<open>\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>\<close>
  AOT_thus \<open>\<^bold>\<A>(\<phi> & \<psi>)\<close>
    using "act-conj-act:3" "vdash-properties:6" by blast
qed

AOT_theorem "Act-Basic:3": \<open>\<^bold>\<A>(\<phi> \<equiv> \<psi>) \<equiv> (\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>))\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>(\<phi> \<equiv> \<psi>)\<close>
  moreover AOT_have \<open>\<^bold>\<A>((\<phi> \<equiv> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>))\<close>
    by (simp add: "RA[2]" "deduction-theorem" "\<equiv>E"(1))
  moreover AOT_have \<open>\<^bold>\<A>((\<phi> \<equiv> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>))\<close>
    by (simp add: "RA[2]" "deduction-theorem" "\<equiv>E"(2))
  ultimately AOT_show \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)\<close>
    using "act-cond"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I" by metis
next
  AOT_assume \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)\<close>
  AOT_hence \<open>\<^bold>\<A>((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>))\<close>
    by (metis "act-conj-act:3" "vdash-properties:10")
  moreover AOT_have \<open>\<^bold>\<A>(((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)) \<rightarrow> (\<phi> \<equiv> \<psi>))\<close>
    by (simp add: AOT_equiv "RA[2]" "df-rules-formulas[2]" "vdash-properties:1[2]")
  ultimately AOT_show \<open>\<^bold>\<A>(\<phi> \<equiv> \<psi>)\<close>
    using "act-cond"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by metis
qed

AOT_theorem "Act-Basic:4": \<open>(\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)) \<equiv> (\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)\<close>
  AOT_show \<open>\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<psi>\<close>
    using 0 "&E" "act-cond"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "\<equiv>I" "\<rightarrow>I" by metis
next
  AOT_assume \<open>\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<psi>\<close>
  AOT_thus \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)\<close>
    by (metis "\<rightarrow>I" "logic-actual-nec:2"[axiom_inst] "\<equiv>E"(1,2) "&I")
qed

AOT_theorem "Act-Basic:5": \<open>\<^bold>\<A>(\<phi> \<equiv> \<psi>) \<equiv> (\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<psi>)\<close>
  using "Act-Basic:3" "Act-Basic:4" "\<equiv>E"(5) by blast

AOT_theorem "Act-Basic:6": \<open>\<^bold>\<A>\<phi> \<equiv> \<box>\<^bold>\<A>\<phi>\<close>
  by (simp add: "\<equiv>I" "qml:2"[axiom_inst] "qml-act:1"[axiom_inst])

AOT_theorem "Act-Basic:7": \<open>\<^bold>\<A>\<box>\<phi> \<rightarrow> \<box>\<^bold>\<A>\<phi>\<close>
  by (metis "Act-Basic:6" "\<rightarrow>I" "\<rightarrow>E" "\<equiv>E"(1,2) "nec-imp-act" "qml-act:2"[axiom_inst])

AOT_theorem "Act-Basic:8": \<open>\<box>\<phi> \<rightarrow> \<box>\<^bold>\<A>\<phi>\<close>
  using "Hypothetical Syllogism" "nec-imp-act" "qml-act:1"[axiom_inst] by blast

AOT_theorem "Act-Basic:9": \<open>\<^bold>\<A>(\<phi> \<or> \<psi>) \<equiv> (\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>(\<phi> \<or> \<psi>)\<close>
  AOT_thus \<open>\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<psi>\<close>
  proof (rule "raa-cor:3")
    AOT_assume \<open>\<not>(\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<psi>)\<close>
    AOT_hence \<open>\<not>\<^bold>\<A>\<phi> & \<not>\<^bold>\<A>\<psi>\<close>
      by (metis "\<equiv>E"(1) "oth-class-taut:5:d")
    AOT_hence \<open>\<^bold>\<A>\<not>\<phi> & \<^bold>\<A>\<not>\<psi>\<close>
      using "logic-actual-nec:1"[axiom_inst, THEN "\<equiv>E"(2)] "&E" "&I" by metis
    AOT_hence \<open>\<^bold>\<A>(\<not>\<phi> & \<not>\<psi>)\<close>
      using "\<equiv>E" "Act-Basic:2" by metis
    moreover AOT_have \<open>\<^bold>\<A>((\<not>\<phi> & \<not>\<psi>) \<equiv> \<not>(\<phi> \<or> \<psi>))\<close>
      using "RA[2]" "\<equiv>E"(6) "oth-class-taut:3:a" "oth-class-taut:5:d" by blast
    moreover AOT_have \<open>\<^bold>\<A>(\<not>\<phi> & \<not>\<psi>) \<equiv> \<^bold>\<A>(\<not>(\<phi> \<or> \<psi>))\<close>
      using calculation(2) by (metis "Act-Basic:5" "\<equiv>E"(1))
    ultimately AOT_have \<open>\<^bold>\<A>(\<not>(\<phi> \<or> \<psi>))\<close> using "\<equiv>E" by blast
    AOT_thus \<open>\<not>\<^bold>\<A>(\<phi> \<or> \<psi>)\<close>
      using "logic-actual-nec:1"[axiom_inst, THEN "\<equiv>E"(1)] by auto
  qed
next
  AOT_assume \<open>\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<psi>\<close>
  AOT_thus \<open>\<^bold>\<A>(\<phi> \<or> \<psi>)\<close>
    by (meson "RA[2]" "act-cond" "\<or>I"(1) "\<or>E"(1) "Disjunction Addition"(1) "Disjunction Addition"(2))
qed

AOT_theorem "Act-Basic:10": \<open>\<^bold>\<A>\<exists>\<alpha> \<phi>{\<alpha>} \<equiv> \<exists>\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close>
proof -
  AOT_have \<theta>: \<open>\<not>\<^bold>\<A>\<forall>\<alpha> \<not>\<phi>{\<alpha>} \<equiv> \<not>\<forall>\<alpha> \<^bold>\<A>\<not>\<phi>{\<alpha>}\<close>
    by (rule "oth-class-taut:4:b"[THEN "\<equiv>E"(1)])
       (metis "logic-actual-nec:3"[axiom_inst])
  AOT_have \<xi>: \<open>\<not>\<forall>\<alpha> \<^bold>\<A>\<not>\<phi>{\<alpha>} \<equiv> \<not>\<forall>\<alpha> \<not>\<^bold>\<A>\<phi>{\<alpha>}\<close>
    by (rule "oth-class-taut:4:b"[THEN "\<equiv>E"(1)])
       (rule "logic-actual-nec:1"[THEN universal_closure, axiom_inst, THEN "cqt-basic:3"[THEN "\<rightarrow>E"]])
  AOT_have \<open>\<^bold>\<A>(\<exists>\<alpha> \<phi>{\<alpha>}) \<equiv> \<^bold>\<A>(\<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>})\<close>
    using AOT_exists[THEN "df-rules-formulas[1]", THEN act_closure, axiom_inst]
          AOT_exists[THEN "df-rules-formulas[2]", THEN act_closure, axiom_inst]
    "Act-Basic:4"[THEN "\<equiv>E"(1)] "&I" "Act-Basic:5"[THEN "\<equiv>E"(2)] by metis
  also AOT_have \<open>\<dots> \<equiv> \<not>\<^bold>\<A>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
    by (simp add: "logic-actual-nec:1" "vdash-properties:1[2]")
  also AOT_have \<open>\<dots> \<equiv> \<not>\<forall>\<alpha> \<^bold>\<A> \<not>\<phi>{\<alpha>}\<close> using \<theta> by blast
  also AOT_have \<open>\<dots> \<equiv> \<not>\<forall>\<alpha> \<not>\<^bold>\<A> \<phi>{\<alpha>}\<close> using \<xi> by blast
  also AOT_have \<open>\<dots> \<equiv> \<exists>\<alpha> \<^bold>\<A> \<phi>{\<alpha>}\<close>
    using AOT_exists[THEN "\<equiv>Df"] by (metis "\<equiv>E"(6) "oth-class-taut:3:a")
  finally AOT_show \<open>\<^bold>\<A>\<exists>\<alpha> \<phi>{\<alpha>} \<equiv> \<exists>\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close> .
qed


AOT_theorem "Act-Basic:11": \<open>\<^bold>\<A>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) \<equiv> \<forall>\<alpha>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>})\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  AOT_hence \<open>\<forall>\<alpha>\<^bold>\<A>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
    using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<^bold>\<A>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> for \<alpha> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>}\<close> for \<alpha> by (metis "Act-Basic:5" "\<equiv>E"(1))
  AOT_thus \<open>\<forall>\<alpha>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>})\<close> by (rule "\<forall>I")
next
  AOT_assume \<open>\<forall>\<alpha>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>})\<close>
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> for \<alpha> by (metis "Act-Basic:5" "\<equiv>E"(2))
  AOT_hence \<open>\<forall>\<alpha> \<^bold>\<A>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> by (rule "\<forall>I")
  AOT_thus \<open>\<^bold>\<A>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
    using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(2)] by fast
qed

AOT_act_theorem "act-quant-uniq": \<open>\<forall>\<beta>(\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>) \<equiv> \<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<beta>(\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> using "\<forall>E" by blast
  AOT_hence \<open>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta>
    using "\<equiv>I" "\<rightarrow>I" "RA[1]" "\<equiv>E"(1) "\<equiv>E"(2) "logic-actual"[act_axiom_inst] "vdash-properties:6"
    by metis
  AOT_thus \<open>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close> by (rule "\<forall>I")
next
  AOT_assume \<open>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  AOT_hence \<open>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta>
    using "\<equiv>I" "\<rightarrow>I" "RA[1]" "\<equiv>E"(1) "\<equiv>E"(2) "logic-actual"[act_axiom_inst] "vdash-properties:6"
    by metis
  AOT_thus \<open>\<forall>\<beta>(\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close> by (rule "\<forall>I")
qed

AOT_act_theorem "fund-cont-desc": \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> \<forall>z(\<phi>{z} \<equiv> z = x)\<close>
  using descriptions[axiom_inst] "act-quant-uniq" "\<equiv>E"(5) by fast

AOT_act_theorem hintikka: \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> (\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x))\<close>
  using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] "term-out:3" "fund-cont-desc" "\<equiv>E"(5) by blast


locale russel_axiom =
  fixes \<psi>
  assumes \<psi>_denotes_asm: "[v \<Turnstile> \<psi>{\<kappa>}] \<Longrightarrow> [v \<Turnstile> \<kappa>\<down>]"
begin
AOT_act_theorem "russell-axiom": \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}} \<equiv> \<exists>x(\<phi>{x} & \<forall>z(\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close>
proof -
  AOT_have b: \<open>\<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<phi>{x} & \<forall>z(\<phi>{z} \<rightarrow> z = x)))\<close>
    using hintikka "\<forall>I" by fast
  show ?thesis
  proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume c: \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}}\<close>
    AOT_hence d: \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> using \<psi>_denotes_asm by blast
    AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
    then AOT_obtain a where a_def: \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
    moreover AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<phi>{a} & \<forall>z(\<phi>{z} \<rightarrow> z = a))\<close> using b "\<forall>E" by blast
    ultimately AOT_have \<open>\<phi>{a} & \<forall>z(\<phi>{z} \<rightarrow> z = a)\<close> using "\<equiv>E" by blast
    moreover AOT_have \<open>\<psi>{a}\<close>
    proof - 
      AOT_have 1: \<open>\<forall>x\<forall>y(x = y \<rightarrow> y = x)\<close>
        by (simp add: "id-eq:2" "universal-cor")
      AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<rightarrow>  \<^bold>\<iota>x \<phi>{x} = a\<close>
        by (rule "\<forall>E"(1)[where \<tau>="\<guillemotleft>\<^bold>\<iota>x \<phi>{x}\<guillemotright>"]; rule "\<forall>E"(2)[where \<beta>=a])
           (auto simp: 1 d "universal-cor")
      AOT_thus \<open>\<psi>{a}\<close>
        using a_def c "=E" "\<rightarrow>E" by blast
    qed
    ultimately AOT_have \<open>\<phi>{a} & \<forall>z(\<phi>{z} \<rightarrow> z = a) & \<psi>{a}\<close> by (rule "&I")
    AOT_thus \<open>\<exists>x(\<phi>{x} & \<forall>z(\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close> by (rule "\<exists>I")
  next
    AOT_assume \<open>\<exists>x(\<phi>{x} & \<forall>z(\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close>
    then AOT_obtain b where g: \<open>\<phi>{b} & \<forall>z(\<phi>{z} \<rightarrow> z = b) & \<psi>{b}\<close> using "instantiation"[rotated] by blast
    AOT_hence h: \<open>b = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<phi>{b} & \<forall>z(\<phi>{z} \<rightarrow> z = b))\<close> using b "\<forall>E" by blast
    AOT_have \<open>\<phi>{b} & \<forall>z(\<phi>{z} \<rightarrow> z = b)\<close> and j: \<open>\<psi>{b}\<close> using g "&E" by blast+
    AOT_hence \<open>b = \<^bold>\<iota>x \<phi>{x}\<close> using h "\<equiv>E" by blast
    AOT_thus \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}}\<close> using j "=E" by blast
  qed
qed
end

(* TODO: this nicely shows off using locales with the embedding, but maybe there is still a nicer way *)
(* TODO: sledgehammer tends to refer to \<psi>_denotes_asm in these instantiation instead of referring
         to cqt:5:a - should be fixed *)
interpretation "russell-axiom[exe,1]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<guillemotright>\<close>
  by standard (metis "cqt:5:a[1]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[exe,2,1,1]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>'\<guillemotright>\<close>
  by standard (metis "cqt:5:a[2]"[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation "russell-axiom[exe,2,1,2]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>'\<kappa>\<guillemotright>\<close>
  by standard (metis "cqt:5:a[2]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[exe,2,2]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>\<guillemotright>\<close>
  by standard (metis "cqt:5:a[2]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[exe,3,1,1]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>'\<kappa>''\<guillemotright>\<close>
  by standard (metis "cqt:5:a[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation "russell-axiom[exe,3,1,2]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>'\<kappa>\<kappa>''\<guillemotright>\<close>
  by standard (metis "cqt:5:a[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation "russell-axiom[exe,3,1,3]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>'\<kappa>''\<kappa>\<guillemotright>\<close>
  by standard (metis "cqt:5:a[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[exe,3,2,1]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>\<kappa>'\<guillemotright>\<close>
  by standard (metis "cqt:5:a[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation "russell-axiom[exe,3,2,2]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>'\<kappa>\<guillemotright>\<close>
  by standard (metis "cqt:5:a[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[exe,3,2,3]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>'\<kappa>\<kappa>\<guillemotright>\<close>
  by standard (metis "cqt:5:a[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[exe,3,3]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>\<kappa>\<guillemotright>\<close>
  by standard (metis "cqt:5:a[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))

interpretation "russell-axiom[enc,1]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[1]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[enc,2,1]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>'[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[2]"[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation "russell-axiom[enc,2,2]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>'\<kappa>[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[2]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[enc,2,3]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[2]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[enc,3,1,1]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>'\<kappa>''[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation "russell-axiom[enc,3,1,2]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>'\<kappa>\<kappa>''[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation "russell-axiom[enc,3,1,3]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>'\<kappa>''\<kappa>[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[enc,3,2,1]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>\<kappa>'[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation "russell-axiom[enc,3,2,2]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>'\<kappa>[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[enc,3,2,3]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>'\<kappa>\<kappa>[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation "russell-axiom[enc,3,3]": russel_axiom \<open>\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>\<kappa>[\<Pi>]\<guillemotright>\<close>
  by standard (metis "cqt:5:b[3]"[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))

AOT_act_theorem "1-exists:1": \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<equiv> \<exists>!x \<phi>{x}\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  AOT_hence \<open>\<phi>{a} & \<forall>z (\<phi>{z} \<rightarrow> z = a)\<close> using hintikka "\<equiv>E" by blast
  AOT_hence \<open>\<exists>x (\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x))\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>!x \<phi>{x}\<close> using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
next
  AOT_assume \<open>\<exists>!x \<phi>{x}\<close>
  AOT_hence \<open>\<exists>x (\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x))\<close>
    using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain b where \<open>\<phi>{b} & \<forall>z (\<phi>{z} \<rightarrow> z = b)\<close> using "instantiation"[rotated] by blast
  AOT_hence \<open>b = \<^bold>\<iota>x \<phi>{x}\<close> using hintikka "\<equiv>E" by blast
  AOT_thus \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> by (metis "t=t-proper:2" "vdash-properties:6")
qed

AOT_act_theorem "1-exists:2": \<open>\<exists>y(y=\<^bold>\<iota>x \<phi>{x}) \<equiv> \<exists>!x \<phi>{x}\<close>
  using "1-exists:1" "free-thms:1" "\<equiv>E"(6) by blast

AOT_act_theorem "y-in:1": \<open>x = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{x}\<close>
  using "&E"(1) "\<rightarrow>I" hintikka "\<equiv>E"(1) by blast

AOT_act_theorem "y-in:2": \<open>z = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{z}\<close> using "y-in:1". (* TODO: same as above *)

AOT_act_theorem "y-in:3": \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<phi>{\<^bold>\<iota>x \<phi>{x}}\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>\<phi>{a}\<close> using calculation hintikka "\<equiv>E"(1) "&E" by blast
  ultimately AOT_show \<open>\<phi>{\<^bold>\<iota>x \<phi>{x}}\<close> using "=E" by blast
qed

AOT_act_theorem "y-in:4": \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x}) \<rightarrow> \<phi>{\<^bold>\<iota>x \<phi>{x}}\<close>
  using "y-in:3"[THEN "\<rightarrow>E"] "free-thms:1"[THEN "\<equiv>E"(2)] "\<rightarrow>I" by blast


AOT_theorem "act-quant-nec": \<open>\<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>) \<equiv> \<forall>\<beta>(\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> 
    by (metis "Act-Basic:5" "act-conj-act:4" "\<equiv>E"(1) "\<equiv>E"(5))
  AOT_thus \<open>\<forall>\<beta>(\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    by (rule "\<forall>I")
next
  AOT_assume \<open>\<forall>\<beta>(\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  AOT_hence \<open>\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta>
    by (metis "Act-Basic:5" "act-conj-act:4" "\<equiv>E"(1) "\<equiv>E"(6))
  AOT_thus \<open>\<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    by (rule "\<forall>I")
qed

AOT_theorem "equi-desc-descA:1": \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> x = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close>
proof -
  AOT_have \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> \<forall>z (\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>  using descriptions[axiom_inst] by blast
  also AOT_have \<open>... \<equiv> \<forall>z (\<^bold>\<A>\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
  proof(rule "\<equiv>I"; rule "\<rightarrow>I"; rule "\<forall>I")
    AOT_assume \<open>\<forall>z (\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
    AOT_hence \<open>\<^bold>\<A>\<phi>{a} \<equiv> a = x\<close> for a using "\<forall>E" by blast
    AOT_thus \<open>\<^bold>\<A>\<^bold>\<A>\<phi>{a} \<equiv> a = x\<close> for a by (metis "Act-Basic:5" "act-conj-act:4" "\<equiv>E"(1) "\<equiv>E"(5))
  next
    AOT_assume \<open>\<forall>z (\<^bold>\<A>\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
    AOT_hence \<open>\<^bold>\<A>\<^bold>\<A>\<phi>{a} \<equiv> a = x\<close> for a using "\<forall>E" by blast
    AOT_thus \<open>\<^bold>\<A>\<phi>{a} \<equiv> a = x\<close> for a  by (metis "Act-Basic:5" "act-conj-act:4" "\<equiv>E"(1) "\<equiv>E"(6))
  qed
  also AOT_have \<open>... \<equiv> x = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close>
    using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] descriptions[axiom_inst] by fast
  finally show ?thesis .
qed

AOT_theorem "equi-desc-descA:2": \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>a = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close> using calculation "equi-desc-descA:1"[THEN "\<equiv>E"(1)] by blast
  ultimately AOT_show \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close> using "=E" by fast
qed

AOT_theorem "nec-hintikka-scheme": \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> \<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x)\<close>
proof -
  AOT_have \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close> using descriptions[axiom_inst] by blast
  also AOT_have \<open>\<dots> \<equiv> (\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x))\<close>
    using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] "term-out:3" by fast
  finally show ?thesis.
qed

AOT_theorem "equiv-desc-eq:1": \<open>\<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> x = \<^bold>\<iota>x \<psi>{x})\<close>
proof(rule "\<rightarrow>I"; rule "\<forall>I")
  fix \<beta>
  AOT_assume \<open>\<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x})\<close>
  AOT_hence \<open>\<^bold>\<A>(\<phi>{x} \<equiv> \<psi>{x})\<close> for x using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(1)] "\<forall>E"(2) by blast
  AOT_hence 0: \<open>\<^bold>\<A>\<phi>{x} \<equiv> \<^bold>\<A>\<psi>{x}\<close> for x by (metis "Act-Basic:5" "\<equiv>E"(1))
  AOT_have \<open>\<beta> = \<^bold>\<iota>x \<phi>{x} \<equiv> \<^bold>\<A>\<phi>{\<beta>} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>)\<close> using "nec-hintikka-scheme" by blast
  also AOT_have \<open>... \<equiv> \<^bold>\<A>\<psi>{\<beta>} & \<forall>z(\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>)\<close>
  proof (rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume 1: \<open>\<^bold>\<A>\<phi>{\<beta>} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>)\<close>
    AOT_hence \<open>\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>\<close> for z using "&E" "\<forall>E" by blast
    AOT_hence \<open>\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>\<close> for z using 0 "\<equiv>E" "\<rightarrow>I" "\<rightarrow>E" by metis
    AOT_hence \<open>\<forall>z(\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>)\<close> using "\<forall>I" by fast
    moreover AOT_have \<open>\<^bold>\<A>\<psi>{\<beta>}\<close> using "&E" 0[THEN "\<equiv>E"(1)] 1 by blast
    ultimately AOT_show \<open>\<^bold>\<A>\<psi>{\<beta>} & \<forall>z(\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>)\<close> using "&I" by blast
  next
    AOT_assume 1: \<open>\<^bold>\<A>\<psi>{\<beta>} & \<forall>z(\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>)\<close>
    AOT_hence \<open>\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>\<close> for z using "&E" "\<forall>E" by blast
    AOT_hence \<open>\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>\<close> for z using 0 "\<equiv>E" "\<rightarrow>I" "\<rightarrow>E" by metis
    AOT_hence \<open>\<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>)\<close> using "\<forall>I" by fast
    moreover AOT_have \<open>\<^bold>\<A>\<phi>{\<beta>}\<close> using "&E" 0[THEN "\<equiv>E"(2)] 1 by blast
    ultimately AOT_show \<open>\<^bold>\<A>\<phi>{\<beta>} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>)\<close> using "&I" by blast
  qed
  also AOT_have \<open>... \<equiv> \<beta> = \<^bold>\<iota>x \<psi>{x}\<close>
    using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] "nec-hintikka-scheme" by blast
  finally AOT_show \<open>\<beta> = \<^bold>\<iota>x \<phi>{x} \<equiv> \<beta> = \<^bold>\<iota>x \<psi>{x}\<close> .
qed

AOT_theorem "equiv-desc-eq:2": \<open>\<^bold>\<iota>x \<phi>{x}\<down> & \<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down> & \<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x})\<close>
  AOT_hence 0: \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> and
            1: \<open>\<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> x = \<^bold>\<iota>x \<psi>{x})\<close>
    using "&E" "free-thms:1"[THEN "\<equiv>E"(1)] "equiv-desc-eq:1" "\<rightarrow>E" by blast+
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>a = \<^bold>\<iota>x \<psi>{x}\<close> using calculation 1 "\<forall>E" "\<equiv>E"(1) by fast
  ultimately AOT_show \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
    using "=E" by fast
qed

AOT_theorem "equiv-desc-eq:3": \<open>\<^bold>\<iota>x \<phi>{x}\<down> & \<box>\<forall>x(\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
  using "\<rightarrow>I" "equiv-desc-eq:2"[THEN "\<rightarrow>E", OF "&I"] "&E" "nec-imp-act"[THEN "\<rightarrow>E"] by metis

(* Note: this is a special case of "exist-nec" *)
AOT_theorem "equiv-desc-eq:4": \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<box>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  AOT_thus \<open>\<box>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
    using "ex:2:a" "=E" by fast
qed

AOT_theorem "equiv-desc-eq:5": \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<exists>y \<box>(y = \<^bold>\<iota>x \<phi>{x})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  AOT_hence \<open>\<box>(a = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "id-nec:2" "vdash-properties:10")
  AOT_thus \<open>\<exists>y \<box>(y = \<^bold>\<iota>x \<phi>{x})\<close> by (rule "\<exists>I")
qed

AOT_act_theorem "equiv-desc-eq2:1": \<open>\<forall>x (\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> x = \<^bold>\<iota>x \<psi>{x})\<close>
  using "\<rightarrow>I" "logic-actual"[act_axiom_inst, THEN "\<rightarrow>E"] "equiv-desc-eq:1"[THEN "\<rightarrow>E"]
        "RA[1]" "deduction-theorem" by blast

AOT_act_theorem "equiv-desc-eq2:2": \<open>\<^bold>\<iota>x \<phi>{x}\<down> & \<forall>x (\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
  using "\<rightarrow>I" "logic-actual"[act_axiom_inst, THEN "\<rightarrow>E"] "equiv-desc-eq:2"[THEN "\<rightarrow>E", OF "&I"]
        "RA[1]" "deduction-theorem" "&E" by metis

context russel_axiom
begin
AOT_theorem "nec-russell-axiom": \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}} \<equiv> \<exists>x(\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close>
proof -
  AOT_have b: \<open>\<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x)))\<close>
    using "nec-hintikka-scheme" "\<forall>I" by fast
  show ?thesis
  proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume c: \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}}\<close>
    AOT_hence d: \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> using \<psi>_denotes_asm by blast
    AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
    then AOT_obtain a where a_def: \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
    moreover AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<^bold>\<A>\<phi>{a} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = a))\<close> using b "\<forall>E" by blast
    ultimately AOT_have \<open>\<^bold>\<A>\<phi>{a} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = a)\<close> using "\<equiv>E" by blast
    moreover AOT_have \<open>\<psi>{a}\<close>
    proof - 
      AOT_have 1: \<open>\<forall>x\<forall>y(x = y \<rightarrow> y = x)\<close>
        by (simp add: "id-eq:2" "universal-cor")
      AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<rightarrow>  \<^bold>\<iota>x \<phi>{x} = a\<close>
        by (rule "\<forall>E"(1)[where \<tau>="\<guillemotleft>\<^bold>\<iota>x \<phi>{x}\<guillemotright>"]; rule "\<forall>E"(2)[where \<beta>=a])
           (auto simp: d "universal-cor" 1)
      AOT_thus \<open>\<psi>{a}\<close>
        using a_def c "=E" "\<rightarrow>E" by metis
    qed
    ultimately AOT_have \<open>\<^bold>\<A>\<phi>{a} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = a) & \<psi>{a}\<close> by (rule "&I")
    AOT_thus \<open>\<exists>x(\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close> by (rule "\<exists>I")
  next
    AOT_assume \<open>\<exists>x(\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close>
    then AOT_obtain b where g: \<open>\<^bold>\<A>\<phi>{b} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = b) & \<psi>{b}\<close> using "instantiation"[rotated] by blast
    AOT_hence h: \<open>b = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<^bold>\<A>\<phi>{b} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = b))\<close> using b "\<forall>E" by blast
    AOT_have \<open>\<^bold>\<A>\<phi>{b} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = b)\<close> and j: \<open>\<psi>{b}\<close> using g "&E" by blast+
    AOT_hence \<open>b = \<^bold>\<iota>x \<phi>{x}\<close> using h "\<equiv>E" by blast
    AOT_thus \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}}\<close> using j "=E" by blast
  qed
qed
end

AOT_theorem "actual-desc:1": \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<equiv> \<exists>!x \<^bold>\<A>\<phi>{x}\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = a)\<close>
    using descriptions[axiom_inst] by blast
  ultimately AOT_have \<open>\<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = a)\<close>
    using "\<equiv>E" by blast
  AOT_hence \<open>\<exists>x\<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>!x \<^bold>\<A>\<phi>{x}\<close>
    using "uniqueness:2"[THEN "\<equiv>E"(2)] by fast
next
  AOT_assume \<open>\<exists>!x \<^bold>\<A>\<phi>{x}\<close>
  AOT_hence \<open>\<exists>x\<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
    using "uniqueness:2"[THEN "\<equiv>E"(1)] by fast
  then AOT_obtain a where \<open>\<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = a)\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = a)\<close>
    using descriptions[axiom_inst] by blast
  ultimately AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "\<equiv>E" by blast
  AOT_thus \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> by (metis "t=t-proper:2" "vdash-properties:6")
qed

AOT_theorem "actual-desc:2": \<open>x = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<^bold>\<A>\<phi>{x}\<close>
  using "&E"(1) "contraposition:1[2]" "\<equiv>E"(1) "nec-hintikka-scheme" "reductio-aa:2" "vdash-properties:9" by blast

AOT_theorem "actual-desc:3": \<open>z = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<^bold>\<A>\<phi>{z}\<close>
  using "actual-desc:2". (* TODO: same as above *)

AOT_theorem "actual-desc:4": \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<^bold>\<A>\<phi>{\<^bold>\<iota>x \<phi>{x}}\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I:1" "existential:1")
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  AOT_thus \<open>\<^bold>\<A>\<phi>{\<^bold>\<iota>x \<phi>{x}}\<close>
    using "actual-desc:2" "=E" "\<rightarrow>E" by fast
qed

(* TODO: take another look at proof in PLM *)
AOT_theorem "actual-desc:5": \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x} \<rightarrow> \<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
  AOT_hence \<phi>_down: \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> and \<psi>_down: \<open>\<^bold>\<iota>x \<psi>{x}\<down>\<close>
    using "t=t-proper:1" "t=t-proper:2" "vdash-properties:6" by blast+
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> and \<open>\<exists>y (y = \<^bold>\<iota>x \<psi>{x})\<close> by (metis "rule=I:1" "existential:1")+
  then AOT_obtain a and b where a_eq: \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> and b_eq: \<open>b = \<^bold>\<iota>x \<psi>{x}\<close>
    using "instantiation"[rotated] by metis

  AOT_have \<open>\<forall>\<alpha>\<forall>\<beta> (\<alpha> = \<beta> \<rightarrow> \<beta> = \<alpha>)\<close> by (rule "\<forall>I"; rule "\<forall>I"; rule "id-eq:2")
  AOT_hence \<open>\<forall>\<beta> (\<^bold>\<iota>x \<phi>{x} = \<beta> \<rightarrow> \<beta> = \<^bold>\<iota>x \<phi>{x})\<close>
    using "\<forall>E" \<phi>_down by blast
  AOT_hence \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x} \<rightarrow> \<^bold>\<iota>x \<psi>{x} = \<^bold>\<iota>x \<phi>{x}\<close>
    using "\<forall>E" \<psi>_down by blast
  AOT_hence 1: \<open>\<^bold>\<iota>x \<psi>{x} = \<^bold>\<iota>x \<phi>{x}\<close> using 0
    "\<rightarrow>E" by blast

  AOT_have \<open>\<^bold>\<A>\<phi>{x} \<equiv> \<^bold>\<A>\<psi>{x}\<close> for x
  proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>\<^bold>\<A>\<phi>{x}\<close>
    moreover AOT_have \<open>\<^bold>\<A>\<phi>{x} \<rightarrow> x = a\<close> for x
      using "nec-hintikka-scheme"[THEN "\<equiv>E"(1), OF a_eq, THEN "&E"(2)] "\<forall>E" by blast
    ultimately AOT_have \<open>x = a\<close> using "\<rightarrow>E" by blast
    AOT_hence \<open>x = \<^bold>\<iota>x \<phi>{x}\<close> using a_eq "=E" by blast
    AOT_hence \<open>x = \<^bold>\<iota>x \<psi>{x}\<close> using 0 "=E" by blast
    AOT_thus \<open>\<^bold>\<A>\<psi>{x}\<close> by (metis "actual-desc:3" "vdash-properties:6")
  next
    AOT_assume \<open>\<^bold>\<A>\<psi>{x}\<close>
    moreover AOT_have \<open>\<^bold>\<A>\<psi>{x} \<rightarrow> x = b\<close> for x
      using "nec-hintikka-scheme"[THEN "\<equiv>E"(1), OF b_eq, THEN "&E"(2)] "\<forall>E" by blast
    ultimately AOT_have \<open>x = b\<close> using "\<rightarrow>E" by blast
    AOT_hence \<open>x = \<^bold>\<iota>x \<psi>{x}\<close> using b_eq "=E" by blast
    AOT_hence \<open>x = \<^bold>\<iota>x \<phi>{x}\<close> using 1 "=E" by blast
    AOT_thus \<open>\<^bold>\<A>\<phi>{x}\<close> by (metis "actual-desc:3" "vdash-properties:6")
  qed
  AOT_hence \<open>\<^bold>\<A>(\<phi>{x} \<equiv> \<psi>{x})\<close> for x by (metis "Act-Basic:5" "\<equiv>E"(2))
  AOT_hence \<open>\<forall>x \<^bold>\<A>(\<phi>{x} \<equiv> \<psi>{x})\<close> by (rule "\<forall>I")
  AOT_thus \<open>\<^bold>\<A>\<forall>x (\<phi>{x} \<equiv> \<psi>{x})\<close>
    using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(2)] by fast
qed    

AOT_theorem "!box-desc:1": \<open>\<exists>!x \<box>\<phi>{x} \<rightarrow> \<forall>y (y = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{y})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>!x \<box>\<phi>{x}\<close>
  AOT_hence \<zeta>: \<open>\<exists>x (\<box>\<phi>{x} & \<forall>z (\<box>\<phi>{z} \<rightarrow> z = x))\<close>
    using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain b where \<theta>: \<open>\<box>\<phi>{b} & \<forall>z (\<box>\<phi>{z} \<rightarrow> z = b)\<close> using "instantiation"[rotated] by blast
  AOT_show \<open>\<forall>y (y = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{y})\<close>
  proof(rule GEN; rule "\<rightarrow>I")
    fix y
    AOT_assume \<open>y = \<^bold>\<iota>x \<phi>{x}\<close>
    AOT_hence \<open>\<^bold>\<A>\<phi>{y} & \<forall>z (\<^bold>\<A>\<phi>{z} \<rightarrow> z = y)\<close> using "nec-hintikka-scheme"[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<^bold>\<A>\<phi>{b} \<rightarrow> b = y\<close> using "&E" "\<forall>E" by blast
    moreover AOT_have \<open>\<^bold>\<A>\<phi>{b}\<close> using \<theta>[THEN "&E"(1)]  by (metis "nec-imp-act" "\<rightarrow>E")
    ultimately AOT_have \<open>b = y\<close> using "\<rightarrow>E" by blast
    moreover AOT_have \<open>\<phi>{b}\<close> using \<theta>[THEN "&E"(1)]  by (metis "qml:2"[axiom_inst] "\<rightarrow>E") 
    ultimately AOT_show \<open>\<phi>{y}\<close> using "=E" by blast
  qed
qed

AOT_theorem "!box-desc:2": \<open>\<forall>x (\<phi>{x} \<rightarrow> \<box>\<phi>{x}) \<rightarrow> (\<exists>!x \<phi>{x} \<rightarrow> \<forall>y (y = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{y}))\<close>
proof(rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>x (\<phi>{x} \<rightarrow> \<box>\<phi>{x})\<close>
  moreover AOT_assume \<open>\<exists>!x \<phi>{x}\<close>
  ultimately AOT_have \<open>\<exists>!x \<box>\<phi>{x}\<close>
    using "nec-exist-!"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<forall>y (y = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{y})\<close>
    using "!box-desc:1" "\<rightarrow>E" by blast
qed

AOT_theorem "dr-alphabetic-thm": \<open>\<^bold>\<iota>\<nu> \<phi>{\<nu>}\<down> \<rightarrow> \<^bold>\<iota>\<nu> \<phi>{\<nu>} = \<^bold>\<iota>\<mu> \<phi>{\<mu>}\<close> (* TODO: vacuous *)
  by (simp add: "rule=I:1" "\<rightarrow>I")

AOT_theorem "RM:1[prem]": assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<rightarrow> \<box>\<psi>\<close>
proof -
  AOT_have \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>(\<phi> \<rightarrow> \<psi>)\<close> using "RN[prem]" assms by blast
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<rightarrow> \<box>\<psi>\<close> by (metis "qml:1"[axiom_inst] "\<rightarrow>E")
qed

AOT_theorem "RM:1": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<rightarrow> \<box>\<psi>\<close>
  using "RM:1[prem]" assms by blast

lemmas RM = "RM:1"

AOT_theorem "RM:2[prem]": assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
proof -
  AOT_have \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<not>\<psi> \<rightarrow> \<not>\<phi>\<close> using assms 
    by (simp add: "contraposition:1[1]")
  AOT_hence \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<not>\<psi> \<rightarrow> \<box>\<not>\<phi>\<close> using "RM:1[prem]" by blast
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fE" "\<equiv>\<^sub>d\<^sub>fI" AOT_dia "deduction-theorem" "modus-tollens:1")
qed

AOT_theorem "RM:2": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
  using "RM:2[prem]" assms by blast

lemmas "RM\<diamond>" = "RM:2"

AOT_theorem "RM:3[prem]": assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<equiv> \<box>\<psi>\<close>
proof -
  AOT_have \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> and \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<psi> \<rightarrow> \<phi>\<close> using assms "\<equiv>E" "\<rightarrow>I" by metis+
  AOT_hence \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<rightarrow> \<box>\<psi>\<close> and \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<psi> \<rightarrow> \<box>\<phi>\<close> using "RM:1[prem]" by metis+
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<equiv> \<box>\<psi>\<close>
    by (simp add: "\<equiv>I")
qed

AOT_theorem "RM:3": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<psi>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<equiv> \<box>\<psi>\<close>
  using "RM:3[prem]" assms by blast

lemmas RE = "RM:3"

AOT_theorem "RM:4[prem]": assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<equiv> \<diamond>\<psi>\<close>
proof -
  AOT_have \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> and \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<psi> \<rightarrow> \<phi>\<close> using assms "\<equiv>E" "\<rightarrow>I" by metis+
  AOT_hence \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close> and \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<psi> \<rightarrow> \<diamond>\<phi>\<close> using "RM:2[prem]" by metis+
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<equiv> \<diamond>\<psi>\<close> by (simp add: "\<equiv>I")
qed

AOT_theorem "RM:4": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<psi>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<equiv> \<diamond>\<psi>\<close>
  using "RM:4[prem]" assms by blast

lemmas "RE\<diamond>" = "RM:4"

AOT_theorem "KBasic:1": \<open>\<box>\<phi> \<rightarrow> \<box>(\<psi> \<rightarrow> \<phi>)\<close>
  by (simp add: RM "pl:1"[axiom_inst])

AOT_theorem "KBasic:2": \<open>\<box>\<not>\<phi> \<rightarrow> \<box>(\<phi> \<rightarrow> \<psi>)\<close>
  by (simp add: RM "useful-tautologies:3")

AOT_theorem "KBasic:3": \<open>\<box>(\<phi> & \<psi>) \<equiv> (\<box>\<phi> & \<box>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<box>(\<phi> & \<psi>)\<close>
  AOT_thus \<open>\<box>\<phi> & \<box>\<psi>\<close>
    by (meson RM "&I" "Conjunction Simplification"(1) "Conjunction Simplification"(2) "vdash-properties:6")
next
  AOT_have \<open>\<box>\<phi> \<rightarrow> \<box>(\<psi> \<rightarrow> (\<phi> & \<psi>))\<close> by (simp add: "RM:1" Adjunction)
  AOT_hence \<open>\<box>\<phi> \<rightarrow> (\<box>\<psi> \<rightarrow> \<box>(\<phi> & \<psi>))\<close>  by (metis "Hypothetical Syllogism" "qml:1"[axiom_inst])
  moreover AOT_assume \<open>\<box>\<phi> & \<box>\<psi>\<close>
  ultimately AOT_show \<open>\<box>(\<phi> & \<psi>)\<close>
    using "\<rightarrow>E" "&E" by blast
qed

AOT_theorem "KBasic:4": \<open>\<box>(\<phi> \<equiv> \<psi>) \<equiv> (\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>))\<close>
proof -
  AOT_have \<theta>: \<open>\<box>((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)) \<equiv> (\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>))\<close>
    by (fact "KBasic:3")
  AOT_modally_strict {
    AOT_have \<open>(\<phi> \<equiv> \<psi>) \<equiv> ((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>))\<close>
      by (fact AOT_equiv[THEN "\<equiv>Df"])
  }
  AOT_hence \<xi>: \<open>\<box>(\<phi> \<equiv> \<psi>) \<equiv> \<box>((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>))\<close>
    by (rule RE)
  with \<xi> and \<theta> AOT_show \<open>\<box>(\<phi> \<equiv> \<psi>) \<equiv> (\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>))\<close>
    using "\<equiv>E"(5) by blast
qed

AOT_theorem "KBasic:5": \<open>(\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>)) \<rightarrow> (\<box>\<phi> \<equiv> \<box>\<psi>)\<close>
proof -
  AOT_have \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<box>\<phi> \<rightarrow> \<box>\<psi>)\<close>
    by (fact "qml:1"[axiom_inst])
  moreover AOT_have \<open>\<box>(\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<box>\<psi> \<rightarrow> \<box>\<phi>)\<close>
    by (fact "qml:1"[axiom_inst])
  ultimately AOT_have \<open>(\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>)) \<rightarrow> ((\<box>\<phi> \<rightarrow> \<box>\<psi>) & (\<box>\<psi> \<rightarrow> \<box>\<phi>))\<close>
    by (metis "&I" MP "Double Composition")
  moreover AOT_have \<open>((\<box>\<phi> \<rightarrow> \<box>\<psi>) & (\<box>\<psi> \<rightarrow> \<box>\<phi>)) \<rightarrow> (\<box>\<phi> \<equiv> \<box>\<psi>)\<close>
    using AOT_equiv[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<rightarrow>I" by blast
  ultimately AOT_show \<open>(\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>)) \<rightarrow> (\<box>\<phi> \<equiv> \<box>\<psi>)\<close>
    by (metis "Hypothetical Syllogism")
qed

AOT_theorem "KBasic:6": \<open>\<box>(\<phi>\<equiv> \<psi>) \<rightarrow> (\<box>\<phi> \<equiv> \<box>\<psi>)\<close>
  using "KBasic:4" "KBasic:5" "deduction-theorem" "\<equiv>E"(1) "vdash-properties:10" by blast
AOT_theorem "KBasic:7": \<open>((\<box>\<phi> & \<box>\<psi>) \<or> (\<box>\<not>\<phi> & \<box>\<not>\<psi>)) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
proof (rule "\<rightarrow>I"; drule "\<or>E"(1); (rule "\<rightarrow>I")?)
  AOT_assume \<open>\<box>\<phi> & \<box>\<psi>\<close>
  AOT_hence \<open>\<box>\<phi>\<close> and \<open>\<box>\<psi>\<close> using "&E" by blast+
  AOT_hence \<open>\<box>(\<phi> \<rightarrow> \<psi>)\<close> and \<open>\<box>(\<psi> \<rightarrow> \<phi>)\<close> using "KBasic:1" "\<rightarrow>E" by blast+
  AOT_hence \<open>\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>)\<close> using "&I" by blast
  AOT_thus \<open>\<box>(\<phi> \<equiv> \<psi>)\<close>  by (metis "KBasic:4" "\<equiv>E"(2))
next
  AOT_assume \<open>\<box>\<not>\<phi> & \<box>\<not>\<psi>\<close>
  AOT_hence 0: \<open>\<box>(\<not>\<phi> & \<not>\<psi>)\<close> using "KBasic:3"[THEN "\<equiv>E"(2)] by blast
  AOT_modally_strict {
    AOT_have \<open>(\<not>\<phi> & \<not>\<psi>) \<rightarrow> (\<phi> \<equiv> \<psi>)\<close>
      by (metis "&E"(1) "&E"(2) "deduction-theorem" "\<equiv>I" "reductio-aa:1")
  }
  AOT_hence \<open>\<box>(\<not>\<phi> & \<not>\<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
    by (rule RM)
  AOT_thus \<open>\<box>(\<phi> \<equiv> \<psi>)\<close> using 0 "\<rightarrow>E" by blast
qed(auto)

AOT_theorem "KBasic:8": \<open>\<box>(\<phi> & \<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
  by (meson "RM:1" "&E"(1) "&E"(2) "deduction-theorem" "\<equiv>I")
AOT_theorem "KBasic:9": \<open>\<box>(\<not>\<phi> & \<not>\<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
  by (metis "RM:1" "&E"(1) "&E"(2) "deduction-theorem" "\<equiv>I" "raa-cor:4")
AOT_theorem "KBasic:10": \<open>\<box>\<phi> \<equiv> \<box>\<not>\<not>\<phi>\<close>
  by (simp add: "RM:3" "oth-class-taut:3:b")
AOT_theorem "KBasic:11": \<open>\<not>\<box>\<phi> \<equiv> \<diamond>\<not>\<phi>\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_show \<open>\<diamond>\<not>\<phi>\<close> if \<open>\<not>\<box>\<phi>\<close>
    using that "\<equiv>\<^sub>d\<^sub>fI" AOT_dia "KBasic:10" "\<equiv>E"(3) by blast
next
  AOT_show \<open>\<not>\<box>\<phi>\<close> if \<open>\<diamond>\<not>\<phi>\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" AOT_dia "KBasic:10" "\<equiv>E"(4) that by blast
qed
AOT_theorem "KBasic:12": \<open>\<box>\<phi> \<equiv> \<not>\<diamond>\<not>\<phi>\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_show \<open>\<not>\<diamond>\<not>\<phi>\<close> if \<open>\<box>\<phi>\<close>
    using "\<not>\<not>I" "KBasic:11" "\<equiv>E"(3) that by blast
next
  AOT_show \<open>\<box>\<phi>\<close> if \<open>\<not>\<diamond>\<not>\<phi>\<close>
  using "KBasic:11" "\<equiv>E"(1) "reductio-aa:1" that by blast
qed
AOT_theorem "KBasic:13": \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<diamond>\<phi> \<rightarrow> \<diamond>\<psi>)\<close>
proof -
  AOT_have \<open>\<phi> \<rightarrow> \<psi> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> by blast
  AOT_hence \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
    using "RM:2[prem]" by blast
  AOT_thus \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<diamond>\<phi> \<rightarrow> \<diamond>\<psi>)\<close> using "\<rightarrow>I" by blast
qed
lemmas "K\<diamond>" = "KBasic:13"
AOT_theorem "KBasic:14": \<open>\<diamond>\<box>\<phi> \<equiv> \<not>\<box>\<diamond>\<not>\<phi>\<close>
  by (meson "RE\<diamond>" "KBasic:11" "KBasic:12" "\<equiv>E"(6) "oth-class-taut:3:a")
AOT_theorem "KBasic:15": \<open>(\<box>\<phi> \<or> \<box>\<psi>) \<rightarrow> \<box>(\<phi> \<or> \<psi>)\<close>
proof -
  AOT_modally_strict {
    AOT_have \<open>\<phi> \<rightarrow> (\<phi> \<or> \<psi>)\<close> and \<open>\<psi> \<rightarrow> (\<phi> \<or> \<psi>)\<close>
      by (auto simp: "Disjunction Addition"(1) "Disjunction Addition"(2))
  }
  AOT_hence \<open>\<box>\<phi> \<rightarrow> \<box>(\<phi> \<or> \<psi>)\<close> and \<open>\<box>\<psi> \<rightarrow> \<box>(\<phi> \<or> \<psi>)\<close>
    using RM by blast+
  AOT_thus \<open>(\<box>\<phi> \<or> \<box>\<psi>) \<rightarrow> \<box>(\<phi> \<or> \<psi>)\<close>
    by (metis "\<or>E"(1) "deduction-theorem")
qed

AOT_theorem "KBasic:16": \<open>(\<box>\<phi> & \<diamond>\<psi>) \<rightarrow> \<diamond>(\<phi> & \<psi>)\<close>
  by (meson "KBasic:13" "RM:1" Adjunction "Hypothetical Syllogism" Importation "vdash-properties:6")

AOT_theorem "rule-sub-lem:1:a":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<not>\<psi> \<equiv> \<not>\<chi>\<close>
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E", OF assms]
        "\<equiv>E"(1) "oth-class-taut:4:b" by blast

AOT_theorem "rule-sub-lem:1:b":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> (\<psi> \<rightarrow> \<Theta>) \<equiv> (\<chi> \<rightarrow> \<Theta>)\<close>
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E", OF assms]
  using "oth-class-taut:4:c" "vdash-properties:6" by blast

AOT_theorem "rule-sub-lem:1:c":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> (\<Theta> \<rightarrow> \<psi>) \<equiv> (\<Theta> \<rightarrow> \<chi>)\<close>
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E", OF assms]
  using "oth-class-taut:4:d" "vdash-properties:6" by blast

AOT_theorem "rule-sub-lem:1:d":
  assumes \<open>for arbitrary \<alpha>: \<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>\<alpha> \<psi>{\<alpha>} \<equiv> \<forall>\<alpha> \<chi>{\<alpha>}\<close>
proof -
  AOT_modally_strict {
    AOT_have \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
      using "qml:2"[axiom_inst, THEN "\<rightarrow>E", OF assms] "\<forall>I" by fast
    AOT_hence 0: \<open>\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast
    AOT_show \<open>\<forall>\<alpha> \<psi>{\<alpha>} \<equiv> \<forall>\<alpha> \<chi>{\<alpha>}\<close>
    proof (rule "\<equiv>I"; rule "\<rightarrow>I")
      AOT_assume \<open>\<forall>\<alpha> \<psi>{\<alpha>}\<close>
      AOT_hence \<open>\<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast
      AOT_hence \<open>\<chi>{\<alpha>}\<close> for \<alpha> using 0 "\<equiv>E" by blast
      AOT_thus \<open>\<forall>\<alpha> \<chi>{\<alpha>}\<close> by (rule "\<forall>I")
    next
      AOT_assume \<open>\<forall>\<alpha> \<chi>{\<alpha>}\<close>
      AOT_hence \<open>\<chi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast
      AOT_hence \<open>\<psi>{\<alpha>}\<close> for \<alpha> using 0 "\<equiv>E" by blast
      AOT_thus \<open>\<forall>\<alpha> \<psi>{\<alpha>}\<close> by (rule "\<forall>I")
    qed
  }
qed

AOT_theorem "rule-sub-lem:1:e":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda> \<psi>] \<equiv> [\<lambda> \<chi>]\<close>
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E", OF assms]
  using "\<equiv>E"(1) "propositions-lemma:6" by blast

AOT_theorem "rule-sub-lem:1:f":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<psi> \<equiv> \<^bold>\<A>\<chi>\<close>
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E", OF assms, THEN "RA[2]"]
  by (metis "Act-Basic:5" "\<equiv>E"(1))

AOT_theorem "rule-sub-lem:1:g":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>\<psi> \<equiv> \<box>\<chi>\<close>
  using "KBasic:6" assms "vdash-properties:6" by blast

text\<open>Note that instead of deriving @{text "rule-sub-lem:2"}, @{text "rule-sub-lem:3"}, @{text "rule-sub-lem:4"},
     and @{text "rule-sub-nec"}, we construct substitution methods instead.\<close>

class AOT_subst =
  fixes AOT_subst :: "('a \<Rightarrow> \<o>) \<Rightarrow> bool"
    and AOT_subst_cond :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes AOT_subst: "AOT_subst \<phi> \<Longrightarrow> AOT_subst_cond \<psi> \<chi> \<Longrightarrow> [v \<Turnstile> \<guillemotleft>\<phi> \<psi>\<guillemotright> \<equiv> \<guillemotleft>\<phi> \<chi>\<guillemotright>]"

named_theorems AOT_substI

instantiation \<o> :: AOT_subst
begin

inductive AOT_subst_\<o> where
  AOT_subst_\<o>_id[AOT_substI]: "AOT_subst_\<o> (\<lambda>\<phi>. \<phi>)"
| AOT_subst_\<o>_const[AOT_substI]: "AOT_subst_\<o> (\<lambda>\<phi>. \<psi>)"
| AOT_subst_\<o>_not[AOT_substI]: "AOT_subst_\<o> \<Theta> \<Longrightarrow> AOT_subst_\<o> (\<lambda> \<phi>. \<guillemotleft>\<not>\<Theta>{\<phi>}\<guillemotright>)"
| AOT_subst_\<o>_imp[AOT_substI]: "AOT_subst_\<o> \<Theta> \<Longrightarrow> AOT_subst_\<o> \<Xi> \<Longrightarrow> AOT_subst_\<o> (\<lambda> \<phi>. \<guillemotleft>\<Theta>{\<phi>} \<rightarrow> \<Xi>{\<phi>}\<guillemotright>)"
| AOT_subst_\<o>_lambda0[AOT_substI]: "AOT_subst_\<o> \<Theta> \<Longrightarrow> AOT_subst_\<o> (\<lambda> \<phi>. (AOT_lambda0 (\<Theta> \<phi>)))"
| AOT_subst_\<o>_act[AOT_substI]: "AOT_subst_\<o> \<Theta> \<Longrightarrow> AOT_subst_\<o> (\<lambda> \<phi>. \<guillemotleft>\<^bold>\<A>\<Theta>{\<phi>}\<guillemotright>)"
| AOT_subst_\<o>_box[AOT_substI]: "AOT_subst_\<o> \<Theta> \<Longrightarrow> AOT_subst_\<o> (\<lambda> \<phi>. \<guillemotleft>\<box>\<Theta>{\<phi>}\<guillemotright>)"
| AOT_subst_\<o>_by_def[AOT_substI]: "(\<And> \<psi> . AOT_model_equiv_def (\<Theta> \<psi>) (\<Xi> \<psi>)) \<Longrightarrow> AOT_subst_\<o> \<Xi> \<Longrightarrow> AOT_subst_\<o> \<Theta>"

definition AOT_subst_cond_\<o> where "AOT_subst_cond_\<o> \<equiv> \<lambda> \<psi> \<chi> . \<forall> v . [v \<Turnstile> \<psi> \<equiv> \<chi>]"

instance
proof
  fix \<psi> \<chi> :: \<o> and \<phi> :: \<open>\<o> \<Rightarrow> \<o>\<close>
  assume cond: \<open>AOT_subst_cond \<psi> \<chi>\<close>
  assume \<open>AOT_subst \<phi>\<close>
  moreover AOT_have \<open>\<^bold>\<turnstile>\<^sub>\<box> \<psi> \<equiv> \<chi>\<close> using cond unfolding AOT_subst_cond_\<o>_def by blast
  ultimately AOT_show \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>{\<psi>} \<equiv> \<phi>{\<chi>}\<close>
  proof (induct arbitrary: \<psi> \<chi>)
    case AOT_subst_\<o>_id
    thus ?case using "\<equiv>E"(2) "oth-class-taut:4:b" "rule-sub-lem:1:a" by blast
  next
    case (AOT_subst_\<o>_const \<psi>)
    thus ?case by (simp add: "oth-class-taut:3:a")
  next
    case (AOT_subst_\<o>_not \<Theta>)
    thus ?case by (simp add: RN "rule-sub-lem:1:a")
  next
    case (AOT_subst_\<o>_imp \<Theta> \<Xi>)
    thus ?case by (meson RN "\<equiv>E"(5) "rule-sub-lem:1:b" "rule-sub-lem:1:c")
  next
    case (AOT_subst_\<o>_lambda0 \<Theta>)
    thus ?case by (simp add: RN "rule-sub-lem:1:e")
  next
    case (AOT_subst_\<o>_act \<Theta>)
    thus ?case by (simp add: RN "rule-sub-lem:1:f")
  next
    case (AOT_subst_\<o>_box \<Theta>)
    thus ?case by (simp add: RN "rule-sub-lem:1:g")
  next
    case (AOT_subst_\<o>_by_def \<Theta> \<Xi>)
    AOT_modally_strict {
      AOT_have \<open>\<Xi>{\<psi>} \<equiv> \<Xi>{\<chi>}\<close> using AOT_subst_\<o>_by_def by simp
      AOT_thus \<open>\<Theta>{\<psi>} \<equiv> \<Theta>{\<chi>}\<close>
        using "\<equiv>Df"[OF AOT_subst_\<o>_by_def(1), of _ \<psi>] "\<equiv>Df"[OF AOT_subst_\<o>_by_def(1), of _ \<chi>]
        by (metis "\<equiv>E"(6) "oth-class-taut:3:a")
    }
  qed
qed
end

instantiation "fun" :: (AOT_Term_id_2, AOT_subst) AOT_subst
begin

definition AOT_subst_cond_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "AOT_subst_cond_fun \<equiv> \<lambda> \<phi> \<psi> . \<forall> \<alpha> . AOT_subst_cond (\<phi> (AOT_term_of_var \<alpha>)) (\<psi> (AOT_term_of_var \<alpha>))"

inductive AOT_subst_fun :: "(('a \<Rightarrow> 'b) \<Rightarrow> \<o>) \<Rightarrow> bool" where
  AOT_subst_fun_const[AOT_substI]: "AOT_subst_fun (\<lambda>\<phi>. \<psi>)"
| AOT_subst_fun_id[AOT_substI]: "AOT_subst \<Psi> \<Longrightarrow> AOT_subst_fun (\<lambda>\<phi>. \<Psi> (\<phi> (AOT_term_of_var x)))"
| AOT_subst_fun_all[AOT_substI]: "AOT_subst \<Psi> \<Longrightarrow> (\<And> \<alpha> . AOT_subst_fun (\<Theta> (AOT_term_of_var \<alpha>))) \<Longrightarrow> AOT_subst_fun (\<lambda>\<phi> :: 'a \<Rightarrow> 'b. \<Psi> \<guillemotleft>\<forall>\<alpha> \<guillemotleft>\<Theta> (\<alpha>::'a) \<phi>\<guillemotright>\<guillemotright>)"
| AOT_subst_fun_not[AOT_substI]: "AOT_subst \<Psi> \<Longrightarrow> AOT_subst_fun (\<lambda>\<phi>. \<guillemotleft>\<not>\<guillemotleft>\<Psi> \<phi>\<guillemotright>\<guillemotright>)"
| AOT_subst_fun_imp[AOT_substI]: "AOT_subst \<Psi> \<Longrightarrow> AOT_subst \<Theta> \<Longrightarrow> AOT_subst_fun (\<lambda>\<phi>. \<guillemotleft>\<guillemotleft>\<Psi> \<phi>\<guillemotright> \<rightarrow> \<guillemotleft>\<Theta> \<phi>\<guillemotright>\<guillemotright>)"
| AOT_subst_fun_lambda0[AOT_substI]: "AOT_subst \<Theta> \<Longrightarrow> AOT_subst_fun (\<lambda> \<phi>. (AOT_lambda0 (\<Theta> \<phi>)))"
| AOT_subst_fun_act[AOT_substI]: "AOT_subst \<Theta> \<Longrightarrow> AOT_subst_fun (\<lambda> \<phi>. \<guillemotleft>\<^bold>\<A>\<guillemotleft>\<Theta> \<phi>\<guillemotright>\<guillemotright>)"
| AOT_subst_fun_box[AOT_substI]: "AOT_subst \<Theta> \<Longrightarrow> AOT_subst_fun (\<lambda> \<phi>. \<guillemotleft>\<box>\<guillemotleft>\<Theta> \<phi>\<guillemotright>\<guillemotright>)"
| AOT_subst_fun_def[AOT_substI]: "(\<And> \<phi> . AOT_model_equiv_def (\<Theta> \<phi>) (\<Psi> \<phi>)) \<Longrightarrow> AOT_subst_fun \<Psi> \<Longrightarrow> AOT_subst_fun \<Theta>"

instance proof
  fix \<psi> \<chi> :: "'a \<Rightarrow> 'b" and \<phi> :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> \<o>\<close>
  assume \<open>AOT_subst \<phi>\<close>
  moreover assume cond: \<open>AOT_subst_cond \<psi> \<chi>\<close>
  ultimately AOT_show \<open>\<^bold>\<turnstile>\<^sub>\<box> \<guillemotleft>\<phi> \<psi>\<guillemotright> \<equiv> \<guillemotleft>\<phi> \<chi>\<guillemotright>\<close>
  proof(induct)
    case (AOT_subst_fun_const \<psi>)
    then show ?case by (simp add: "oth-class-taut:3:a")
  next
  case (AOT_subst_fun_id \<Psi> x)
  then show ?case by (simp add: AOT_subst AOT_subst_cond_fun_def) 
  next
  case (AOT_subst_fun_all \<Psi> \<Theta>)
  AOT_have \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<Theta>{\<alpha>, \<guillemotleft>\<psi>\<guillemotright>} \<equiv> \<Theta>{\<alpha>, \<guillemotleft>\<chi>\<guillemotright>})\<close> for \<alpha>
    using AOT_subst_fun_all.hyps(3) AOT_subst_fun_all.prems RN by presburger
  thus ?case using AOT_subst[OF AOT_subst_fun_all(1)]
    by (simp add: RN "rule-sub-lem:1:d" AOT_subst_cond_fun_def AOT_subst_cond_\<o>_def)
  next
  case (AOT_subst_fun_not \<Psi>)
  then show ?case by (simp add: RN "rule-sub-lem:1:a")
  next
  case (AOT_subst_fun_imp \<Psi> \<Theta>)
  then show ?case 
    unfolding AOT_subst_cond_fun_def AOT_subst_cond_\<o>_def
    by (meson "\<equiv>E"(5) "oth-class-taut:4:c" "oth-class-taut:4:d" "vdash-properties:6")
  next
  case (AOT_subst_fun_lambda0 \<Theta>)
  then show ?case by (simp add: RN "rule-sub-lem:1:e")
  next
  case (AOT_subst_fun_act \<Theta>)
  then show ?case by (simp add: RN "rule-sub-lem:1:f")
  next
  case (AOT_subst_fun_box \<Theta>)
  then show ?case by (simp add: RN "rule-sub-lem:1:g")
  next
  case (AOT_subst_fun_def \<Theta> \<Psi>)
  then show ?case
    by (meson "df-rules-formulas[3]" "df-rules-formulas[4]" "\<equiv>I" "\<equiv>E"(5))
  qed
qed
end

method_setup AOT_defI =
\<open>Scan.lift (Scan.succeed (fn ctxt => (Method.CONTEXT_METHOD (fn thms => (Context_Tactic.CONTEXT_SUBGOAL (fn (trm,int) => 
Context_Tactic.CONTEXT_TACTIC (
let
fun findHeadConst (Const x) = SOME x
  | findHeadConst (A $ B) = findHeadConst A
  | findHeadConst _ = NONE
fun findDef (Const (\<^const_name>\<open>AOT_model_equiv_def\<close>, _) $ lhs $ rhs) = findHeadConst lhs
  | findDef (A $ B) = (case findDef A of SOME x => SOME x | _ => findDef B)
  | findDef (Abs (a,b,c)) = findDef c
  | findDef _ = NONE
val const_opt = (findDef trm)
val defs = case const_opt of SOME const => List.filter (fn thm => let
    val concl = Thm.concl_of thm
    val thmconst = (findDef concl)
    in case thmconst of SOME (c,_) => fst const = c | _ => false end) (AOT_Definitions.get ctxt)
    | _ => []
in
resolve_tac ctxt defs 1
end
)) 1)))))\<close>
\<open>Resolve AOT definitions\<close>

method AOT_subst_intro_helper = ((rule AOT_substI
      | AOT_defI
      | (simp only: AOT_subst_cond_\<o>_def AOT_subst_cond_fun_def; ((rule allI)+)?)))

method AOT_subst for \<psi>::"'a::AOT_subst" and \<chi>::"'a::AOT_subst" =
    (match conclusion in "[v \<Turnstile> \<guillemotleft>\<phi> \<psi>\<guillemotright>]" for \<phi> and v \<Rightarrow>
      \<open>match (\<phi>) in "\<lambda>a . ?p" \<Rightarrow> \<open>fail\<close> \<bar> "\<lambda>a . a" \<Rightarrow> \<open>fail\<close>
       \<bar> _ \<Rightarrow> \<open>rule AOT_subst[where \<phi>=\<phi> and \<psi>=\<psi> and \<chi>=\<chi>, THEN "\<equiv>E"(2)]
       ; (AOT_subst_intro_helper+)?\<close>\<close>)

method AOT_subst_rev for \<chi>::"'a::AOT_subst" and \<psi>::"'a::AOT_subst" =
    (match conclusion in "[v \<Turnstile> \<guillemotleft>\<phi> \<psi>\<guillemotright>]" for \<phi> and v \<Rightarrow>
      \<open>match (\<phi>) in "\<lambda>a . ?p" \<Rightarrow> \<open>fail\<close> \<bar> "\<lambda>a . a" \<Rightarrow> \<open>fail\<close>
       \<bar> _ \<Rightarrow> \<open>rule AOT_subst[where \<phi>=\<phi> and \<psi>=\<chi> and \<chi>=\<psi>, THEN "\<equiv>E"(1)]
       ; (AOT_subst_intro_helper+)?\<close>\<close>)

method AOT_subst_manual for \<phi>::"'a::AOT_subst \<Rightarrow> \<o>" =
    (rule AOT_subst[where \<phi>=\<phi>, THEN "\<equiv>E"(2)]; (AOT_subst_intro_helper+)?)

method AOT_subst_manual_rev for \<phi>::"'a::AOT_subst \<Rightarrow> \<o>" =
    (rule AOT_subst[where \<phi>=\<phi>, THEN "\<equiv>E"(1)]; (AOT_subst_intro_helper+)?)

method AOT_subst_using uses subst =
    (match subst in "[?w \<Turnstile> \<psi> \<equiv> \<chi>]" for \<psi> \<chi> \<Rightarrow> \<open>
       match conclusion in "[v \<Turnstile> \<guillemotleft>\<phi> \<psi>\<guillemotright>]" for \<phi> v \<Rightarrow> \<open>
         rule AOT_subst[where \<phi>=\<phi> and \<psi>=\<psi> and \<chi>=\<chi>, THEN "\<equiv>E"(2)]
         ; ((AOT_subst_intro_helper | (fact subst; fail))+)?\<close>\<close>)

method AOT_subst_using_rev uses subst =
    (match subst in "[?w \<Turnstile> \<psi> \<equiv> \<chi>]" for \<psi> \<chi> \<Rightarrow> \<open>
      match conclusion in "[v \<Turnstile> \<guillemotleft>\<phi> \<chi>\<guillemotright>]" for \<phi> v \<Rightarrow> \<open>
        rule AOT_subst[where \<phi>=\<phi> and \<psi>=\<psi> and \<chi>=\<chi>, THEN "\<equiv>E"(1)]
        ; ((AOT_subst_intro_helper | (fact subst; fail))+)?\<close>\<close>)

AOT_theorem "rule-sub-remark:1[1]": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> A!x \<equiv> \<not>\<diamond>E!x\<close> and \<open>\<not>A!x\<close> shows \<open>\<not>\<not>\<diamond>E!x\<close>
  by (AOT_subst_rev "\<guillemotleft>A!x\<guillemotright>" "\<guillemotleft>\<not>\<diamond>E!x\<guillemotright>") (auto simp: assms)

AOT_theorem "rule-sub-remark:1[2]": assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> A!x \<equiv> \<not>\<diamond>E!x\<close> and  \<open>\<not>\<not>\<diamond>E!x\<close> shows \<open>\<not>A!x\<close>
  by (AOT_subst "\<guillemotleft>A!x\<guillemotright>" "\<guillemotleft>\<not>\<diamond>E!x\<guillemotright>") (auto simp: assms)

AOT_theorem "rule-sub-remark:2[1]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> [R]xy \<equiv> ([R]xy & ([Q]a \<or> \<not>[Q]a))\<close> and \<open>p \<rightarrow> [R]xy\<close> shows \<open>p \<rightarrow> [R]xy & ([Q]a \<or> \<not>[Q]a)\<close>
  by (AOT_subst_using_rev subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:2[2]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> [R]xy \<equiv> ([R]xy & ([Q]a \<or> \<not>[Q]a))\<close> and \<open>p \<rightarrow> [R]xy & ([Q]a \<or> \<not>[Q]a)\<close> shows \<open>p \<rightarrow> [R]xy\<close>
  by (AOT_subst_using subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:3[1]":
  assumes \<open>for arbitrary x: \<^bold>\<turnstile>\<^sub>\<box> A!x \<equiv> \<not>\<diamond>E!x\<close>
      and \<open>\<exists>x A!x\<close>
    shows \<open>\<exists>x \<not>\<diamond>E!x\<close>
  by (AOT_subst_rev "\<lambda>\<kappa>. \<guillemotleft>A!\<kappa>\<guillemotright>" "\<lambda>\<kappa>. \<guillemotleft>\<not>\<diamond>E!\<kappa>\<guillemotright>") (auto simp: assms)

AOT_theorem "rule-sub-remark:3[2]":
  assumes \<open>for arbitrary x: \<^bold>\<turnstile>\<^sub>\<box> A!x \<equiv> \<not>\<diamond>E!x\<close>
      and \<open>\<exists>x \<not>\<diamond>E!x\<close>
    shows \<open>\<exists>x A!x\<close>
  by (AOT_subst "\<lambda>\<kappa>. \<guillemotleft>A!\<kappa>\<guillemotright>" "\<lambda>\<kappa>. \<guillemotleft>\<not>\<diamond>E!\<kappa>\<guillemotright>") (auto simp: assms)

AOT_theorem "rule-sub-remark:4[1]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<not>\<not>[P]x \<equiv> [P]x\<close> and \<open>\<^bold>\<A>\<not>\<not>[P]x\<close> shows \<open>\<^bold>\<A>[P]x\<close>
  by (AOT_subst_using_rev subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:4[2]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<not>\<not>[P]x \<equiv> [P]x\<close> and \<open>\<^bold>\<A>[P]x\<close> shows \<open>\<^bold>\<A>\<not>\<not>[P]x\<close>
  by (AOT_subst_using subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:5[1]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> (\<phi> \<rightarrow> \<psi>) \<equiv> (\<not>\<psi> \<rightarrow> \<not>\<phi>)\<close> and \<open>\<box>(\<phi> \<rightarrow> \<psi>)\<close> shows \<open>\<box>(\<not>\<psi> \<rightarrow> \<not>\<phi>)\<close>
  by (AOT_subst_using_rev subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:5[2]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> (\<phi> \<rightarrow> \<psi>) \<equiv> (\<not>\<psi> \<rightarrow> \<not>\<phi>)\<close> and \<open>\<box>(\<not>\<psi> \<rightarrow> \<not>\<phi>)\<close> shows \<open>\<box>(\<phi> \<rightarrow> \<psi>)\<close> 
  by (AOT_subst_using subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:6[1]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<psi> \<equiv> \<chi>\<close> and \<open>\<box>(\<phi> \<rightarrow> \<psi>)\<close> shows \<open>\<box>(\<phi> \<rightarrow> \<chi>)\<close> 
  by (AOT_subst_using_rev subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:6[2]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<psi> \<equiv> \<chi>\<close> and \<open>\<box>(\<phi> \<rightarrow> \<chi>)\<close> shows \<open>\<box>(\<phi> \<rightarrow> \<psi>)\<close>
  by (AOT_subst_using subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:7[1]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<not>\<not>\<phi>\<close> and \<open>\<box>(\<phi> \<rightarrow> \<phi>)\<close> shows \<open>\<box>(\<not>\<not>\<phi> \<rightarrow> \<phi>)\<close> 
  by (AOT_subst_using_rev subst: assms(1)) (simp add: assms(2))

AOT_theorem "rule-sub-remark:7[2]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<not>\<not>\<phi>\<close> and \<open>\<box>(\<not>\<not>\<phi> \<rightarrow> \<phi>)\<close> shows  \<open>\<box>(\<phi> \<rightarrow> \<phi>)\<close>
  by (AOT_subst_using subst: assms(1)) (simp add: assms(2))

AOT_theorem "KBasic2:1": \<open>\<box>\<not>\<phi> \<equiv> \<not>\<diamond>\<phi>\<close>
  by (meson AOT_dia "contraposition:2" "Hypothetical Syllogism" "df-rules-formulas[3]"
            "df-rules-formulas[4]" "\<equiv>I" "useful-tautologies:1")

AOT_theorem "KBasic2:2": \<open>\<diamond>(\<phi> \<or> \<psi>) \<equiv> (\<diamond>\<phi> \<or> \<diamond>\<psi>)\<close>
proof -
  AOT_have \<open>\<diamond>(\<phi> \<or> \<psi>) \<equiv> \<diamond>\<not>(\<not>\<phi> & \<not>\<psi>)\<close>
    by (simp add: "RE\<diamond>" "oth-class-taut:5:b")
  also AOT_have \<open>\<dots> \<equiv> \<not>\<box>(\<not>\<phi> & \<not>\<psi>)\<close>
    using "KBasic:11" "\<equiv>E"(6) "oth-class-taut:3:a" by blast
  also AOT_have \<open>\<dots> \<equiv> \<not>(\<box>\<not>\<phi> & \<box>\<not>\<psi>)\<close>
    using "KBasic:3" "\<equiv>E"(1) "oth-class-taut:4:b" by blast
  also AOT_have \<open>\<dots> \<equiv> \<not>(\<not>\<diamond>\<phi> & \<not>\<diamond>\<psi>)\<close>
    apply (AOT_subst_rev "\<guillemotleft>\<box>\<not>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<diamond>\<phi>\<guillemotright>")
    apply (simp add: "KBasic2:1")
    apply (AOT_subst_rev "\<guillemotleft>\<box>\<not>\<psi>\<guillemotright>" "\<guillemotleft>\<not>\<diamond>\<psi>\<guillemotright>")
    by (auto simp: "KBasic2:1" "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<not>\<not>(\<diamond>\<phi> \<or> \<diamond>\<psi>)\<close>
    using "\<equiv>E"(6) "oth-class-taut:3:b" "oth-class-taut:5:b" by blast
  also AOT_have \<open>\<dots> \<equiv> \<diamond>\<phi> \<or> \<diamond>\<psi>\<close>
    by (simp add: "\<equiv>I" "useful-tautologies:1" "useful-tautologies:2")
  finally show ?thesis .
qed

AOT_theorem "KBasic2:3": \<open>\<diamond>(\<phi> & \<psi>) \<rightarrow> (\<diamond>\<phi> & \<diamond>\<psi>)\<close>
  by (metis "RM\<diamond>" "&I" "Conjunction Simplification"(1) "Conjunction Simplification"(2) "deduction-theorem" "modus-tollens:1" "reductio-aa:1")

AOT_theorem "KBasic2:4": \<open>\<diamond>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<box>\<phi> \<rightarrow> \<diamond>\<psi>)\<close>
proof -
  AOT_have \<open>\<diamond>(\<phi> \<rightarrow> \<psi>) \<equiv> \<diamond>(\<not>\<phi> \<or> \<psi>)\<close>
    by (AOT_subst "\<guillemotleft>\<phi> \<rightarrow> \<psi>\<guillemotright>" "\<guillemotleft>\<not>\<phi> \<or> \<psi>\<guillemotright>")
       (auto simp: "oth-class-taut:1:c" "oth-class-taut:3:a")
  also AOT_have \<open>... \<equiv> \<diamond>\<not>\<phi> \<or> \<diamond>\<psi>\<close>
    by (simp add: "KBasic2:2")
  also AOT_have \<open>... \<equiv> \<not>\<box>\<phi> \<or> \<diamond>\<psi>\<close>
    by (AOT_subst "\<guillemotleft>\<not>\<box>\<phi>\<guillemotright>" "\<guillemotleft>\<diamond>\<not>\<phi>\<guillemotright>")
       (auto simp: "KBasic:11" "oth-class-taut:3:a")
  also AOT_have \<open>... \<equiv> \<box>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
    using "\<equiv>E"(6) "oth-class-taut:1:c" "oth-class-taut:3:a" by blast
  finally show ?thesis .
qed

AOT_theorem "KBasic2:5": \<open>\<diamond>\<diamond>\<phi> \<equiv> \<not>\<box>\<box>\<not>\<phi>\<close>
  apply (AOT_subst "\<guillemotleft>\<diamond>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<box>\<not>\<phi>\<guillemotright>")
   apply (simp add: AOT_dia "\<equiv>Df")
  apply (AOT_subst "\<guillemotleft>\<diamond>\<not>\<box>\<not>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<box>\<not>\<not>\<box>\<not>\<phi>\<guillemotright>")
   apply (simp add: AOT_dia "\<equiv>Df")
  apply (AOT_subst_rev "\<guillemotleft>\<box>\<not>\<phi>\<guillemotright>"  "\<guillemotleft>\<not>\<not>\<box>\<not>\<phi>\<guillemotright>")
   apply (simp add: "oth-class-taut:3:b")
  by (simp add: "oth-class-taut:3:a")


AOT_theorem "KBasic2:6": \<open>\<box>(\<phi> \<or> \<psi>) \<rightarrow> (\<box>\<phi> \<or> \<diamond>\<psi>)\<close>
proof(rule "\<rightarrow>I"; rule "raa-cor:1")
  AOT_assume \<open>\<box>(\<phi> \<or> \<psi>)\<close>
  AOT_hence \<open>\<box>(\<not>\<phi> \<rightarrow> \<psi>)\<close>
    apply - apply (AOT_subst_rev "\<guillemotleft>\<phi> \<or> \<psi>\<guillemotright>" "\<guillemotleft>\<not>\<phi> \<rightarrow> \<psi>\<guillemotright>")
    by (simp add: AOT_disj "\<equiv>Df")
  AOT_hence 1: \<open>\<diamond>\<not>\<phi> \<rightarrow> \<diamond>\<psi>\<close> using "KBasic:13" "vdash-properties:10" by blast
  AOT_assume \<open>\<not>(\<box>\<phi> \<or> \<diamond>\<psi>)\<close>
  AOT_hence \<open>\<not>\<box>\<phi>\<close> and \<open>\<not>\<diamond>\<psi>\<close> using "&E" "\<equiv>E"(1) "oth-class-taut:5:d" by blast+
  AOT_thus \<open>\<diamond>\<psi> & \<not>\<diamond>\<psi>\<close> using "&I"(1) 1[THEN "\<rightarrow>E"] "KBasic:11" "\<equiv>E"(4) "raa-cor:3" by blast
qed

AOT_theorem "KBasic2:7": \<open>(\<box>(\<phi> \<or> \<psi>) & \<diamond>\<not>\<phi>) \<rightarrow> \<diamond>\<psi>\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>\<box>(\<phi> \<or> \<psi>)\<close>
  AOT_hence 1: \<open>\<box>\<phi> \<or> \<diamond>\<psi>\<close>
    using "KBasic2:6" "\<or>I"(2) "\<or>E"(1) by blast
  AOT_assume \<open>\<diamond>\<not>\<phi>\<close>
  AOT_hence \<open>\<not>\<box>\<phi>\<close> using "KBasic:11" "\<equiv>E"(2) by blast
  AOT_thus \<open>\<diamond>\<psi>\<close> using 1 "\<or>E"(2) by blast
qed

AOT_theorem "T-S5-fund:1": \<open>\<phi> \<rightarrow> \<diamond>\<phi>\<close>
  by (meson "\<equiv>\<^sub>d\<^sub>fI" AOT_dia "contraposition:2" "Hypothetical Syllogism" "deduction-theorem" "qml:2"[axiom_inst])
lemmas "T\<diamond>" = "T-S5-fund:1"

AOT_theorem "T-S5-fund:2": \<open>\<diamond>\<box>\<phi> \<rightarrow> \<box>\<phi>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<diamond>\<box>\<phi>\<close>
  AOT_hence \<open>\<not>\<box>\<diamond>\<not>\<phi>\<close>
    using "KBasic:14" "\<equiv>E"(4) "raa-cor:3" by blast
  moreover AOT_have \<open>\<diamond>\<not>\<phi> \<rightarrow> \<box>\<diamond>\<not>\<phi>\<close>
    by (fact "qml:3"[axiom_inst])
  ultimately AOT_have \<open>\<not>\<diamond>\<not>\<phi>\<close>
    using "modus-tollens:1" by blast
  AOT_thus \<open>\<box>\<phi>\<close> using "KBasic:12" "\<equiv>E"(2) by blast
qed
lemmas "5\<diamond>" = "T-S5-fund:2"

(* Also interestingly none of these have proofs in PLM. *)
AOT_theorem "Act-Sub:1": \<open>\<^bold>\<A>\<phi> \<equiv> \<not>\<^bold>\<A>\<not>\<phi>\<close>
  by (AOT_subst "\<guillemotleft>\<^bold>\<A>\<not>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<^bold>\<A>\<phi>\<guillemotright>")
     (auto simp: "logic-actual-nec:1"[axiom_inst] "oth-class-taut:3:b")

AOT_theorem "Act-Sub:2": \<open>\<diamond>\<phi> \<equiv> \<^bold>\<A>\<diamond>\<phi>\<close>
  apply (AOT_subst "\<guillemotleft>\<diamond>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<box>\<not>\<phi>\<guillemotright>")
   apply (simp add: AOT_dia "\<equiv>Df")
  by (metis "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "\<equiv>E"(2) "\<equiv>E"(3)
            "logic-actual-nec:1"[axiom_inst] "qml-act:2"[axiom_inst])

AOT_theorem "Act-Sub:3": \<open>\<^bold>\<A>\<phi> \<rightarrow> \<diamond>\<phi>\<close>
  apply (AOT_subst "\<guillemotleft>\<diamond>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<box>\<not>\<phi>\<guillemotright>")
   apply (simp add: AOT_dia "\<equiv>Df")
  by (metis "Act-Sub:1" "deduction-theorem" "\<equiv>E"(4) "nec-imp-act" "reductio-aa:2" "vdash-properties:6")


AOT_theorem "Act-Sub:4": \<open>\<^bold>\<A>\<phi> \<equiv> \<diamond>\<^bold>\<A>\<phi>\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>\<phi>\<close>
  AOT_thus \<open>\<diamond>\<^bold>\<A>\<phi>\<close> using "T\<diamond>" "vdash-properties:10" by blast
next
  AOT_assume \<open>\<diamond>\<^bold>\<A>\<phi>\<close>
  AOT_hence \<open>\<not>\<box>\<not>\<^bold>\<A>\<phi>\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" AOT_dia by blast
  AOT_hence \<open>\<not>\<box>\<^bold>\<A>\<not>\<phi>\<close>
    apply - apply (AOT_subst "\<guillemotleft>\<^bold>\<A>\<not>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<^bold>\<A>\<phi>\<guillemotright>")
    by (simp add: "logic-actual-nec:1"[axiom_inst])
  AOT_thus \<open>\<^bold>\<A>\<phi>\<close>
      using "Act-Basic:1" "Act-Basic:6" "\<or>E"(3) "\<equiv>E"(4) "reductio-aa:1" by blast
qed

AOT_theorem "Act-Sub:5": \<open>\<diamond>\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>\<diamond>\<phi>\<close>
  by (metis "Act-Sub:2" "Act-Sub:3" "Act-Sub:4" "deduction-theorem" "\<equiv>E"(1) "\<equiv>E"(2) "vdash-properties:6")

AOT_theorem "S5Basic:1": \<open>\<diamond>\<phi> \<equiv> \<box>\<diamond>\<phi>\<close>
  by (simp add: "\<equiv>I" "qml:2" "qml:3" "vdash-properties:1[2]")

AOT_theorem "S5Basic:2": \<open>\<box>\<phi> \<equiv> \<diamond>\<box>\<phi>\<close>
  by (simp add: "T\<diamond>" "5\<diamond>" "\<equiv>I")

AOT_theorem "S5Basic:3": \<open>\<phi> \<rightarrow> \<box>\<diamond>\<phi>\<close>
  using "T\<diamond>" "Hypothetical Syllogism" "qml:3" "vdash-properties:1[2]" by blast
lemmas "B" = "S5Basic:3"

AOT_theorem "S5Basic:4": \<open>\<diamond>\<box>\<phi> \<rightarrow> \<phi>\<close>
  using "5\<diamond>" "Hypothetical Syllogism" "qml:2" "vdash-properties:1[2]" by blast
lemmas "B\<diamond>" = "S5Basic:4"

AOT_theorem "S5Basic:5": \<open>\<box>\<phi> \<rightarrow> \<box>\<box>\<phi>\<close>
  using "RM:1" "S5Basic:3" "5\<diamond>" "Hypothetical Syllogism" by blast
lemmas "4" = "S5Basic:5"

AOT_theorem "S5Basic:6": \<open>\<box>\<phi> \<equiv> \<box>\<box>\<phi>\<close>
  by (simp add: "S5Basic:5" "\<equiv>I" "qml:2"[axiom_inst])

AOT_theorem "S5Basic:7": \<open>\<diamond>\<diamond>\<phi> \<rightarrow> \<diamond>\<phi>\<close>
  apply (AOT_subst "\<guillemotleft>\<diamond>\<diamond>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<box>\<not>\<diamond>\<phi>\<guillemotright>")
   apply (simp add: AOT_dia "\<equiv>Df")
  apply (AOT_subst "\<guillemotleft>\<diamond>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<box>\<not>\<phi>\<guillemotright>")
   apply (simp add: AOT_dia "\<equiv>Df")
  apply (AOT_subst_rev "\<guillemotleft>\<box>\<not>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<not>\<box>\<not>\<phi>\<guillemotright>")
   apply (simp add: "oth-class-taut:3:b")
  apply (AOT_subst_rev "\<guillemotleft>\<box>\<not>\<phi>\<guillemotright>" "\<guillemotleft>\<box>\<box>\<not>\<phi>\<guillemotright>")
   apply (simp add: "S5Basic:6")
  by (simp add: "if-p-then-p")

lemmas "4\<diamond>" = "S5Basic:7"

AOT_theorem "S5Basic:8": \<open>\<diamond>\<diamond>\<phi> \<equiv> \<diamond>\<phi>\<close>
  by (simp add: "S5Basic:7" "T\<diamond>" "\<equiv>I")

AOT_theorem "S5Basic:9": \<open>\<box>(\<phi> \<or> \<box>\<psi>) \<equiv> (\<box>\<phi> \<or> \<box>\<psi>)\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I")
  using "KBasic2:6" "5\<diamond>" "\<or>I"(3) "if-p-then-p" "vdash-properties:10" apply blast
  by (meson "KBasic:15" "S5Basic:5" "\<or>I"(3) "\<or>E"(1) "Disjunction Addition"(1) "con-dis-taut:7"
            "intro-elim:1" "Commutativity of \<or>")

AOT_theorem "S5Basic:10": \<open>\<box>(\<phi> \<or> \<diamond>\<psi>) \<equiv> (\<box>\<phi> \<or> \<diamond>\<psi>)\<close>
(* Note: nicely this proof is entirely sledgehammer generated *)
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<box>(\<phi> \<or> \<diamond>\<psi>)\<close>
  AOT_hence \<open>\<box>\<phi> \<or> \<diamond>\<diamond>\<psi>\<close>
    by (meson "KBasic2:6" "\<or>I"(2) "\<or>E"(1))
  AOT_thus \<open>\<box>\<phi> \<or> \<diamond>\<psi>\<close>
    by (meson "S5Basic:4" "S5Basic:5" "S5Basic:7" "T\<diamond>" "\<or>I"(3))
next
  AOT_assume \<open>\<box>\<phi> \<or> \<diamond>\<psi>\<close>
  AOT_hence \<open>\<box>\<phi> \<or> \<box>\<diamond>\<psi>\<close>
    by (meson "S5Basic:1" "S5Basic:4" "S5Basic:6" "T\<diamond>" "5\<diamond>" "\<or>I"(3) "intro-elim:1")
  AOT_thus \<open>\<box>(\<phi> \<or> \<diamond>\<psi>)\<close>
    by (meson "KBasic:15" "\<or>I"(3) "\<or>E"(1) "Disjunction Addition"(1) "Disjunction Addition"(2))
qed

AOT_theorem "S5Basic:11": \<open>\<diamond>(\<phi> & \<diamond>\<psi>) \<equiv> (\<diamond>\<phi> & \<diamond>\<psi>)\<close>
proof -
  AOT_have \<open>\<diamond>(\<phi> & \<diamond>\<psi>) \<equiv> \<diamond>\<not>(\<not>\<phi> \<or> \<not>\<diamond>\<psi>)\<close>
    by (AOT_subst "\<guillemotleft>\<phi> & \<diamond>\<psi>\<guillemotright>" "\<guillemotleft>\<not>(\<not>\<phi> \<or> \<not>\<diamond>\<psi>)\<guillemotright>")
       (auto simp: "oth-class-taut:5:a" "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<diamond>\<not>(\<not>\<phi> \<or> \<box>\<not>\<psi>)\<close>
    by (AOT_subst "\<guillemotleft>\<box>\<not>\<psi>\<guillemotright>" "\<guillemotleft>\<not>\<diamond>\<psi>\<guillemotright>")
       (auto simp: "KBasic2:1" "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<not>\<box>(\<not>\<phi> \<or> \<box>\<not>\<psi>)\<close>
    using "KBasic:11" "\<equiv>E"(6) "oth-class-taut:3:a" by blast
  also AOT_have \<open>\<dots> \<equiv> \<not>(\<box>\<not>\<phi> \<or> \<box>\<not>\<psi>)\<close>
    using "S5Basic:9" "\<equiv>E"(1) "oth-class-taut:4:b" by blast
  also AOT_have \<open>\<dots> \<equiv> \<not>(\<not>\<diamond>\<phi> \<or> \<not>\<diamond>\<psi>)\<close>
    apply (AOT_subst "\<guillemotleft>\<box>\<not>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<diamond>\<phi>\<guillemotright>")
     apply (simp add: "KBasic2:1")
    apply (AOT_subst "\<guillemotleft>\<box>\<not>\<psi>\<guillemotright>" "\<guillemotleft>\<not>\<diamond>\<psi>\<guillemotright>")
    by (auto simp: "KBasic2:1" "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<diamond>\<phi> & \<diamond>\<psi>\<close>
    using "\<equiv>E"(6) "oth-class-taut:3:a" "oth-class-taut:5:a" by blast
  finally show ?thesis .
qed

AOT_theorem "S5Basic:12": \<open>\<diamond>(\<phi> & \<box>\<psi>) \<equiv> (\<diamond>\<phi> & \<box>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<diamond>(\<phi> & \<box>\<psi>)\<close>
  AOT_hence \<open>\<diamond>\<phi> & \<diamond>\<box>\<psi>\<close>
    using "KBasic2:3" "vdash-properties:6" by blast
  AOT_thus \<open>\<diamond>\<phi> & \<box>\<psi>\<close>
    using "5\<diamond>" "&I" "&E"(1) "&E"(2) "vdash-properties:6" by blast
next
  AOT_assume \<open>\<diamond>\<phi> & \<box>\<psi>\<close>
  moreover AOT_have \<open>(\<box>\<box>\<psi> & \<diamond>\<phi>) \<rightarrow> \<diamond>(\<phi> & \<box>\<psi>)\<close>
    by (AOT_subst "\<guillemotleft>\<phi> & \<box>\<psi>\<guillemotright>" "\<guillemotleft>\<box>\<psi> & \<phi>\<guillemotright>")
       (auto simp: "Commutativity of &" "KBasic:16")
  ultimately AOT_show \<open>\<diamond>(\<phi> & \<box>\<psi>)\<close>
    by (metis "S5Basic:5" "&I" "Conjunction Simplification"(1) "Conjunction Simplification"(2) "vdash-properties:6")
qed


AOT_theorem "S5Basic:13": \<open>\<box>(\<phi> \<rightarrow> \<box>\<psi>) \<equiv> \<box>(\<diamond>\<phi> \<rightarrow> \<psi>)\<close>
proof (rule "\<equiv>I")
  AOT_modally_strict {
    AOT_have \<open>\<box>(\<phi> \<rightarrow> \<box>\<psi>) \<rightarrow> (\<diamond>\<phi> \<rightarrow> \<psi>)\<close>
      by (meson "KBasic:13" "S5Basic:4" "Hypothetical Syllogism" "deduction-theorem")
  }
  AOT_hence \<open>\<box>\<box>(\<phi> \<rightarrow> \<box>\<psi>) \<rightarrow> \<box>(\<diamond>\<phi> \<rightarrow> \<psi>)\<close>
    by (rule RM)
  AOT_thus  \<open>\<box>(\<phi> \<rightarrow> \<box>\<psi>) \<rightarrow> \<box>(\<diamond>\<phi> \<rightarrow> \<psi>)\<close>
    using "S5Basic:5" "Hypothetical Syllogism" by blast
next
  AOT_modally_strict {
    AOT_have \<open>\<box>(\<diamond>\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<box>\<psi>)\<close>
      by (meson "S5Basic:3" "Hypothetical Syllogism" "deduction-theorem" "qml:1" "vdash-properties:1[2]")
  }
  AOT_hence  \<open>\<box>\<box>(\<diamond>\<phi> \<rightarrow> \<psi>) \<rightarrow> \<box>(\<phi> \<rightarrow> \<box>\<psi>)\<close>
    by (rule RM)
  AOT_thus \<open>\<box>(\<diamond>\<phi> \<rightarrow> \<psi>) \<rightarrow> \<box>(\<phi> \<rightarrow> \<box>\<psi>)\<close>
    using "S5Basic:5" "Hypothetical Syllogism" by blast
qed

AOT_theorem derived_S5_rules_1:
  assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<box>\<psi>\<close>
proof -
  AOT_have \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<diamond>\<phi> \<rightarrow> \<box>\<psi>\<close>
    using assms by (rule "RM:1[prem]")
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<box>\<psi>\<close>
    using "S5Basic:3" "Hypothetical Syllogism" by blast
qed

AOT_theorem derived_S5_rules_2:
  assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<box>\<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<psi>\<close>
proof -
  AOT_have \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<box>\<psi>\<close>
    using assms by (rule "RM:2[prem]")
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<psi>\<close>
    using "B\<diamond>" "Hypothetical Syllogism" by blast
qed
AOT_theorem BFs_1: \<open>\<forall>\<alpha> \<box>\<phi>{\<alpha>} \<rightarrow> \<box>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
proof -
  AOT_modally_strict {
    AOT_modally_strict {
      AOT_have \<open>\<forall>\<alpha> \<box>\<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>}\<close> for \<alpha> by (fact AOT)
    }
    AOT_hence \<open>\<diamond>\<forall>\<alpha> \<box>\<phi>{\<alpha>} \<rightarrow> \<diamond>\<box>\<phi>{\<alpha>}\<close> for \<alpha> by (rule "RM\<diamond>")
    AOT_hence \<open>\<diamond>\<forall>\<alpha> \<box>\<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<phi>{\<alpha>}\<close>
      using "B\<diamond>" "\<forall>I" "\<rightarrow>E" "\<rightarrow>I" by metis
  }
  thus ?thesis using derived_S5_rules_1 by blast
qed
lemmas "BF" = BFs_1

AOT_theorem BFs_2: \<open>\<box>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<box>\<phi>{\<alpha>}\<close>
proof -
  AOT_have \<open>\<box>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>}\<close> for \<alpha> using RM "cqt-orig:3" by metis
  thus ?thesis using  "cqt-orig:2"[THEN "\<rightarrow>E"] "\<forall>I" by metis
qed
lemmas "CBF" = BFs_2

AOT_theorem BFs_3: \<open>\<diamond>\<exists>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<exists>\<alpha> \<diamond>\<phi>{\<alpha>}\<close>
proof(rule "\<rightarrow>I")
  AOT_modally_strict {
    AOT_have \<open>\<box>\<forall>\<alpha> \<not>\<phi>{\<alpha>} \<equiv> \<forall>\<alpha> \<box>\<not>\<phi>{\<alpha>}\<close>
      using BF CBF "\<equiv>I" by blast
  } note \<theta> = this

  AOT_assume \<open>\<diamond>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  AOT_hence \<open>\<not>\<box>\<not>(\<exists>\<alpha> \<phi>{\<alpha>})\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" AOT_dia by blast
  AOT_hence \<open>\<not>\<box>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
    apply - apply (AOT_subst "\<guillemotleft>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<guillemotright>" "\<guillemotleft>\<not>(\<exists>\<alpha> \<phi>{\<alpha>})\<guillemotright>")
    using "\<equiv>\<^sub>d\<^sub>fI" AOT_equiv AOT_exists "&I" "contraposition:2" "cqt-further:4"
          "df-rules-formulas[1]" "vdash-properties:1[2]" by blast
  AOT_hence \<open>\<not>\<forall>\<alpha> \<box>\<not>\<phi>{\<alpha>}\<close>
    apply - apply (AOT_subst_using_rev subst: \<theta>)
    using \<theta> by blast
  AOT_hence \<open>\<not>\<forall>\<alpha> \<not>\<not>\<box>\<not>\<phi>{\<alpha>}\<close>
    apply - apply (AOT_subst_rev "\<lambda> \<tau>. \<guillemotleft>\<box>\<not>\<phi>{\<tau>}\<guillemotright>"  "\<lambda> \<tau>. \<guillemotleft>\<not>\<not>\<box>\<not>\<phi>{\<tau>}\<guillemotright>")
    by (simp add: "oth-class-taut:3:b")
  AOT_hence 0: \<open>\<exists>\<alpha> \<not>\<box>\<not>\<phi>{\<alpha>}\<close>
    by (rule AOT_exists[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_show \<open>\<exists>\<alpha> \<diamond>\<phi>{\<alpha>}\<close>
    apply (AOT_subst "\<lambda> \<tau> . \<guillemotleft>\<diamond>\<phi>{\<tau>}\<guillemotright>" "\<lambda> \<tau> . \<guillemotleft>\<not>\<box>\<not>\<phi>{\<tau>}\<guillemotright>")
     apply (simp add: AOT_dia "\<equiv>Df")
    using 0 by blast
qed
lemmas "BF\<diamond>" = "BFs_3"

AOT_theorem BFs_4: \<open>\<exists>\<alpha> \<diamond>\<phi>{\<alpha>} \<rightarrow> \<diamond>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>\<alpha> \<diamond>\<phi>{\<alpha>}\<close>
  AOT_hence \<open>\<not>\<forall>\<alpha> \<not>\<diamond>\<phi>{\<alpha>}\<close>
    using AOT_exists[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence \<open>\<not>\<forall>\<alpha> \<box>\<not>\<phi>{\<alpha>}\<close>
    apply - apply (AOT_subst "\<lambda> \<tau> . \<guillemotleft>\<box>\<not>\<phi>{\<tau>}\<guillemotright>" "\<lambda> \<tau> . \<guillemotleft>\<not>\<diamond>\<phi>{\<tau>}\<guillemotright>")
    by (simp add: "KBasic2:1")
  moreover AOT_have \<open>\<forall>\<alpha> \<box>\<not>\<phi>{\<alpha>} \<equiv> \<box>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
    using "\<equiv>I" BFs_1 BFs_2 by metis
  ultimately AOT_have 1: \<open>\<not>\<box>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
    using "\<equiv>E"(3) by blast
  AOT_show \<open>\<diamond>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
    apply (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    apply (AOT_subst "\<guillemotleft>\<exists>\<alpha> \<phi>{\<alpha>}\<guillemotright>" "\<guillemotleft>\<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<guillemotright>")
     apply (simp add: AOT_exists "\<equiv>Df")
    apply (AOT_subst "\<guillemotleft>\<not>\<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<guillemotright>" "\<guillemotleft>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<guillemotright>")
    by (auto simp: 1 "\<equiv>I" "useful-tautologies:1" "useful-tautologies:2")
qed
lemmas "CBF\<diamond>" = BFs_4

AOT_theorem sign_S5_thm_1: \<open>\<exists>\<alpha> \<box>\<phi>{\<alpha>} \<rightarrow> \<box>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>\<alpha> \<box>\<phi>{\<alpha>}\<close>
  then AOT_obtain \<alpha> where \<open>\<box>\<phi>{\<alpha>}\<close> using "\<exists>E" by metis
  moreover AOT_have \<open>\<box>\<alpha>\<down>\<close>
    by (simp add: "ex:1:a" "rule-ui:2[const_var]" RN)
  moreover AOT_have \<open>\<box>\<phi>{\<tau>}, \<box>\<tau>\<down> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<exists>\<alpha> \<phi>{\<alpha>}\<close> for \<tau>
  proof -
    AOT_have \<open>\<phi>{\<tau>}, \<tau>\<down> \<^bold>\<turnstile>\<^sub>\<box> \<exists>\<alpha> \<phi>{\<alpha>}\<close> using "existential:1" by blast
    AOT_thus \<open>\<box>\<phi>{\<tau>}, \<box>\<tau>\<down> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
      using "RN[prem]"[where \<Gamma>="{\<phi> \<tau>, \<guillemotleft>\<tau>\<down>\<guillemotright>}", simplified] by blast
  qed
  ultimately AOT_show \<open>\<box>\<exists>\<alpha> \<phi>{\<alpha>}\<close> by blast
qed

lemmas "Buridan" = sign_S5_thm_1

AOT_theorem sign_S5_thm_2: \<open>\<diamond>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<diamond>\<phi>{\<alpha>}\<close>
proof -
  AOT_have \<open>\<forall>\<alpha> (\<diamond>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<diamond>\<phi>{\<alpha>})\<close>
    by (simp add: "RM\<diamond>" "cqt-orig:3" "\<forall>I")
  AOT_thus \<open>\<diamond>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<diamond>\<phi>{\<alpha>}\<close>
    using "\<forall>E"(4) "\<forall>I" "\<rightarrow>E" "\<rightarrow>I" by metis
qed

lemmas "Buridan\<diamond>" = sign_S5_thm_2

AOT_theorem sign_S5_thm_3: \<open>\<diamond>\<exists>\<alpha> (\<phi>{\<alpha>} & \<psi>{\<alpha>}) \<rightarrow> \<diamond>(\<exists>\<alpha> \<phi>{\<alpha>} & \<exists>\<alpha> \<psi>{\<alpha>})\<close>
  apply (rule "RM:2")
  by (metis (no_types, lifting) "instantiation" "&I" "&E"(1)
                                "&E"(2) "deduction-theorem" "existential:2[const_var]")

AOT_theorem sign_S5_thm_4: \<open>\<diamond>\<exists>\<alpha> (\<phi>{\<alpha>} & \<psi>{\<alpha>}) \<rightarrow> \<diamond>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  apply (rule "RM:2")
  by (meson "instantiation" "&E"(1) "deduction-theorem" "existential:2[const_var]")

AOT_theorem sign_S5_thm_5: \<open>(\<box>\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<box>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})) \<rightarrow> \<box>\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})\<close>
proof -
  {
    fix \<phi>' \<psi>' \<chi>'
    AOT_assume \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>' & \<psi>' \<rightarrow> \<chi>'\<close>
    AOT_hence \<open>\<box>\<phi>' & \<box>\<psi>' \<rightarrow> \<box>\<chi>'\<close>
      using "RN[prem]"[where \<Gamma>="{\<phi>', \<psi>'}"] apply simp
      using "&E" "&I" "\<rightarrow>E" "\<rightarrow>I" by metis
  } note R = this
  show ?thesis by (rule R; fact AOT)
qed

AOT_theorem sign_S5_thm_6: \<open>(\<box>\<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) & \<box>\<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})) \<rightarrow> \<box>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
proof -
  {
    fix \<phi>' \<psi>' \<chi>'
    AOT_assume \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>' & \<psi>' \<rightarrow> \<chi>'\<close>
    AOT_hence \<open>\<box>\<phi>' & \<box>\<psi>' \<rightarrow> \<box>\<chi>'\<close>
      using "RN[prem]"[where \<Gamma>="{\<phi>', \<psi>'}"] apply simp
      using "&E" "&I" "\<rightarrow>E" "\<rightarrow>I" by metis
  } note R = this
  show ?thesis by (rule R; fact AOT)
qed

AOT_theorem "exist-nec2:1": \<open>\<diamond>\<tau>\<down> \<rightarrow> \<tau>\<down>\<close>
  using "B\<diamond>" "RM\<diamond>" "Hypothetical Syllogism" "exist-nec" by blast

AOT_theorem exists_nec2_2: \<open>\<diamond>\<tau>\<down> \<equiv> \<box>\<tau>\<down>\<close>
  by (meson "Act-Sub:3" "Hypothetical Syllogism" "exist-nec" "exist-nec2:1" "\<equiv>I" "nec-imp-act")

AOT_theorem exists_nec2_3: \<open>\<not>\<tau>\<down> \<rightarrow> \<box>\<not>\<tau>\<down>\<close>
  using "KBasic2:1" "deduction-theorem" "exist-nec2:1" "\<equiv>E"(2) "modus-tollens:1" by blast

AOT_theorem exists_nec2_4: \<open>\<diamond>\<not>\<tau>\<down> \<equiv> \<box>\<not>\<tau>\<down>\<close>
  by (metis "Act-Sub:3" "KBasic:12" "deduction-theorem" "exist-nec" exists_nec2_3 "\<equiv>I" "\<equiv>E"(4) "nec-imp-act" "reductio-aa:1")

AOT_theorem id_nec2_1: \<open>\<diamond>\<alpha> = \<beta> \<rightarrow> \<alpha> = \<beta>\<close>
  using "B\<diamond>" "RM\<diamond>" "Hypothetical Syllogism" "id-nec:1" by blast

AOT_theorem id_nec2_2: \<open>\<alpha> \<noteq> \<beta> \<rightarrow> \<box>\<alpha> \<noteq> \<beta>\<close>
  apply (AOT_subst_using subst: "=-infix"[THEN "\<equiv>Df"])
  using "KBasic2:1" "deduction-theorem" id_nec2_1 "\<equiv>E"(2) "modus-tollens:1" by blast

AOT_theorem id_nec2_3: \<open>\<diamond>\<alpha> \<noteq> \<beta> \<rightarrow> \<alpha> \<noteq> \<beta>\<close>
  apply (AOT_subst_using subst: "=-infix"[THEN "\<equiv>Df"])
  by (metis "KBasic:11" "deduction-theorem" "id-nec:2" "\<equiv>E"(3) "reductio-aa:2" "vdash-properties:6")

AOT_theorem id_nec2_4: \<open>\<diamond>\<alpha> = \<beta> \<rightarrow> \<box>\<alpha> = \<beta>\<close>
  using "Hypothetical Syllogism" id_nec2_1 "id-nec:1" by blast

AOT_theorem id_nec2_5: \<open>\<diamond>\<alpha> \<noteq> \<beta> \<rightarrow> \<box>\<alpha> \<noteq> \<beta>\<close>
  using id_nec2_3 id_nec2_2 "\<rightarrow>I" "\<rightarrow>E" by metis

AOT_theorem sc_eq_box_box_1: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>) \<equiv> (\<diamond>\<phi> \<rightarrow> \<box>\<phi>)\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I")
  using "KBasic:13" "5\<diamond>" "Hypothetical Syllogism" "vdash-properties:10" apply blast
  by (metis "KBasic2:1" "KBasic:1" "KBasic:2" "S5Basic:13" "\<equiv>E"(2) "raa-cor:5" "vdash-properties:6")

AOT_theorem sc_eq_box_box_2: \<open>(\<box>(\<phi> \<rightarrow> \<box>\<phi>) \<or> (\<diamond>\<phi> \<rightarrow> \<box>\<phi>)) \<rightarrow> (\<diamond>\<phi> \<equiv> \<box>\<phi>)\<close>
  by (metis "Act-Sub:3" "KBasic:13" "5\<diamond>" "\<or>E"(2) "deduction-theorem" "\<equiv>I" "nec-imp-act" "raa-cor:2" "vdash-properties:10")

AOT_theorem sc_eq_box_box_3: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>) \<rightarrow> (\<not>\<box>\<phi> \<equiv> \<box>\<not>\<phi>)\<close>
proof (rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>)\<close>
  AOT_hence \<open>\<diamond>\<phi> \<rightarrow> \<box>\<phi>\<close> using sc_eq_box_box_1 "\<equiv>E" by blast
  moreover AOT_assume \<open>\<not>\<box>\<phi>\<close>
  ultimately AOT_have \<open>\<not>\<diamond>\<phi>\<close>
    using "modus-tollens:1" by blast
  AOT_thus \<open>\<box>\<not>\<phi>\<close>
    using "KBasic2:1" "\<equiv>E"(2) by blast
next
  AOT_assume \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>)\<close>
  moreover AOT_assume \<open>\<box>\<not>\<phi>\<close>
  ultimately AOT_show \<open>\<not>\<box>\<phi>\<close>
    using "modus-tollens:1" "qml:2" "vdash-properties:10" "vdash-properties:1[2]" by blast
qed

AOT_theorem sc_eq_box_box_4: \<open>(\<box>(\<phi> \<rightarrow> \<box>\<phi>) & \<box>(\<psi> \<rightarrow> \<box>\<psi>)) \<rightarrow> ((\<box>\<phi> \<equiv> \<box>\<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>))\<close>
proof(rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume \<theta>: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>) & \<box>(\<psi> \<rightarrow> \<box>\<psi>)\<close>
  AOT_assume \<xi>: \<open>\<box>\<phi> \<equiv> \<box>\<psi>\<close>
  AOT_hence \<open>(\<box>\<phi> & \<box>\<psi>) \<or> (\<not>\<box>\<phi> & \<not>\<box>\<psi>)\<close>
    using "\<equiv>E"(4) "oth-class-taut:4:g" "raa-cor:3" by blast
  moreover {
    AOT_assume \<open>\<box>\<phi> & \<box>\<psi>\<close>
    AOT_hence \<open>\<box>(\<phi> \<equiv> \<psi>)\<close>
      using "KBasic:3" "KBasic:8" "\<equiv>E"(2) "vdash-properties:10" by blast
  }
  moreover {
    AOT_assume \<open>\<not>\<box>\<phi> & \<not>\<box>\<psi>\<close>
    moreover AOT_have \<open>\<not>\<box>\<phi> \<equiv> \<box>\<not>\<phi>\<close> and \<open>\<not>\<box>\<psi> \<equiv> \<box>\<not>\<psi>\<close>
      using \<theta> "Conjunction Simplification"(1) "Conjunction Simplification"(2) sc_eq_box_box_3 "vdash-properties:10" by metis+
    ultimately AOT_have \<open>\<box>\<not>\<phi> & \<box>\<not>\<psi>\<close>
      by (metis "&I" "Conjunction Simplification"(1) "Conjunction Simplification"(2) "\<equiv>E"(4) "modus-tollens:1" "raa-cor:3")
    AOT_hence \<open>\<box>(\<phi> \<equiv> \<psi>)\<close>
      using "KBasic:3" "KBasic:9" "\<equiv>E"(2) "vdash-properties:10" by blast
  }
  ultimately AOT_show \<open>\<box>(\<phi> \<equiv> \<psi>)\<close>
    using "\<or>E"(2) "reductio-aa:1" by blast
qed

AOT_theorem sc_eq_box_box_5: \<open>(\<box>(\<phi> \<rightarrow> \<box>\<phi>) & \<box>(\<psi> \<rightarrow> \<box>\<psi>)) \<rightarrow> ((\<phi> \<equiv> \<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>))\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume A: \<open>(\<box>(\<phi> \<rightarrow> \<box>\<phi>) & \<box>(\<psi> \<rightarrow> \<box>\<psi>))\<close>
  AOT_hence \<open>\<phi> \<rightarrow> \<box>\<phi>\<close> and \<open>\<psi> \<rightarrow> \<box>\<psi>\<close>
    using "&E" "qml:2"[axiom_inst] "\<rightarrow>E" by blast+
  moreover AOT_assume \<open>\<phi> \<equiv> \<psi>\<close>
  ultimately AOT_have \<open>\<box>\<phi> \<equiv> \<box>\<psi>\<close>
    using "\<rightarrow>E" "qml:2"[axiom_inst] "\<equiv>E" "\<equiv>I" by meson
  moreover AOT_have \<open>(\<box>\<phi> \<equiv> \<box>\<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
    using A sc_eq_box_box_4 "\<rightarrow>E" by blast
  ultimately AOT_show \<open>\<box>(\<phi> \<equiv> \<psi>)\<close> using "\<rightarrow>E" by blast
qed

AOT_theorem sc_eq_fur_1: \<open>\<diamond>\<^bold>\<A>\<phi> \<equiv> \<box>\<^bold>\<A>\<phi>\<close>
  using "Act-Basic:6" "Act-Sub:4" "\<equiv>E"(6) by blast

AOT_theorem sc_eq_fur_2: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>) \<rightarrow> (\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close>
  by (metis "B\<diamond>" "Act-Sub:3" "KBasic:13" "T\<diamond>" "Hypothetical Syllogism" "deduction-theorem" "\<equiv>I" "nec-imp-act")

AOT_theorem sc_eq_fur_3: \<open>\<box>\<forall>x (\<phi>{x} \<rightarrow> \<box>\<phi>{x}) \<rightarrow> (\<exists>!x \<phi>{x} \<rightarrow> \<^bold>\<iota>x \<phi>{x}\<down>)\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<box>\<forall>x (\<phi>{x} \<rightarrow> \<box>\<phi>{x})\<close>
  AOT_hence A: \<open>\<forall>x \<box>(\<phi>{x} \<rightarrow> \<box>\<phi>{x})\<close> using CBF "\<rightarrow>E" by blast
  AOT_assume \<open>\<exists>!x \<phi>{x}\<close>
  then AOT_obtain a where a_def: \<open>\<phi>{a} & \<forall>y (\<phi>{y} \<rightarrow> y = a)\<close>
    using "\<exists>E"[rotated 1, OF "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"]] by blast
  moreover AOT_have \<open>\<box>\<phi>{a}\<close> using calculation A "\<forall>E"(2) "qml:2"[axiom_inst] "\<rightarrow>E" "&E"(1) by blast
  AOT_hence \<open>\<^bold>\<A>\<phi>{a}\<close> using "nec-imp-act" "vdash-properties:6" by blast
  moreover AOT_have \<open>\<forall>y (\<^bold>\<A>\<phi>{y} \<rightarrow> y = a)\<close>
  proof (rule "\<forall>I"; rule "\<rightarrow>I")
    fix b
    AOT_assume \<open>\<^bold>\<A>\<phi>{b}\<close>
    AOT_hence \<open>\<diamond>\<phi>{b}\<close>
      using "Act-Sub:3" "vdash-properties:6" by blast
    moreover {
      AOT_have \<open>\<box>(\<phi>{b} \<rightarrow> \<box>\<phi>{b})\<close>
        using A "\<forall>E"(2) by blast
      AOT_hence \<open>\<diamond>\<phi>{b} \<rightarrow> \<box>\<phi>{b}\<close>
        using "KBasic:13" "5\<diamond>" "Hypothetical Syllogism" "vdash-properties:6" by blast
    }
    ultimately AOT_have \<open>\<box>\<phi>{b}\<close> using "\<rightarrow>E" by blast
    AOT_hence \<open>\<phi>{b}\<close> using "qml:2"[axiom_inst] "\<rightarrow>E" by blast
    AOT_thus \<open>b = a\<close>
      using a_def[THEN "&E"(2)] "\<forall>E"(2) "\<rightarrow>E" by blast
  qed
  ultimately AOT_have \<open>\<^bold>\<A>\<phi>{a} & \<forall>y (\<^bold>\<A>\<phi>{y} \<rightarrow> y = a)\<close>
    using "&I" by blast
  AOT_hence \<open>\<exists>x (\<^bold>\<A>\<phi>{x} & \<forall>y (\<^bold>\<A>\<phi>{y} \<rightarrow> y = x))\<close> using "\<exists>I" by fast
  AOT_hence \<open>\<exists>!x \<^bold>\<A>\<phi>{x}\<close> using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
  AOT_thus \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
    using "actual-desc:1"[THEN "\<equiv>E"(2)] by blast
qed

AOT_theorem sc_eq_fur_4: \<open>\<box>\<forall>x (\<phi>{x} \<rightarrow> \<box>\<phi>{x}) \<rightarrow> (x = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x)))\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>\<box>\<forall>x (\<phi>{x} \<rightarrow> \<box>\<phi>{x})\<close>
  AOT_hence \<open>\<forall>x \<box>(\<phi>{x} \<rightarrow> \<box>\<phi>{x})\<close> using CBF "\<rightarrow>E" by blast
  AOT_hence A: \<open>\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<phi>{\<alpha>}\<close> for \<alpha> using sc_eq_fur_2 "\<forall>E" "\<rightarrow>E" by fast
  AOT_show \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x))\<close>
  proof (rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>x = \<^bold>\<iota>x \<phi>{x}\<close>
    AOT_hence B: \<open>\<^bold>\<A>\<phi>{x} & \<forall>z (\<^bold>\<A>\<phi>{z} \<rightarrow> z = x)\<close>
      using "nec-hintikka-scheme"[THEN "\<equiv>E"(1)] by blast
    AOT_show \<open>\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x)\<close>
    proof (rule "&I"; (rule "\<forall>I"; rule "\<rightarrow>I")?)
      AOT_show \<open>\<phi>{x}\<close> using A B[THEN "&E"(1)] "\<equiv>E"(1) by blast
    next
      AOT_show \<open>z = x\<close> if \<open>\<phi>{z}\<close> for z
        using that B[THEN "&E"(2)] "\<forall>E"(2) "\<rightarrow>E" A[THEN "\<equiv>E"(2)] by blast
    qed
  next
    AOT_assume B: \<open>\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x)\<close>
    AOT_have \<open>\<^bold>\<A>\<phi>{x} & \<forall>z (\<^bold>\<A>\<phi>{z} \<rightarrow> z = x)\<close>
    proof(rule "&I"; (rule "\<forall>I"; rule "\<rightarrow>I")?)
      AOT_show \<open>\<^bold>\<A>\<phi>{x}\<close> using B[THEN "&E"(1)] A[THEN "\<equiv>E"(2)] by blast
    next
      AOT_show \<open>b = x\<close> if \<open>\<^bold>\<A>\<phi>{b}\<close> for b
        using that A[THEN "\<equiv>E"(1)] B[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    qed
    AOT_thus \<open>x = \<^bold>\<iota>x \<phi>{x}\<close>
      using "nec-hintikka-scheme"[THEN "\<equiv>E"(2)] by blast
  qed
qed

AOT_theorem id_act_1: \<open>\<alpha> = \<beta> \<equiv> \<^bold>\<A>\<alpha> = \<beta>\<close>
  by (meson "Act-Sub:3" "Hypothetical Syllogism" id_nec2_1 "id-nec:2" "\<equiv>I" "nec-imp-act")

AOT_theorem id_act_2: \<open>\<alpha> \<noteq> \<beta> \<equiv> \<^bold>\<A>\<alpha> \<noteq> \<beta>\<close>
proof (AOT_subst "\<guillemotleft>\<alpha> \<noteq> \<beta>\<guillemotright>" "\<guillemotleft>\<not>(\<alpha> = \<beta>)\<guillemotright>")
  AOT_modally_strict {
    AOT_show \<open>\<alpha> \<noteq> \<beta> \<equiv> \<not>(\<alpha> = \<beta>)\<close>
      by (simp add: "=-infix" "\<equiv>Df")
  }
next
  AOT_show \<open>\<not>(\<alpha> = \<beta>) \<equiv> \<^bold>\<A>\<not>(\<alpha> = \<beta>)\<close>
  proof (safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<not>\<alpha> = \<beta>\<close>
    AOT_hence \<open>\<not>\<^bold>\<A>\<alpha> = \<beta>\<close> using id_act_1 "\<equiv>E"(3) by blast
    AOT_thus \<open>\<^bold>\<A>\<not>\<alpha> = \<beta>\<close>
      using "\<not>\<not>E" "Act-Sub:1" "\<equiv>E"(3) by blast
  next
    AOT_assume \<open>\<^bold>\<A>\<not>\<alpha> = \<beta>\<close>
    AOT_hence \<open>\<not>\<^bold>\<A>\<alpha> = \<beta>\<close>
      using "\<not>\<not>I" "Act-Sub:1" "\<equiv>E"(4) by blast
    AOT_thus \<open>\<not>\<alpha> = \<beta>\<close>
      using id_act_1 "\<equiv>E"(4) by blast
  qed
qed

AOT_theorem A_Exists_1: \<open>\<^bold>\<A>\<exists>!\<alpha> \<phi>{\<alpha>} \<equiv> \<exists>!\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close>
proof -
  AOT_have \<open>\<^bold>\<A>\<exists>!\<alpha> \<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<exists>\<alpha>\<forall>\<beta> (\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    by (AOT_subst_using subst: "uniqueness:2")
       (simp add: "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<exists>\<alpha> \<^bold>\<A>\<forall>\<beta> (\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    by (simp add: "Act-Basic:10")
  also AOT_have \<open>\<dots> \<equiv> \<exists>\<alpha>\<forall>\<beta> \<^bold>\<A>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    by (AOT_subst "\<lambda> \<tau> . \<guillemotleft>\<^bold>\<A>\<forall>\<beta> (\<phi>{\<beta>} \<equiv> \<beta> = \<tau>)\<guillemotright>" "\<lambda> \<tau> . \<guillemotleft>\<forall>\<beta> \<^bold>\<A>(\<phi>{\<beta>} \<equiv> \<beta> = \<tau>)\<guillemotright>")
       (auto simp: "logic-actual-nec:3" "vdash-properties:1[2]" "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<exists>\<alpha>\<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<^bold>\<A>\<beta> = \<alpha>)\<close>
    by (AOT_subst_rev "\<lambda> \<tau> \<tau>' . \<guillemotleft>\<^bold>\<A>(\<phi>{\<tau>'} \<equiv> \<tau>' = \<tau>)\<guillemotright>" "\<lambda> \<tau> \<tau>'. \<guillemotleft>\<^bold>\<A>\<phi>{\<tau>'} \<equiv> \<^bold>\<A>\<tau>' = \<tau>\<guillemotright>")
       (auto simp: "Act-Basic:5" "cqt-further:7")
  also AOT_have \<open>\<dots> \<equiv> \<exists>\<alpha>\<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    apply (AOT_subst "\<lambda> \<tau> \<tau>' :: 'a . \<guillemotleft>\<^bold>\<A>\<tau>' = \<tau>\<guillemotright>" "\<lambda> \<tau> \<tau>'. \<guillemotleft>\<tau>' = \<tau>\<guillemotright>")
     apply (meson id_act_1 "\<equiv>E"(6) "oth-class-taut:3:a")
    by (simp add: "cqt-further:7")
  also AOT_have \<open>... \<equiv> \<exists>!\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close>
    using "uniqueness:2" "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by fast
  finally show ?thesis .
qed

AOT_theorem A_Exists_2: \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<equiv> \<^bold>\<A>\<exists>!x \<phi>{x}\<close>
  by (AOT_subst_using subst: A_Exists_1)
     (simp add: "actual-desc:1")

AOT_theorem id_act_desc_1: \<open>\<^bold>\<iota>x (x = y)\<down>\<close>
proof(rule "existence:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "\<exists>I")
  AOT_show \<open>[\<lambda>x E!x \<rightarrow> E!x]\<^bold>\<iota>x (x = y)\<close>
  proof (rule "russell-axiom[exe,1].nec-russell-axiom"[THEN "\<equiv>E"(2)]; rule "\<exists>I"; (rule "&I")+)
    AOT_show \<open>\<^bold>\<A>y = y\<close> by (simp add: "RA[2]" "id-eq:1")
  next
    AOT_show \<open>\<forall>z (\<^bold>\<A>z = y \<rightarrow> z = y)\<close>
      apply (rule "\<forall>I")
      using id_act_1[THEN "\<equiv>E"(2)] "\<rightarrow>I" by blast
  next
    AOT_show \<open>[\<lambda>x E!x \<rightarrow> E!x]y\<close>
    proof (rule "lambda-predicates:2"[axiom_inst, THEN "\<rightarrow>E", THEN "\<equiv>E"(2)])
      AOT_show \<open>[\<lambda>x E!x \<rightarrow> E!x]\<down>\<close>
        by "cqt:2[lambda]"
    next
      AOT_show \<open>E!y \<rightarrow> E!y\<close> 
        by (simp add: "if-p-then-p")
    qed
  qed
next
  AOT_show \<open>[\<lambda>x E!x \<rightarrow> E!x]\<down>\<close>
    by "cqt:2[lambda]"
qed

AOT_theorem id_act_desc_2: \<open>y = \<^bold>\<iota>x (x = y)\<close>
  by (rule descriptions[axiom_inst, THEN "\<equiv>E"(2)]; rule "\<forall>I"; rule id_act_1[symmetric])

AOT_theorem pre_en_eq_1_1: \<open>x\<^sub>1[F] \<rightarrow> \<box>x\<^sub>1[F]\<close>
  by (simp add: encoding "vdash-properties:1[2]")

AOT_theorem pre_en_eq_1_2: \<open>x\<^sub>1x\<^sub>2[F] \<rightarrow> \<box>x\<^sub>1x\<^sub>2[F]\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>x\<^sub>1x\<^sub>2[F]\<close>
  AOT_hence \<open>x\<^sub>1[\<lambda>y [F]yx\<^sub>2]\<close> and \<open>x\<^sub>2[\<lambda>y [F]x\<^sub>1y]\<close>
    using "nary_encoding[2]"[axiom_inst, THEN "\<equiv>E"(1)] "&E" by blast+
  moreover AOT_have \<open>[\<lambda>y [F]yx\<^sub>2]\<down>\<close> by "cqt:2[lambda]"
  moreover AOT_have \<open>[\<lambda>y [F]x\<^sub>1y]\<down>\<close> by "cqt:2[lambda]"
  ultimately AOT_have \<open>\<box>x\<^sub>1[\<lambda>y [F]yx\<^sub>2]\<close> and \<open>\<box>x\<^sub>2[\<lambda>y [F]x\<^sub>1y]\<close>
    using encoding[axiom_inst, unvarify F] "\<rightarrow>E" "&I" by blast+
  note A = this
  AOT_hence \<open>\<box>(x\<^sub>1[\<lambda>y [F]yx\<^sub>2] & x\<^sub>2[\<lambda>y [F]x\<^sub>1y])\<close>
    using "KBasic:3"[THEN "\<equiv>E"(2)] "&I" by blast
  AOT_thus \<open>\<box>x\<^sub>1x\<^sub>2[F]\<close>
    by (rule "nary_encoding[2]"[axiom_inst, THEN RN, THEN "KBasic:6"[THEN "\<rightarrow>E"], THEN "\<equiv>E"(2)])
qed

AOT_theorem pre_en_eq_1_3: \<open>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<rightarrow> \<box>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  AOT_hence \<open>x\<^sub>1[\<lambda>y [F]yx\<^sub>2x\<^sub>3]\<close> and \<open>x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3]\<close> and \<open>x\<^sub>3[\<lambda>y [F]x\<^sub>1x\<^sub>2y]\<close>
    using "nary_encoding[3]"[axiom_inst, THEN "\<equiv>E"(1)] "&E" by blast+
  moreover AOT_have \<open>[\<lambda>y [F]yx\<^sub>2x\<^sub>3]\<down>\<close> by "cqt:2[lambda]"
  moreover AOT_have \<open>[\<lambda>y [F]x\<^sub>1yx\<^sub>3]\<down>\<close> by "cqt:2[lambda]"
  moreover AOT_have \<open>[\<lambda>y [F]x\<^sub>1x\<^sub>2y]\<down>\<close> by "cqt:2[lambda]"
  ultimately AOT_have \<open>\<box>x\<^sub>1[\<lambda>y [F]yx\<^sub>2x\<^sub>3]\<close> and \<open>\<box>x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3]\<close> and \<open>\<box>x\<^sub>3[\<lambda>y [F]x\<^sub>1x\<^sub>2y]\<close>
    using encoding[axiom_inst, unvarify F] "\<rightarrow>E" by blast+
  note A = this
  AOT_have B: \<open>\<box>(x\<^sub>1[\<lambda>y [F]yx\<^sub>2x\<^sub>3] & x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3] & x\<^sub>3[\<lambda>y [F]x\<^sub>1x\<^sub>2y])\<close>
    by (rule "KBasic:3"[THEN "\<equiv>E"(2)] "&I" A)+
  AOT_thus \<open>\<box>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
    by (rule "nary_encoding[3]"[axiom_inst, THEN RN, THEN "KBasic:6"[THEN "\<rightarrow>E"], THEN "\<equiv>E"(2)])
qed

AOT_theorem pre_en_eq_1_4: \<open>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<rightarrow> \<box>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  AOT_hence \<open>x\<^sub>1[\<lambda>y [F]yx\<^sub>2x\<^sub>3x\<^sub>4]\<close> and \<open>x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3x\<^sub>4]\<close> and \<open>x\<^sub>3[\<lambda>y [F]x\<^sub>1x\<^sub>2yx\<^sub>4]\<close> and  \<open>x\<^sub>4[\<lambda>y [F]x\<^sub>1x\<^sub>2x\<^sub>3y]\<close>
    using "nary_encoding[4]"[axiom_inst, THEN "\<equiv>E"(1)] "&E" by metis+
  moreover AOT_have \<open>[\<lambda>y [F]yx\<^sub>2x\<^sub>3x\<^sub>4]\<down>\<close> by "cqt:2[lambda]"
  moreover AOT_have \<open>[\<lambda>y [F]x\<^sub>1yx\<^sub>3x\<^sub>4]\<down>\<close> by "cqt:2[lambda]"
  moreover AOT_have \<open>[\<lambda>y [F]x\<^sub>1x\<^sub>2yx\<^sub>4]\<down>\<close> by "cqt:2[lambda]"
  moreover AOT_have \<open>[\<lambda>y [F]x\<^sub>1x\<^sub>2x\<^sub>3y]\<down>\<close> by "cqt:2[lambda]"
  ultimately AOT_have \<open>\<box>x\<^sub>1[\<lambda>y [F]yx\<^sub>2x\<^sub>3x\<^sub>4]\<close> and \<open>\<box>x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3x\<^sub>4]\<close> and \<open>\<box>x\<^sub>3[\<lambda>y [F]x\<^sub>1x\<^sub>2yx\<^sub>4]\<close> and \<open>\<box>x\<^sub>4[\<lambda>y [F]x\<^sub>1x\<^sub>2x\<^sub>3y]\<close>
    using "\<rightarrow>E" encoding[axiom_inst, unvarify F] by blast+
  note A = this
  AOT_have B: \<open>\<box>(x\<^sub>1[\<lambda>y [F]yx\<^sub>2x\<^sub>3x\<^sub>4] & x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3x\<^sub>4] & x\<^sub>3[\<lambda>y [F]x\<^sub>1x\<^sub>2yx\<^sub>4] & x\<^sub>4[\<lambda>y [F]x\<^sub>1x\<^sub>2x\<^sub>3y])\<close>
    by (rule "KBasic:3"[THEN "\<equiv>E"(2)] "&I" A)+
  AOT_thus \<open>\<box>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
    by (rule "nary_encoding[4]"[axiom_inst, THEN RN, THEN "KBasic:6"[THEN "\<rightarrow>E"], THEN "\<equiv>E"(2)])
qed

AOT_theorem pre_en_eq_2_1: \<open>\<not>x\<^sub>1[F] \<rightarrow> \<box>\<not>x\<^sub>1[F]\<close>
proof (rule "\<rightarrow>I"; rule "raa-cor:1")
  AOT_assume \<open>\<not>\<box>\<not>x\<^sub>1[F]\<close>
  AOT_hence \<open>\<diamond>x\<^sub>1[F]\<close>
    by (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_hence \<open>x\<^sub>1[F]\<close>
    by(rule "S5Basic:13"[THEN "\<equiv>E"(1), OF  pre_en_eq_1_1[THEN RN], THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<rightarrow>E"])
  moreover AOT_assume \<open>\<not>x\<^sub>1[F]\<close>
  ultimately AOT_show \<open>x\<^sub>1[F] & \<not>x\<^sub>1[F]\<close> by (rule "&I")
qed
AOT_theorem pre_en_eq_2_2: \<open>\<not>x\<^sub>1x\<^sub>2[F] \<rightarrow> \<box>\<not>x\<^sub>1x\<^sub>2[F]\<close>
proof (rule "\<rightarrow>I"; rule "raa-cor:1")
  AOT_assume \<open>\<not>\<box>\<not>x\<^sub>1x\<^sub>2[F]\<close>
  AOT_hence \<open>\<diamond>x\<^sub>1x\<^sub>2[F]\<close>
    by (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_hence \<open>x\<^sub>1x\<^sub>2[F]\<close>
    by(rule "S5Basic:13"[THEN "\<equiv>E"(1), OF  pre_en_eq_1_2[THEN RN], THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<rightarrow>E"])
  moreover AOT_assume \<open>\<not>x\<^sub>1x\<^sub>2[F]\<close>
  ultimately AOT_show \<open>x\<^sub>1x\<^sub>2[F] & \<not>x\<^sub>1x\<^sub>2[F]\<close> by (rule "&I")
qed

AOT_theorem pre_en_eq_2_3: \<open>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<rightarrow> \<box>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
proof (rule "\<rightarrow>I"; rule "raa-cor:1")
  AOT_assume \<open>\<not>\<box>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  AOT_hence \<open>\<diamond>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
    by (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_hence \<open>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
    by(rule "S5Basic:13"[THEN "\<equiv>E"(1), OF  pre_en_eq_1_3[THEN RN], THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<rightarrow>E"])
  moreover AOT_assume \<open>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  ultimately AOT_show \<open>x\<^sub>1x\<^sub>2x\<^sub>3[F] & \<not>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close> by (rule "&I")
qed

AOT_theorem pre_en_eq_2_4: \<open>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<rightarrow> \<box>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
proof (rule "\<rightarrow>I"; rule "raa-cor:1")
  AOT_assume \<open>\<not>\<box>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  AOT_hence \<open>\<diamond>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
    by (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_hence \<open>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
    by(rule "S5Basic:13"[THEN "\<equiv>E"(1), OF  pre_en_eq_1_4[THEN RN], THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<rightarrow>E"])
  moreover AOT_assume \<open>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  ultimately AOT_show \<open>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] & \<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close> by (rule "&I")
qed

AOT_theorem en_eq_1_1: \<open>\<diamond>x\<^sub>1[F] \<equiv> \<box>x\<^sub>1[F]\<close>
  using pre_en_eq_1_1[THEN RN] sc_eq_box_box_2 "\<or>I" "\<rightarrow>E" by metis
AOT_theorem en_eq_1_2: \<open>\<diamond>x\<^sub>1x\<^sub>2[F] \<equiv> \<box>x\<^sub>1x\<^sub>2[F]\<close>
  using pre_en_eq_1_2[THEN RN] sc_eq_box_box_2 "\<or>I" "\<rightarrow>E" by metis
AOT_theorem en_eq_1_3: \<open>\<diamond>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> \<box>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  using pre_en_eq_1_3[THEN RN] sc_eq_box_box_2 "\<or>I" "\<rightarrow>E" by fast
AOT_theorem en_eq_1_4: \<open>\<diamond>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> \<box>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  using pre_en_eq_1_4[THEN RN] sc_eq_box_box_2 "\<or>I" "\<rightarrow>E" by fast

AOT_theorem en_eq_2_1: \<open>x\<^sub>1[F] \<equiv> \<box>x\<^sub>1[F]\<close>
  by (simp add: "\<equiv>I" pre_en_eq_1_1 "qml:2"[axiom_inst])
AOT_theorem en_eq_2_2: \<open>x\<^sub>1x\<^sub>2[F] \<equiv> \<box>x\<^sub>1x\<^sub>2[F]\<close>
  by (simp add: "\<equiv>I" pre_en_eq_1_2 "qml:2"[axiom_inst])
AOT_theorem en_eq_2_3: \<open>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> \<box>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  by (simp add: "\<equiv>I" pre_en_eq_1_3 "qml:2"[axiom_inst])
AOT_theorem en_eq_2_4: \<open>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> \<box>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  by (simp add: "\<equiv>I" pre_en_eq_1_4 "qml:2"[axiom_inst])

AOT_theorem en_eq_3_1: \<open>\<diamond>x\<^sub>1[F] \<equiv> x\<^sub>1[F]\<close>
  using "T\<diamond>" derived_S5_rules_2[where \<Gamma>="{}", OF pre_en_eq_1_1] "\<equiv>I" by blast
AOT_theorem en_eq_3_2: \<open>\<diamond>x\<^sub>1x\<^sub>2[F] \<equiv> x\<^sub>1x\<^sub>2[F]\<close>
  using "T\<diamond>" derived_S5_rules_2[where \<Gamma>="{}", OF pre_en_eq_1_2] "\<equiv>I" by blast
AOT_theorem en_eq_3_3: \<open>\<diamond>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  using "T\<diamond>" derived_S5_rules_2[where \<Gamma>="{}", OF pre_en_eq_1_3] "\<equiv>I" by blast
AOT_theorem en_eq_3_4: \<open>\<diamond>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  using "T\<diamond>" derived_S5_rules_2[where \<Gamma>="{}", OF pre_en_eq_1_4] "\<equiv>I" by blast

AOT_theorem en_eq_4_1: \<open>(x\<^sub>1[F] \<equiv> y\<^sub>1[G]) \<equiv> (\<box>x\<^sub>1[F] \<equiv> \<box>y\<^sub>1[G])\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] "\<equiv>E"(1,2) en_eq_2_1 by blast+
AOT_theorem en_eq_4_2: \<open>(x\<^sub>1x\<^sub>2[F] \<equiv> y\<^sub>1y\<^sub>2[G]) \<equiv> (\<box>x\<^sub>1x\<^sub>2[F] \<equiv> \<box>y\<^sub>1y\<^sub>2[G])\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] "\<equiv>E"(1,2) en_eq_2_2 by blast+
AOT_theorem en_eq_4_3: \<open>(x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> y\<^sub>1y\<^sub>2y\<^sub>3[G]) \<equiv> (\<box>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> \<box>y\<^sub>1y\<^sub>2y\<^sub>3[G])\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] "\<equiv>E"(1,2) en_eq_2_3 by blast+
AOT_theorem en_eq_4_4: \<open>(x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> y\<^sub>1y\<^sub>2y\<^sub>3y\<^sub>4[G]) \<equiv> (\<box>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> \<box>y\<^sub>1y\<^sub>2y\<^sub>3y\<^sub>4[G])\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
  using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] "\<equiv>E"(1,2) en_eq_2_4 by blast+

AOT_theorem en_eq_5_1: \<open>\<box>(x\<^sub>1[F] \<equiv> y\<^sub>1[G]) \<equiv> (\<box>x\<^sub>1[F] \<equiv> \<box>y\<^sub>1[G])\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I")
  using en_eq_4_1[THEN "\<equiv>E"(1)] "qml:2"[axiom_inst, THEN "\<rightarrow>E"] apply blast
  using sc_eq_box_box_4[THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
        "&I"[OF pre_en_eq_1_1[THEN RN], OF pre_en_eq_1_1[THEN RN]] by blast
AOT_theorem en_eq_5_2: \<open>\<box>(x\<^sub>1x\<^sub>2[F] \<equiv> y\<^sub>1y\<^sub>2[G]) \<equiv> (\<box>x\<^sub>1x\<^sub>2[F] \<equiv> \<box>y\<^sub>1y\<^sub>2[G])\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I")
  using en_eq_4_2[THEN "\<equiv>E"(1)] "qml:2"[axiom_inst, THEN "\<rightarrow>E"] apply blast
  using sc_eq_box_box_4[THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
        "&I"[OF pre_en_eq_1_2[THEN RN], OF pre_en_eq_1_2[THEN RN]] by blast
AOT_theorem en_eq_5_3: \<open>\<box>(x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> y\<^sub>1y\<^sub>2y\<^sub>3[G]) \<equiv> (\<box>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> \<box>y\<^sub>1y\<^sub>2y\<^sub>3[G])\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I")
  using en_eq_4_3[THEN "\<equiv>E"(1)] "qml:2"[axiom_inst, THEN "\<rightarrow>E"] apply blast
  using sc_eq_box_box_4[THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
        "&I"[OF pre_en_eq_1_3[THEN RN], OF pre_en_eq_1_3[THEN RN]] by blast
AOT_theorem en_eq_5_4: \<open>\<box>(x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> y\<^sub>1y\<^sub>2y\<^sub>3y\<^sub>4[G]) \<equiv> (\<box>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> \<box>y\<^sub>1y\<^sub>2y\<^sub>3y\<^sub>4[G])\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I")
  using en_eq_4_4[THEN "\<equiv>E"(1)] "qml:2"[axiom_inst, THEN "\<rightarrow>E"] apply blast
  using sc_eq_box_box_4[THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
        "&I"[OF pre_en_eq_1_4[THEN RN], OF pre_en_eq_1_4[THEN RN]] by blast

AOT_theorem en_eq_6_1: \<open>(x\<^sub>1[F] \<equiv> y\<^sub>1[G]) \<equiv> \<box>(x\<^sub>1[F] \<equiv> y\<^sub>1[G])\<close>
  using en_eq_5_1[symmetric] en_eq_4_1 "\<equiv>E"(5) by fast
AOT_theorem en_eq_6_2: \<open>(x\<^sub>1x\<^sub>2[F] \<equiv> y\<^sub>1y\<^sub>2[G]) \<equiv> \<box>(x\<^sub>1x\<^sub>2[F] \<equiv> y\<^sub>1y\<^sub>2[G])\<close>
  using en_eq_5_2[symmetric] en_eq_4_2 "\<equiv>E"(5) by fast
AOT_theorem en_eq_6_3: \<open>(x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> y\<^sub>1y\<^sub>2y\<^sub>3[G]) \<equiv> \<box>(x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> y\<^sub>1y\<^sub>2y\<^sub>3[G])\<close>
  using en_eq_5_3[symmetric] en_eq_4_3 "\<equiv>E"(5) by fast
AOT_theorem en_eq_6_4: \<open>(x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> y\<^sub>1y\<^sub>2y\<^sub>3y\<^sub>4[G]) \<equiv> \<box>(x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> y\<^sub>1y\<^sub>2y\<^sub>3y\<^sub>4[G])\<close>
  using en_eq_5_4[symmetric] en_eq_4_4 "\<equiv>E"(5) by fast

AOT_theorem en_eq_7_1: \<open>\<not>x\<^sub>1[F] \<equiv> \<box>\<not>x\<^sub>1[F]\<close>
  using pre_en_eq_2_1 "qml:2"[axiom_inst] "\<equiv>I" by blast
AOT_theorem en_eq_7_2: \<open>\<not>x\<^sub>1x\<^sub>2[F] \<equiv> \<box>\<not>x\<^sub>1x\<^sub>2[F]\<close>
  using pre_en_eq_2_2 "qml:2"[axiom_inst] "\<equiv>I" by blast
AOT_theorem en_eq_7_3: \<open>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> \<box>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  using pre_en_eq_2_3 "qml:2"[axiom_inst] "\<equiv>I" by blast
AOT_theorem en_eq_7_4: \<open>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> \<box>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  using pre_en_eq_2_4 "qml:2"[axiom_inst] "\<equiv>I" by blast

AOT_theorem en_eq_8_1: \<open>\<diamond>\<not>x\<^sub>1[F] \<equiv> \<not>x\<^sub>1[F]\<close>
  using en_eq_2_1[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)]] "KBasic:11" "\<equiv>E"(5)[symmetric] by blast
AOT_theorem en_eq_8_2: \<open>\<diamond>\<not>x\<^sub>1x\<^sub>2[F] \<equiv> \<not>x\<^sub>1x\<^sub>2[F]\<close>
  using en_eq_2_2[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)]] "KBasic:11" "\<equiv>E"(5)[symmetric] by blast
AOT_theorem en_eq_8_3: \<open>\<diamond>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> \<not>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  using en_eq_2_3[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)]] "KBasic:11" "\<equiv>E"(5)[symmetric] by blast
AOT_theorem en_eq_8_4: \<open>\<diamond>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> \<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  using en_eq_2_4[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)]] "KBasic:11" "\<equiv>E"(5)[symmetric] by blast

AOT_theorem en_eq_9_1: \<open>\<diamond>\<not>x\<^sub>1[F] \<equiv> \<box>\<not>x\<^sub>1[F]\<close>
  using en_eq_7_1 en_eq_8_1 "\<equiv>E"(5) by blast
AOT_theorem en_eq_9_2: \<open>\<diamond>\<not>x\<^sub>1x\<^sub>2[F] \<equiv> \<box>\<not>x\<^sub>1x\<^sub>2[F]\<close>
  using en_eq_7_2 en_eq_8_2 "\<equiv>E"(5) by blast
AOT_theorem en_eq_9_3: \<open>\<diamond>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> \<box>\<not>x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  using en_eq_7_3 en_eq_8_3 "\<equiv>E"(5) by blast
AOT_theorem en_eq_9_4: \<open>\<diamond>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> \<box>\<not>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  using en_eq_7_4 en_eq_8_4 "\<equiv>E"(5) by blast

AOT_theorem en_eq_10_1: \<open>\<^bold>\<A>x\<^sub>1[F] \<equiv> x\<^sub>1[F]\<close>
  by (metis "Act-Sub:3" "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "nec-imp-act" en_eq_3_1 pre_en_eq_1_1)
AOT_theorem en_eq_10_2: \<open>\<^bold>\<A>x\<^sub>1x\<^sub>2[F] \<equiv> x\<^sub>1x\<^sub>2[F]\<close>
  by (metis "Act-Sub:3" "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "nec-imp-act" en_eq_3_2 pre_en_eq_1_2)
AOT_theorem en_eq_10_3: \<open>\<^bold>\<A>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> x\<^sub>1x\<^sub>2x\<^sub>3[F]\<close>
  by (metis "Act-Sub:3" "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "nec-imp-act" en_eq_3_3 pre_en_eq_1_3)
AOT_theorem en_eq_10_4: \<open>\<^bold>\<A>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F]\<close>
  by (metis "Act-Sub:3" "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "nec-imp-act" en_eq_3_4 pre_en_eq_1_4)

AOT_theorem oa_facts_1: \<open>O!x \<rightarrow> \<box>O!x\<close>
proof(rule "\<rightarrow>I")
  AOT_modally_strict {
    AOT_have \<open>[\<lambda>x \<diamond>E!x]x \<equiv> \<diamond>E!x\<close>
      by (rule "lambda-predicates:2"[axiom_inst, THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  } note \<theta> = this
  AOT_assume \<open>O!x\<close>
  AOT_hence \<open>[\<lambda>x \<diamond>E!x]x\<close>
    by (rule "=\<^sub>d\<^sub>fE"(2)[OF AOT_ordinary, rotated 1]) "cqt:2[lambda]"
  AOT_hence \<open>\<diamond>E!x\<close> using \<theta>[THEN "\<equiv>E"(1)] by blast
  AOT_hence 0: \<open>\<box>\<diamond>E!x\<close> using "qml:3"[axiom_inst, THEN "\<rightarrow>E"] by blast
  AOT_have \<open>\<box>[\<lambda>x \<diamond>E!x]x\<close>
    by (AOT_subst_using subst: \<theta>) (simp add: 0)
  AOT_thus \<open>\<box>O!x\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_ordinary, rotated 1]) "cqt:2[lambda]"
qed

AOT_theorem oa_facts_2: \<open>A!x \<rightarrow> \<box>A!x\<close>
proof(rule "\<rightarrow>I")
  AOT_modally_strict {
    AOT_have \<open>[\<lambda>x \<not>\<diamond>E!x]x \<equiv> \<not>\<diamond>E!x\<close>
      by (rule "lambda-predicates:2"[axiom_inst, THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  } note \<theta> = this
  AOT_assume \<open>A!x\<close>
  AOT_hence \<open>[\<lambda>x \<not>\<diamond>E!x]x\<close>
    by (rule "=\<^sub>d\<^sub>fE"(2)[OF AOT_abstract, rotated 1]) "cqt:2[lambda]"
  AOT_hence \<open>\<not>\<diamond>E!x\<close> using \<theta>[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<box>\<not>E!x\<close> using "KBasic2:1"[THEN "\<equiv>E"(2)] by blast
  AOT_hence 0: \<open>\<box>\<box>\<not>E!x\<close> using "S5Basic:5"[THEN "\<rightarrow>E"] by blast
  AOT_have 1: \<open>\<box>\<not>\<diamond>E!x\<close>
    apply (AOT_subst "\<guillemotleft>\<not>\<diamond>E!x\<guillemotright>" "\<guillemotleft>\<box>\<not>E!x\<guillemotright>")
    using "KBasic2:1"[symmetric] apply blast
    using 0 by blast
  AOT_have \<open>\<box>[\<lambda>x \<not>\<diamond>E!x]x\<close>
    by (AOT_subst_using subst: \<theta>) (simp add: 1)
  AOT_thus \<open>\<box>A!x\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_abstract, rotated 1]) "cqt:2[lambda]"
qed

AOT_theorem oa_facts_3: \<open>\<diamond>O!x \<rightarrow> O!x\<close>
  using oa_facts_1 "B\<diamond>" "RM\<diamond>" "Hypothetical Syllogism" by blast
AOT_theorem oa_facts_4: \<open>\<diamond>A!x \<rightarrow> A!x\<close>
  using oa_facts_2 "B\<diamond>" "RM\<diamond>" "Hypothetical Syllogism" by blast

AOT_theorem oa_facts_5: \<open>\<diamond>O!x \<equiv> \<box>O!x\<close>
  by (meson "Act-Sub:3" "Hypothetical Syllogism" "\<equiv>I" "nec-imp-act" oa_facts_1 oa_facts_3)

AOT_theorem oa_facts_6: \<open>\<diamond>A!x \<equiv> \<box>A!x\<close>
  by (meson "Act-Sub:3" "Hypothetical Syllogism" "\<equiv>I" "nec-imp-act" oa_facts_2 oa_facts_4)

AOT_theorem oa_facts_7: \<open>O!x \<equiv> \<^bold>\<A>O!x\<close>
  by (meson "Act-Sub:3" "Hypothetical Syllogism" "\<equiv>I" "nec-imp-act" oa_facts_1 oa_facts_3)

AOT_theorem oa_facts_8: \<open>A!x \<equiv> \<^bold>\<A>A!x\<close>
  by (meson "Act-Sub:3" "Hypothetical Syllogism" "\<equiv>I" "nec-imp-act" oa_facts_2 oa_facts_4)

AOT_theorem beta_C_meta: \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n, \<nu>\<^sub>1...\<nu>\<^sub>n}]\<down> \<rightarrow> ([\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n, \<nu>\<^sub>1...\<nu>\<^sub>n}]\<nu>\<^sub>1...\<nu>\<^sub>n \<equiv> \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n, \<nu>\<^sub>1...\<nu>\<^sub>n})\<close>
  using "lambda-predicates:2"[axiom_inst] by blast

AOT_theorem beta_C_cor_1: \<open>(\<forall>\<nu>\<^sub>1...\<forall>\<nu>\<^sub>n([\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n, \<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>)) \<rightarrow> \<forall>\<nu>\<^sub>1...\<forall>\<nu>\<^sub>n ([\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n, \<nu>\<^sub>1...\<nu>\<^sub>n}]\<nu>\<^sub>1...\<nu>\<^sub>n \<equiv> \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n, \<nu>\<^sub>1...\<nu>\<^sub>n})\<close>
  apply (rule "cqt-basic:14"[where 'a='a, THEN "\<rightarrow>E"])
  using beta_C_meta "\<forall>I" by fast

AOT_theorem beta_C_cor_2: \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<down> \<rightarrow> \<forall>\<nu>\<^sub>1...\<forall>\<nu>\<^sub>n ([\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<nu>\<^sub>1...\<nu>\<^sub>n \<equiv> \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n})\<close>
  apply (rule "\<rightarrow>I"; rule "\<forall>I")
  using beta_C_meta[THEN "\<rightarrow>E"] by fast

(* TODO: syntax + double-check if this is really a faithful representation *)
theorem beta_C_cor_3: assumes \<open>\<And>\<nu>\<^sub>1\<nu>\<^sub>n. AOT_instance_of_cqt_2 (\<phi> (AOT_term_of_var \<nu>\<^sub>1\<nu>\<^sub>n))\<close>
  shows \<open>[v \<Turnstile> \<forall>\<nu>\<^sub>1...\<forall>\<nu>\<^sub>n ([\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n,\<mu>\<^sub>1...\<mu>\<^sub>n}]\<nu>\<^sub>1...\<nu>\<^sub>n \<equiv> \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n,\<nu>\<^sub>1...\<nu>\<^sub>n})]\<close>
  using "cqt:2[lambda]"[axiom_inst, OF assms] beta_C_cor_1[THEN "\<rightarrow>E"] "\<forall>I" by fast

AOT_theorem betaC_1_a: \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<^bold>\<turnstile>\<^sub>\<box> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}\<close>
proof -
  AOT_modally_strict {
    AOT_assume \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<close>
    moreover AOT_have \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<down>\<close> and \<open>\<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>\<close>
      using calculation "cqt:5:a"[axiom_inst, THEN "\<rightarrow>E"] "&E" by blast+
    ultimately AOT_show \<open>\<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}\<close>
      using beta_C_cor_2[THEN "\<rightarrow>E", THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] by blast
  }
qed

AOT_theorem betaC_1_b: \<open>\<not>\<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n} \<^bold>\<turnstile>\<^sub>\<box> \<not>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<close>
  using betaC_1_a "raa-cor:3" by blast

lemmas "\<beta>\<rightarrow>C" = betaC_1_a betaC_1_b

AOT_theorem betaC_2_a: \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<down>, \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>, \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n} \<^bold>\<turnstile>\<^sub>\<box> [\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<close>
proof -
  AOT_modally_strict {
    AOT_assume 1: \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<down>\<close> and 2: \<open>\<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>\<close> and 3: \<open>\<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}\<close>
    AOT_hence \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<close>
      using beta_C_cor_2[THEN "\<rightarrow>E", OF 1, THEN "\<forall>E"(1), THEN "\<equiv>E"(2)] by blast
  }
  AOT_thus \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<down>, \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>, \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n} \<^bold>\<turnstile>\<^sub>\<box> [\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<close>
    by blast
qed

AOT_theorem betaC_2_b: \<open>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<down>, \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>, \<not>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<^bold>\<turnstile>\<^sub>\<box> \<not>\<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}\<close>
  using betaC_2_a "raa-cor:3" by blast

lemmas "\<beta>\<leftarrow>C" = betaC_2_a betaC_2_b

AOT_theorem eta_conversion_lemma1_1: \<open>\<Pi>\<down> \<rightarrow> [\<lambda>x\<^sub>1...x\<^sub>n [\<Pi>]x\<^sub>1...x\<^sub>n] = \<Pi>\<close>
  using "lambda-predicates:3"[axiom_inst] "\<forall>I" "\<forall>E"(1) "\<rightarrow>I" by fast

AOT_theorem eta_conversion_lemma1_2: \<open>\<Pi>\<down> \<rightarrow> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n [\<Pi>]\<nu>\<^sub>1...\<nu>\<^sub>n] = \<Pi>\<close>
  using eta_conversion_lemma1_1. (* TODO: spurious in the embedding *)

(* match (\<tau>) in "\<lambda>a . ?b" \<Rightarrow> \<open>match (\<tau>') in "\<lambda>a . ?b" \<Rightarrow> \<open>fail\<close>\<close> \<bar> _ \<Rightarrow> \<open> *)

AOT_theorem id_sym: assumes \<open>\<tau> = \<tau>'\<close> shows \<open>\<tau>' = \<tau>\<close>
  using "=E"[where \<phi>="\<lambda> \<tau>' . \<guillemotleft>\<tau>' = \<tau>\<guillemotright>", rotated 1, OF assms]
        "=I"(1)[OF "t=t-proper:1"[THEN "\<rightarrow>E", OF assms]] by auto

declare id_sym[sym]

AOT_theorem id_trans: assumes \<open>\<tau> = \<tau>'\<close> and \<open>\<tau>' = \<tau>''\<close> shows \<open>\<tau> = \<tau>''\<close>
proof -
  AOT_have \<open>\<forall>\<alpha>\<forall>\<beta>\<forall>\<gamma> (\<alpha> = \<beta> & \<beta> = \<gamma> \<rightarrow> \<alpha> = \<gamma>)\<close>
    apply (rule GEN)+
    by (fact "id-eq:3")
  AOT_hence \<open>(\<tau> = \<tau>' & \<tau>' = \<tau>'' \<rightarrow> \<tau> = \<tau>'')\<close>
    using "t=t-proper:1"[THEN "\<rightarrow>E", OF assms(1)]
        "t=t-proper:1"[THEN "\<rightarrow>E", OF assms(2)]
        "t=t-proper:2"[THEN "\<rightarrow>E", OF assms(2)]
          "\<forall>E"(1) by blast
  thus ?thesis using assms "&I" "\<rightarrow>E" by blast
qed

declare id_trans[trans]

method "\<eta>C" for \<Pi> :: \<open><'a::{AOT_Term_id_2,AOT_\<kappa>s}>\<close> = (match conclusion in "[v \<Turnstile> \<tau>{\<Pi>} = \<tau>'{\<Pi>}]" for v \<tau> \<tau>' \<Rightarrow> \<open>
rule "=E"[rotated 1, OF eta_conversion_lemma1_2[THEN "\<rightarrow>E", of v "\<guillemotleft>[\<Pi>]\<guillemotright>", symmetric]]
\<close>)
(*
AOT_theorem \<open>[\<lambda>y [\<lambda>z [P]z]y \<rightarrow> [\<lambda>u [S]u]y] = [\<lambda>y [P]y \<rightarrow> [S]y]\<close>
  apply ("\<eta>C" "\<guillemotleft>[P]\<guillemotright>") defer
   apply ("\<eta>C" "\<guillemotleft>[S]\<guillemotright>") defer
  oops
*)
(* TODO: proper representation of eta_conversion_lemma2 *)

AOT_theorem sub_des_lam_1: \<open>[\<lambda>z\<^sub>1...z\<^sub>n  \<chi>{z\<^sub>1...z\<^sub>n, \<^bold>\<iota>x \<phi>{x}}]\<down> & \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x} \<rightarrow> [\<lambda>z\<^sub>1...z\<^sub>n \<chi>{z\<^sub>1...z\<^sub>n, \<^bold>\<iota>x \<phi>{x}}] = [\<lambda>z\<^sub>1...z\<^sub>n \<chi>{z\<^sub>1...z\<^sub>n, \<^bold>\<iota>x \<psi>{x}}]\<close>
proof(rule "\<rightarrow>I")
  AOT_assume A: \<open>[\<lambda>z\<^sub>1...z\<^sub>n  \<chi>{z\<^sub>1...z\<^sub>n, \<^bold>\<iota>x \<phi>{x}}]\<down> & \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
  AOT_show \<open>[\<lambda>z\<^sub>1...z\<^sub>n \<chi>{z\<^sub>1...z\<^sub>n, \<^bold>\<iota>x \<phi>{x}}] = [\<lambda>z\<^sub>1...z\<^sub>n \<chi>{z\<^sub>1...z\<^sub>n, \<^bold>\<iota>x \<psi>{x}}]\<close>
    using "=E"[where \<phi>="\<lambda> \<tau> . \<guillemotleft>[\<lambda>z\<^sub>1...z\<^sub>n \<chi>{z\<^sub>1...z\<^sub>n, \<^bold>\<iota>x \<phi>{x}}] = [\<lambda>z\<^sub>1...z\<^sub>n \<chi>{z\<^sub>1...z\<^sub>n, \<tau>}]\<guillemotright>",
               OF "=I"(1)[OF A[THEN "&E"(1)]], OF A[THEN "&E"(2)]]
    by blast
qed

AOT_theorem sub_des_lam_2: \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x} \<rightarrow> \<chi>{\<^bold>\<iota>x \<phi>{x}} = \<chi>{\<^bold>\<iota>x \<psi>{x}}\<close> for \<chi> :: \<open>\<kappa> \<Rightarrow> \<o>\<close>
  using "=E"[where \<phi>="\<lambda> \<tau> . \<guillemotleft>\<chi>{\<^bold>\<iota>x \<phi>{x}} = \<chi>{\<tau>}\<guillemotright>", OF "=I"(1)[OF "log-prop-prop:2"]] "\<rightarrow>I" by blast

AOT_theorem prop_equiv: \<open>F = G \<equiv> \<forall>x (x[F] \<equiv> x[G])\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>F = G\<close>
  AOT_thus \<open>\<forall>x (x[F] \<equiv> x[G])\<close>
    by (rule "=E"[rotated]) (fact "oth-class-taut:3:a"[THEN GEN])
next
  AOT_assume \<open>\<forall>x (x[F] \<equiv> x[G])\<close>
  AOT_hence \<open>x[F] \<equiv> x[G]\<close> for x using "\<forall>E" by blast
  AOT_hence \<open>\<box>(x[F] \<equiv> x[G])\<close> for x using en_eq_6_1[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<forall>x \<box>(x[F] \<equiv> x[G])\<close> by (rule GEN)
  AOT_hence \<open>\<box>\<forall>x (x[F] \<equiv> x[G])\<close> using BF[THEN "\<rightarrow>E"] by fast
  AOT_thus "F = G" using "p-identity-thm2:1"[THEN "\<equiv>E"(2)] by blast
qed

AOT_theorem relations_1:
  assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close>
  shows \<open>\<exists>F \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> \<phi>{x\<^sub>1...x\<^sub>n})\<close>
  apply (rule "\<exists>I"(1)[where \<tau>="\<guillemotleft>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<guillemotright>"])
  using "cqt:2[lambda]"[OF assms, axiom_inst] beta_C_cor_2[THEN "\<rightarrow>E", THEN RN] by blast+

AOT_theorem relations_2:
  assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close>
  shows \<open>\<exists>F \<box>\<forall>x ([F]x \<equiv> \<phi>{x})\<close>
  using relations_1 assms by blast

AOT_theorem block_paradox_1: \<open>\<not>[\<lambda>x \<exists>G (x[G] & \<not>[G]x)]\<down>\<close>
proof(rule RAA(2))
  let ?\<phi>="\<lambda> \<tau>. \<guillemotleft>\<exists>G (\<tau>[G] & \<not>[G]\<tau>)\<guillemotright>"
  AOT_assume A: \<open>[\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>]\<down>\<close>
  AOT_have \<open>\<exists>x (A!x & \<forall>F (x[F] \<equiv> F = [\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>]))\<close>
    using "A-objects"[axiom_inst] by fast
  then AOT_obtain a where \<xi>: \<open>A!a & \<forall>F (a[F] \<equiv> F = [\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>])\<close>
    using "\<exists>E"[rotated] by blast
  AOT_show \<open>\<not>[\<lambda>x \<exists>G (x[G] & \<not>[G]x)]\<down>\<close>
  proof (rule "\<or>E"(1)[OF "exc-mid"]; rule "\<rightarrow>I")
    AOT_assume B: \<open>[\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>]a\<close>
    AOT_hence \<open>\<exists>G (a[G] & \<not>[G]a)\<close> using "\<beta>\<rightarrow>C" A by blast
    then AOT_obtain P where \<open>a[P] & \<not>[P]a\<close> using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>P = [\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>]\<close>
      using \<xi>[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] calculation[THEN "&E"(1)] by blast
    ultimately AOT_have \<open>\<not>[\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>]a\<close>
      using "=E" "&E"(2) by fast
    AOT_thus \<open>\<not>[\<lambda>x \<exists>G (x[G] & \<not>[G]x)]\<down>\<close> using B RAA by blast
  next
    AOT_assume B: \<open>\<not>[\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>]a\<close>
    AOT_hence \<open>\<not>\<exists>G (a[G] & \<not>[G]a)\<close> using "\<beta>\<leftarrow>C" "cqt:2[const_var]"[of a, axiom_inst] A by blast
    AOT_hence C: \<open>\<forall>G \<not>(a[G] & \<not>[G]a)\<close> using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
    AOT_have \<open>\<forall>G (a[G] \<rightarrow> [G]a)\<close>
      by (AOT_subst "\<lambda> \<Pi> . \<guillemotleft>a[\<Pi>] \<rightarrow> [\<Pi>]a\<guillemotright>" "\<lambda> \<Pi> . \<guillemotleft>\<not>(a[\<Pi>] & \<not>[\<Pi>]a)\<guillemotright>")
         (auto simp: "oth-class-taut:1:a" C)
    AOT_hence \<open>a[\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>] \<rightarrow> [\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>]a\<close> using "\<forall>E" A by blast
    moreover AOT_have \<open>a[\<lambda>x \<guillemotleft>?\<phi> x\<guillemotright>]\<close> using \<xi>[THEN "&E"(2), THEN "\<forall>E"(1), OF A, THEN "\<equiv>E"(2)]
      using "=I"(1)[OF A] by blast
    ultimately AOT_show \<open>\<not>[\<lambda>x \<exists>G (x[G] & \<not>[G]x)]\<down>\<close> using B "\<rightarrow>E" RAA by blast
  qed
qed(simp)

AOT_theorem block_paradox_2: \<open>\<not>\<exists>F \<forall>x([F]x \<equiv> \<exists>G(x[G] & \<not>[G]x))\<close>
proof(rule RAA(2))
  AOT_assume \<open>\<exists>F \<forall>x ([F]x \<equiv> \<exists>G (x[G] & \<not>[G]x))\<close>
  then AOT_obtain F where F_prop: \<open>\<forall>x ([F]x \<equiv> \<exists>G (x[G] & \<not>[G]x))\<close> using "\<exists>E"[rotated] by blast
  AOT_have \<open>\<exists>x (A!x & \<forall>G (x[G] \<equiv> G = F))\<close>
    using "A-objects"[axiom_inst] by fast
  then AOT_obtain a where \<xi>: \<open>A!a & \<forall>G (a[G] \<equiv> G = F)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_show \<open>\<not>\<exists>F \<forall>x([F]x \<equiv> \<exists>G(x[G] & \<not>[G]x))\<close>
  proof (rule "\<or>E"(1)[OF "exc-mid"]; rule "\<rightarrow>I")
    AOT_assume B: \<open>[F]a\<close>
    AOT_hence \<open>\<exists>G (a[G] & \<not>[G]a)\<close> using F_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by blast
    then AOT_obtain P where \<open>a[P] & \<not>[P]a\<close> using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>P = F\<close>
      using \<xi>[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] calculation[THEN "&E"(1)] by blast
    ultimately AOT_have \<open>\<not>[F]a\<close>
      using "=E" "&E"(2) by fast
    AOT_thus \<open>\<not>\<exists>F \<forall>x([F]x \<equiv> \<exists>G(x[G] & \<not>[G]x))\<close> using B RAA by blast
  next
    AOT_assume B: \<open>\<not>[F]a\<close>
    AOT_hence \<open>\<not>\<exists>G (a[G] & \<not>[G]a)\<close>
      using "oth-class-taut:4:b"[THEN "\<equiv>E"(1), OF F_prop[THEN "\<forall>E"(2)[of _ _ a]], THEN "\<equiv>E"(1)] by simp
    AOT_hence C: \<open>\<forall>G \<not>(a[G] & \<not>[G]a)\<close> using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
    AOT_have \<open>\<forall>G (a[G] \<rightarrow> [G]a)\<close>
      by (AOT_subst "\<lambda> \<Pi> . \<guillemotleft>a[\<Pi>] \<rightarrow> [\<Pi>]a\<guillemotright>" "\<lambda> \<Pi> . \<guillemotleft>\<not>(a[\<Pi>] & \<not>[\<Pi>]a)\<guillemotright>")
         (auto simp: "oth-class-taut:1:a" C)
    AOT_hence \<open>a[F] \<rightarrow> [F]a\<close> using "\<forall>E" by blast
    moreover AOT_have \<open>a[F]\<close> using \<xi>[THEN "&E"(2), THEN "\<forall>E"(2), of F, THEN "\<equiv>E"(2)]
      using "=I"(2) by blast
    ultimately AOT_show \<open>\<not>\<exists>F \<forall>x([F]x \<equiv> \<exists>G(x[G] & \<not>[G]x))\<close> using B "\<rightarrow>E" RAA by blast
  qed
qed(simp)

AOT_theorem block_paradox_3: \<open>\<not>\<forall>y [\<lambda>z z = y]\<down>\<close>
proof(rule RAA(2))
  AOT_assume \<theta>: \<open>\<forall>y [\<lambda>z z = y]\<down>\<close>
  AOT_have \<open>\<exists>x (A!x & \<forall>F (x[F] \<equiv> \<exists>y(F = [\<lambda>z z = y] & \<not>y[F])))\<close>
    using "A-objects"[axiom_inst] by force
  then AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<exists>y (F = [\<lambda>z z = y] & \<not>y[F]))\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<zeta>: \<open>a[\<lambda>z z = a] \<equiv> \<exists>y ([\<lambda>z z = a] = [\<lambda>z z = y] & \<not>y[\<lambda>z z = a])\<close>
    using \<theta>[THEN "\<forall>E"(2)] a_prop[THEN "&E"(2), THEN "\<forall>E"(1)] by blast
  AOT_show \<open>\<not>\<forall>y [\<lambda>z z = y]\<down>\<close>
  proof (rule "\<or>E"(1)[OF "exc-mid"]; rule "\<rightarrow>I")
    AOT_assume A: \<open>a[\<lambda>z z = a]\<close>
    AOT_hence \<open>\<exists>y ([\<lambda>z z = a] = [\<lambda>z z = y] & \<not>y[\<lambda>z z = a])\<close>
      using \<zeta>[THEN "\<equiv>E"(1)] by blast
    then AOT_obtain b where b_prop: \<open>[\<lambda>z z = a] = [\<lambda>z z = b] & \<not>b[\<lambda>z z = a]\<close>
      using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>a = a\<close> by (rule "=I")
    moreover AOT_have \<open>[\<lambda>z z = a]\<down>\<close> using \<theta> "\<forall>E" by blast
    moreover AOT_have \<open>a\<down>\<close> using "cqt:2[const_var]"[axiom_inst] .
    ultimately AOT_have \<open>[\<lambda>z z = a]a\<close> using "\<beta>\<leftarrow>C" by blast
    AOT_hence \<open>[\<lambda>z z = b]a\<close> using "=E" b_prop[THEN "&E"(1)] by fast
    AOT_hence \<open>a = b\<close> using "\<beta>\<rightarrow>C" by blast
    AOT_hence \<open>b[\<lambda>z z = a]\<close> using A "=E" by fast
    AOT_thus \<open>\<not>\<forall>y [\<lambda>z z = y]\<down>\<close> using b_prop[THEN "&E"(2)] RAA by blast
  next
    AOT_assume A: \<open>\<not>a[\<lambda>z z = a]\<close>
    AOT_hence \<open>\<not>\<exists>y ([\<lambda>z z = a] = [\<lambda>z z = y] & \<not>y[\<lambda>z z = a])\<close>
      using \<zeta> "oth-class-taut:4:b"[THEN "\<equiv>E"(1), THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<forall>y \<not>([\<lambda>z z = a] = [\<lambda>z z = y] & \<not>y[\<lambda>z z = a])\<close>
      using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<not>([\<lambda>z z = a] = [\<lambda>z z = a] & \<not>a[\<lambda>z z = a])\<close>
      using "\<forall>E" by blast
    AOT_hence \<open>[\<lambda>z z = a] = [\<lambda>z z = a] \<rightarrow> a[\<lambda>z z = a]\<close>
      by (metis "&I" "deduction-theorem" "raa-cor:4")
    AOT_hence \<open>a[\<lambda>z z = a]\<close> using "=I"(1) \<theta>[THEN "\<forall>E"(2)] "\<rightarrow>E" by blast
    AOT_thus \<open>\<not>\<forall>y [\<lambda>z z = y]\<down>\<close> using A RAA by blast
  qed
qed(simp)

AOT_theorem block_paradox_4: \<open>\<not>\<forall>y \<exists>F \<forall>x([F]x \<equiv> x = y)\<close>
proof(rule RAA(2))
  AOT_assume \<theta>: \<open>\<forall>y \<exists>F \<forall>x([F]x \<equiv> x = y)\<close>
  AOT_have \<open>\<exists>x (A!x & \<forall>F (x[F] \<equiv> \<exists>z (\<forall>y([F]y \<equiv> y = z) & \<not>z[F])))\<close>
    using "A-objects"[axiom_inst] by force
  then AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<exists>z (\<forall>y([F]y \<equiv> y = z) & \<not>z[F]))\<close>
    using "\<exists>E"[rotated] by blast
  AOT_obtain F where F_prop: \<open>\<forall>x ([F]x \<equiv> x = a)\<close> using \<theta>[THEN "\<forall>E"(2)] "\<exists>E"[rotated] by blast
  AOT_have \<zeta>: \<open>a[F] \<equiv> \<exists>z (\<forall>y ([F]y \<equiv> y = z) & \<not>z[F])\<close>
    using a_prop[THEN "&E"(2), THEN "\<forall>E"(2)] by blast
  AOT_show \<open>\<not>\<forall>y \<exists>F \<forall>x([F]x \<equiv> x = y)\<close>
  proof (rule "\<or>E"(1)[OF "exc-mid"]; rule "\<rightarrow>I")
    AOT_assume A: \<open>a[F]\<close>
    AOT_hence \<open>\<exists>z (\<forall>y ([F]y \<equiv> y = z) & \<not>z[F])\<close>
      using \<zeta>[THEN "\<equiv>E"(1)] by blast
    then AOT_obtain b where b_prop: \<open>\<forall>y ([F]y \<equiv> y = b) & \<not>b[F]\<close>
      using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>[F]a\<close> using F_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] "=I"(2) by blast
    ultimately AOT_have \<open>a = b\<close> using "\<forall>E"(2) "\<equiv>E"(1) "&E" by fast
    AOT_hence \<open>a = b\<close> using "\<beta>\<rightarrow>C" by blast
    AOT_hence \<open>b[F]\<close> using A "=E" by fast
    AOT_thus \<open>\<not>\<forall>y \<exists>F \<forall>x([F]x \<equiv> x = y)\<close> using b_prop[THEN "&E"(2)] RAA by blast
  next
    AOT_assume A: \<open>\<not>a[F]\<close>
    AOT_hence \<open>\<not>\<exists>z (\<forall>y ([F]y \<equiv> y = z) & \<not>z[F])\<close>
      using \<zeta> "oth-class-taut:4:b"[THEN "\<equiv>E"(1), THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<forall>z \<not>(\<forall>y ([F]y \<equiv> y = z) & \<not>z[F])\<close>
      using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<not>(\<forall>y ([F]y \<equiv> y = a) & \<not>a[F])\<close>
      using "\<forall>E" by blast
    AOT_hence \<open>\<forall>y ([F]y \<equiv> y = a) \<rightarrow> a[F]\<close>
      by (metis "&I" "deduction-theorem" "raa-cor:4")
    AOT_hence \<open>a[F]\<close> using F_prop "\<rightarrow>E" by blast
    AOT_thus \<open>\<not>\<forall>y \<exists>F \<forall>x([F]x \<equiv> x = y)\<close> using A RAA by blast
  qed
qed(simp)

AOT_theorem block_paradox_5_wrong: \<open>\<forall>x\<forall>y\<exists>F ([F]xy \<equiv> x = y)\<close>
proof (rule "\<forall>I")+
  fix x y
  AOT_show \<open>\<exists>F ([F]xy \<equiv> x = y)\<close>
  proof (rule "\<or>E"(1)[OF "exc-mid"]; rule "\<rightarrow>I")
    AOT_assume 0: \<open>x = y\<close>
    AOT_have A: \<open>[\<lambda>xy \<forall>p (p \<rightarrow> p)]\<down>\<close>
      by "cqt:2[lambda]"
    AOT_have \<open>[\<lambda>xy \<forall>p (p \<rightarrow> p)]xy\<close>
      apply (rule "\<beta>\<leftarrow>C"(1))
      using A apply blast
      using "cqt:2[const_var]"[of "x", axiom_inst] "cqt:2[const_var]"[of "y", axiom_inst]
       apply (simp add: prod_denotesI "&I")
      using "if-p-then-p" "\<forall>I" by fast
    AOT_hence \<open>[\<lambda>xy \<forall>p (p \<rightarrow> p)]xy \<equiv> x = y\<close>
      using 0 "\<equiv>I" "vdash-properties:9" "\<rightarrow>I" by blast
    AOT_thus \<open>\<exists>F ([F]xy \<equiv> x = y)\<close>
      using A "\<exists>I" by fast
  next
    AOT_assume 0: \<open>\<not>(x = y)\<close>
    AOT_have A: \<open>[\<lambda>xy \<exists>p (p & \<not>p)]\<down>\<close>
      by "cqt:2[lambda]"
    AOT_have 1: \<open>\<not>[\<lambda>xy \<exists>p (p & \<not>p)]xy\<close>
      apply (rule "\<beta>\<rightarrow>C"(2)) apply simp
      by (meson "instantiation" "raa-cor:1")
    AOT_have \<open>\<not>[\<lambda>xy \<exists>p (p & \<not>p)]xy \<equiv> \<not>(x = y)\<close>
      using "\<equiv>I"[OF "vdash-properties:9"[OF 0], OF "vdash-properties:9"[OF 1]]
      by blast
    AOT_hence \<open>[\<lambda>xy \<exists>p (p & \<not>p)]xy \<equiv> (x = y)\<close>
      using "oth-class-taut:4:b"[THEN "\<equiv>E"(2)] by blast
    AOT_thus \<open>\<exists>F ([F]xy \<equiv> x = y)\<close>
      using A "\<exists>I" by fast
  qed
qed

(* TODO[IMPORTANT]: this is supposedly the correct version *)
AOT_theorem block_paradox_5: \<open>\<not>\<exists>F\<forall>x\<forall>y([F]xy \<equiv> y = x)\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>\<exists>F\<forall>x\<forall>y([F]xy \<equiv> y = x)\<close>
  then AOT_obtain F where F_prop: \<open>\<forall>x\<forall>y([F]xy \<equiv> y = x)\<close> using "\<exists>E"[rotated] by blast
  {
    fix x
    AOT_have 1: \<open>\<forall>y([F]xy \<equiv> y = x)\<close> using F_prop "\<forall>E" by blast
    AOT_have 2: \<open>[\<lambda>z [F]xz]\<down>\<close> by "cqt:2[lambda]"
    moreover AOT_have \<open>\<forall>y([\<lambda>z [F]xz]y \<equiv> y = x)\<close>
    proof(rule "\<forall>I")
      fix y
      AOT_have \<open>[\<lambda>z [F]xz]y \<equiv> [F]xy\<close>
        using beta_C_meta[THEN "\<rightarrow>E"] 2 by fast
      also AOT_have \<open>... \<equiv> y = x\<close> using 1 "\<forall>E"
        by fast
      finally AOT_show \<open>[\<lambda>z [F]xz]y \<equiv> y = x\<close>.
    qed
    ultimately AOT_have \<open>\<exists>F\<forall>y([F]y \<equiv> y = x)\<close>
      using "\<exists>I" by fast
  }
  AOT_hence \<open>\<forall>x\<exists>F\<forall>y([F]y \<equiv> y = x)\<close>
    by (rule GEN)
  AOT_thus \<open>\<forall>x\<exists>F\<forall>y([F]y \<equiv> y = x) & \<not>\<forall>x\<exists>F\<forall>y([F]y \<equiv> y = x)\<close>
    using "&I" block_paradox_4 by blast
qed

AOT_act_theorem block_paradox2_1: \<open>\<forall>x [G]x \<rightarrow> \<not>[\<lambda>x [G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))]\<down>\<close>
proof(rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_assume antecedant: \<open>\<forall>x [G]x\<close>
  AOT_have Lemma: \<open>\<forall>x ([G]\<^bold>\<iota>y(y = x & \<exists>H (x[H] & \<not>[H]x)) \<equiv> \<exists>H (x[H] & \<not>[H]x))\<close>
  proof(rule GEN)
    fix x
    AOT_have A: \<open>[G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x)) \<equiv> \<exists>!y (y = x & \<exists>H (x[H] & \<not>[H]x))\<close>
    proof(rule "\<equiv>I"; rule "\<rightarrow>I")
      AOT_assume \<open>[G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))\<close>
      AOT_hence \<open>\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))\<down>\<close>
        using "cqt:5:a"[axiom_inst, THEN "\<rightarrow>E", THEN "&E"(2)] by blast
      AOT_thus \<open>\<exists>!y (y = x & \<exists>H (x[H] & \<not>[H]x))\<close>
        using "1-exists:1"[THEN "\<equiv>E"(1)] by blast
    next
      AOT_assume A: \<open>\<exists>!y (y = x & \<exists>H (x[H] & \<not>[H]x))\<close>
      AOT_obtain a where a_1: \<open>a = x & \<exists>H (x[H] & \<not>[H]x)\<close> and a_2: \<open>\<forall>z (z = x & \<exists>H (x[H] & \<not>[H]x) \<rightarrow> z = a)\<close>
        using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF A] "&E" "\<exists>E"[rotated] by blast
      AOT_have a_3: \<open>[G]a\<close>
        using antecedant "\<forall>E" by blast
      AOT_show \<open>[G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))\<close>
        apply (rule "russell-axiom[exe,1].russell-axiom"[THEN "\<equiv>E"(2)])
        apply (rule "\<exists>I"(2))
        using a_1 a_2 a_3 "&I" by blast
    qed
    also AOT_have B: \<open>... \<equiv> \<exists>H (x[H] & \<not>[H]x)\<close>
    proof (rule "\<equiv>I"; rule "\<rightarrow>I")
      AOT_assume A: \<open>\<exists>!y (y = x & \<exists>H (x[H] & \<not>[H]x))\<close>
      AOT_obtain a where \<open>a = x & \<exists>H (x[H] & \<not>[H]x)\<close>
        using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF A] "&E" "\<exists>E"[rotated] by blast
      AOT_thus \<open>\<exists>H (x[H] & \<not>[H]x)\<close> using "&E" by blast
    next
      AOT_assume \<open>\<exists>H (x[H] & \<not>[H]x)\<close>
      AOT_hence \<open>x = x & \<exists>H (x[H] & \<not>[H]x)\<close>
        using "id-eq:1" "&I" by blast
      moreover AOT_have \<open>\<forall>z (z = x & \<exists>H (x[H] & \<not>[H]x) \<rightarrow> z = x)\<close>
        by (simp add: "Conjunction Simplification"(1) "universal-cor")
      ultimately AOT_show \<open>\<exists>!y (y = x & \<exists>H (x[H] & \<not>[H]x))\<close>
        using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "\<exists>I"(2) by fast
    qed
    finally AOT_show \<open>([G]\<^bold>\<iota>y(y = x & \<exists>H (x[H] & \<not>[H]x)) \<equiv> \<exists>H (x[H] & \<not>[H]x))\<close> .
  qed

  AOT_assume A: \<open>[\<lambda>x [G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))]\<down>\<close>
  AOT_have \<theta>: \<open>\<forall>x ([\<lambda>x [G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))]x \<equiv> [G]\<^bold>\<iota>y(y = x & \<exists>H (x[H] & \<not>[H]x)))\<close>
    using beta_C_meta[THEN "\<rightarrow>E", OF A] "\<forall>I" by fast
  AOT_have \<open>\<forall>x ([\<lambda>x [G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))]x \<equiv> \<exists>H (x[H] & \<not>[H]x))\<close>
    using \<theta> Lemma "cqt-basic:10"[THEN "\<rightarrow>E"] "&I" by fast
  AOT_hence \<open>\<exists>F \<forall>x ([F]x \<equiv> \<exists>H (x[H] & \<not>[H]x))\<close>
    using "\<exists>I"(1) A by fast
  AOT_thus \<open>(\<exists>F \<forall>x ([F]x \<equiv> \<exists>H (x[H] & \<not>[H]x))) & (\<not>\<exists>F \<forall>x ([F]x \<equiv> \<exists>H (x[H] & \<not>[H]x)))\<close>
    using block_paradox_2 "&I" by blast
qed

AOT_act_theorem block_paradox2_2: \<open>\<exists>G \<not>[\<lambda>x [G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))]\<down>\<close>
proof(rule "\<exists>I"(1))
  AOT_have 0: \<open>[\<lambda>x \<forall>p (p \<rightarrow>p)]\<down>\<close>
    by "cqt:2[lambda]"
  moreover AOT_have \<open>\<forall>x [\<lambda>x \<forall>p (p \<rightarrow>p)]x\<close>
    apply (rule GEN)
    apply (rule beta_C_cor_2[THEN "\<rightarrow>E", OF 0, THEN "\<forall>E"(2), THEN "\<equiv>E"(2)])
    using "if-p-then-p" GEN by fast
  moreover AOT_have \<open>\<forall>G (\<forall>x [G]x \<rightarrow> \<not>[\<lambda>x [G]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))]\<down>)\<close>
      using block_paradox2_1 "\<forall>I" by fast
  ultimately AOT_show \<open>\<not>[\<lambda>x [\<lambda>x \<forall>p (p \<rightarrow>p)]\<^bold>\<iota>y (y = x & \<exists>H (x[H] & \<not>[H]x))]\<down>\<close>
    using "\<forall>E"(1) "\<rightarrow>E" by blast
qed("cqt:2[lambda]")

AOT_theorem propositions: \<open>\<exists>p \<box>(p \<equiv> \<phi>)\<close>
proof(rule "\<exists>I"(1))
  AOT_show \<open>\<box>(\<phi> \<equiv> \<phi>)\<close>
    by (simp add: RN "oth-class-taut:3:a")
next
  AOT_show \<open>\<phi>\<down>\<close>
    by (simp add: "log-prop-prop:2")
qed

AOT_theorem pos_not_equiv_ne_1: \<open>(\<diamond>\<not>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> [G]x\<^sub>1...x\<^sub>n)) \<rightarrow> F \<noteq> G\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>\<diamond>\<not>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> [G]x\<^sub>1...x\<^sub>n)\<close>
  AOT_hence \<open>\<not>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> [G]x\<^sub>1...x\<^sub>n)\<close>
    using "KBasic:11"[THEN "\<equiv>E"(2)] by blast
  AOT_hence \<open>\<not>(F = G)\<close>
    using "id-rel-nec-equiv:1" "modus-tollens:1" by blast
  AOT_thus \<open>F \<noteq> G\<close>
    using "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

AOT_theorem pos_not_equiv_ne_2: \<open>(\<diamond>\<not>(\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> F \<noteq> G\<close>
proof (rule "\<rightarrow>I")
  AOT_modally_strict {
    AOT_have \<open>\<not>(\<phi>{F} \<equiv> \<phi>{G}) \<rightarrow> \<not>(F = G)\<close>
    proof (rule "\<rightarrow>I"; rule "raa-cor:2")
      AOT_assume 1: \<open>F = G\<close>
      AOT_hence \<open>\<phi>{F} \<rightarrow> \<phi>{G}\<close> using "l-identity"[axiom_inst, THEN "\<rightarrow>E"] by blast
      moreover {
        AOT_have \<open>G = F\<close> using 1 id_sym by blast
        AOT_hence \<open>\<phi>{G} \<rightarrow> \<phi>{F}\<close> using "l-identity"[axiom_inst, THEN "\<rightarrow>E"] by blast
      }
      ultimately AOT_have \<open>\<phi>{F} \<equiv> \<phi>{G}\<close> using "\<equiv>I" by blast
      moreover AOT_assume \<open>\<not>(\<phi>{F} \<equiv> \<phi>{G})\<close>
      ultimately AOT_show \<open>(\<phi>{F} \<equiv> \<phi>{G}) & \<not>(\<phi>{F} \<equiv> \<phi>{G})\<close>
        using "&I" by blast
    qed
  }
  AOT_hence \<open>\<diamond>\<not>(\<phi>{F} \<equiv> \<phi>{G}) \<rightarrow> \<diamond>\<not>(F = G)\<close>
    using "RM:2[prem]" by blast
  moreover AOT_assume \<open>\<diamond>\<not>(\<phi>{F} \<equiv> \<phi>{G})\<close>
  ultimately AOT_have 0: \<open>\<diamond>\<not>(F = G)\<close> using "\<rightarrow>E" by blast
  AOT_have \<open>\<diamond>(F \<noteq> G)\<close>
    by (AOT_subst "\<guillemotleft>F \<noteq> G\<guillemotright>" "\<guillemotleft>\<not>(F = G)\<guillemotright>")
       (auto simp: "=-infix" "\<equiv>Df" 0)
  AOT_thus \<open>F \<noteq> G\<close>
    using id_nec2_3[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem pos_not_equiv_ne_2_0: \<open>(\<diamond>\<not>(\<phi>{p} \<equiv> \<phi>{q})) \<rightarrow> p \<noteq> q\<close>
proof (rule "\<rightarrow>I")
  AOT_modally_strict {
    AOT_have \<open>\<not>(\<phi>{p} \<equiv> \<phi>{q}) \<rightarrow> \<not>(p = q)\<close>
    proof (rule "\<rightarrow>I"; rule "raa-cor:2")
      AOT_assume 1: \<open>p = q\<close>
      AOT_hence \<open>\<phi>{p} \<rightarrow> \<phi>{q}\<close> using "l-identity"[axiom_inst, THEN "\<rightarrow>E"] by blast
      moreover {
        AOT_have \<open>q = p\<close> using 1 id_sym by blast
        AOT_hence \<open>\<phi>{q} \<rightarrow> \<phi>{p}\<close> using "l-identity"[axiom_inst, THEN "\<rightarrow>E"] by blast
      }
      ultimately AOT_have \<open>\<phi>{p} \<equiv> \<phi>{q}\<close> using "\<equiv>I" by blast
      moreover AOT_assume \<open>\<not>(\<phi>{p} \<equiv> \<phi>{q})\<close>
      ultimately AOT_show \<open>(\<phi>{p} \<equiv> \<phi>{q}) & \<not>(\<phi>{p} \<equiv> \<phi>{q})\<close>
        using "&I" by blast
    qed
  }
  AOT_hence \<open>\<diamond>\<not>(\<phi>{p} \<equiv> \<phi>{q}) \<rightarrow> \<diamond>\<not>(p = q)\<close>
    using "RM:2[prem]" by blast
  moreover AOT_assume \<open>\<diamond>\<not>(\<phi>{p} \<equiv> \<phi>{q})\<close>
  ultimately AOT_have 0: \<open>\<diamond>\<not>(p = q)\<close> using "\<rightarrow>E" by blast
  AOT_have \<open>\<diamond>(p \<noteq> q)\<close>
    by (AOT_subst "\<guillemotleft>p \<noteq> q\<guillemotright>" "\<guillemotleft>\<not>(p = q)\<guillemotright>")
       (auto simp: 0 "=-infix" "\<equiv>Df")
  AOT_thus \<open>p \<noteq> q\<close>
    using id_nec2_3[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem pos_not_equiv_ne_3: \<open>(\<not>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> [G]x\<^sub>1...x\<^sub>n)) \<rightarrow> F \<noteq> G\<close>
  using "\<rightarrow>I" pos_not_equiv_ne_1[THEN "\<rightarrow>E"] "T\<diamond>"[THEN "\<rightarrow>E"] by blast

AOT_theorem pos_not_equiv_ne_4: \<open>(\<not>(\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> F \<noteq> G\<close>
  using "\<rightarrow>I" pos_not_equiv_ne_2[THEN "\<rightarrow>E"] "T\<diamond>"[THEN "\<rightarrow>E"] by blast

AOT_theorem pos_not_equiv_ne_4_0: \<open>(\<not>(\<phi>{p} \<equiv> \<phi>{q})) \<rightarrow> p \<noteq> q\<close>
  using "\<rightarrow>I" pos_not_equiv_ne_2_0[THEN "\<rightarrow>E"] "T\<diamond>"[THEN "\<rightarrow>E"] by blast

AOT_define relation_negation :: "\<Pi> \<Rightarrow> \<Pi>" ("_\<^sup>-")
  df_relation_negation: "[F]\<^sup>- =\<^sub>d\<^sub>f [\<lambda>x\<^sub>1...x\<^sub>n \<not>[F]x\<^sub>1...x\<^sub>n]"

nonterminal \<phi>neg
syntax "" :: "\<phi>neg \<Rightarrow> \<tau>" ("_")
syntax "" :: "\<phi>neg \<Rightarrow> \<phi>" ("'(_')")

AOT_define relation_negation_0 :: \<open>\<phi> \<Rightarrow> \<phi>neg\<close> ("'(_')\<^sup>-")
  df_relation_negation_0: "(p)\<^sup>- =\<^sub>d\<^sub>f [\<lambda> \<not>p]"

AOT_theorem rel_neg_T_1: \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<not>[\<Pi>]x\<^sub>1...x\<^sub>n]\<down>\<close>
  by "cqt:2[lambda]"

AOT_theorem rel_neg_T_1_0: \<open>[\<lambda> \<not>\<phi>]\<down>\<close>
  using "cqt:2[lambda0]"[axiom_inst] by blast

AOT_theorem rel_neg_T_2: \<open>[\<Pi>]\<^sup>- = [\<lambda>x\<^sub>1...x\<^sub>n \<not>[\<Pi>]x\<^sub>1...x\<^sub>n]\<close>
  using "=I"(1)[OF rel_neg_T_1]
  by (rule "=\<^sub>d\<^sub>fI"(1)[OF df_relation_negation, OF rel_neg_T_1])

AOT_theorem rel_neg_T_2_0: \<open>(\<phi>)\<^sup>- = [\<lambda> \<not>\<phi>]\<close>
  using "=I"(1)[OF rel_neg_T_1_0]
  by (rule "=\<^sub>d\<^sub>fI"(1)[OF df_relation_negation_0, OF rel_neg_T_1_0])

AOT_theorem rel_neg_T_3: \<open>[\<Pi>]\<^sup>-\<down>\<close>
  using "=\<^sub>d\<^sub>fI"(1)[OF df_relation_negation, OF rel_neg_T_1] rel_neg_T_1 by blast

AOT_theorem rel_neg_T_3_0: \<open>(\<phi>)\<^sup>-\<down>\<close>
  using "log-prop-prop:2" by blast
(*  using "=\<^sub>d\<^sub>fI"(1)[OF df_relation_negation_0, OF rel_neg_T_1_0] rel_neg_T_1_0 by blast *)

(* Note: PLM states the zero place case twice *)
AOT_theorem thm_relation_negation_1: \<open>[F]\<^sup>-x\<^sub>1...x\<^sub>n \<equiv> \<not>[F]x\<^sub>1...x\<^sub>n\<close>
proof -
  AOT_have \<open>[F]\<^sup>-x\<^sub>1...x\<^sub>n \<equiv> [\<lambda>x\<^sub>1...x\<^sub>n \<not>[F]x\<^sub>1...x\<^sub>n]x\<^sub>1...x\<^sub>n\<close>
    using "=E"[rotated, OF rel_neg_T_2] "=E"[rotated, OF rel_neg_T_2[THEN id_sym]]
    "\<rightarrow>I" "\<equiv>I" by fast
  also AOT_have \<open>... \<equiv> \<not>[F]x\<^sub>1...x\<^sub>n\<close>
    using beta_C_meta[THEN "\<rightarrow>E", OF rel_neg_T_1] by fast
  finally show ?thesis.
qed

AOT_theorem thm_relation_negation_2: \<open>\<not>[F]\<^sup>-x\<^sub>1...x\<^sub>n \<equiv> [F]x\<^sub>1...x\<^sub>n\<close>
  apply (AOT_subst "\<guillemotleft>[F]x\<^sub>1...x\<^sub>n\<guillemotright>" "\<guillemotleft>\<not>\<not>[F]x\<^sub>1...x\<^sub>n\<guillemotright>")
   apply (simp add: "oth-class-taut:3:b")
  apply (rule "oth-class-taut:4:b"[THEN "\<equiv>E"(1)])
  using thm_relation_negation_1.

AOT_theorem thm_relation_negation_3: \<open>((p)\<^sup>-) \<equiv> \<not>p\<close>
proof -
  AOT_have \<open>(p)\<^sup>- = [\<lambda> \<not>p]\<close> using rel_neg_T_2_0 by blast
  AOT_hence \<open>((p)\<^sup>-) \<equiv> [\<lambda> \<not>p]\<close>
    using df_relation_negation_0 "log-prop-prop:2" "oth-class-taut:3:a" "rule-id-def:2:a" by blast
  also AOT_have \<open>[\<lambda> \<not>p] \<equiv> \<not>p\<close>
    by (simp add: "propositions-lemma:2")
  finally show ?thesis.
qed

AOT_theorem thm_relation_negation_4: \<open>(\<not>((p)\<^sup>-)) \<equiv> p\<close>
  using thm_relation_negation_3[THEN "\<equiv>E"(1)]
        thm_relation_negation_3[THEN "\<equiv>E"(2)]
        "\<equiv>I" "\<rightarrow>I" RAA by metis

AOT_theorem thm_relation_negation_5: \<open>[F] \<noteq> [F]\<^sup>-\<close>
proof -
  AOT_have \<open>\<not>([F] = [F]\<^sup>-)\<close>
  proof (rule RAA(2))
    AOT_show \<open>[F]x\<^sub>1...x\<^sub>n \<rightarrow> [F]x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n
      using "if-p-then-p".
  next
    AOT_assume \<open>[F] = [F]\<^sup>-\<close>
    AOT_hence \<open>[F]\<^sup>- = [F]\<close> using id_sym by blast
    AOT_hence \<open>[F]x\<^sub>1...x\<^sub>n \<equiv> \<not>[F]x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n
      using "=E" thm_relation_negation_1 by fast
    AOT_thus \<open>\<not>([F]x\<^sub>1...x\<^sub>n \<rightarrow> [F]x\<^sub>1...x\<^sub>n)\<close> for x\<^sub>1x\<^sub>n
      using "\<equiv>E" RAA by metis
  qed
  thus ?thesis
    using "\<equiv>\<^sub>d\<^sub>fI" "=-infix" by blast
qed

AOT_theorem thm_relation_negation_6: \<open>p \<noteq> (p)\<^sup>-\<close>
proof -
  AOT_have \<open>\<not>(p = (p)\<^sup>-)\<close>
  proof (rule RAA(2))
    AOT_show \<open>p \<rightarrow> p\<close>
      using "if-p-then-p".
  next
    AOT_assume \<open>p = (p)\<^sup>-\<close>
    AOT_hence \<open>(p)\<^sup>- = p\<close> using id_sym by blast
    AOT_hence \<open>p \<equiv> \<not>p\<close>
      using "=E" thm_relation_negation_3 by fast
    AOT_thus \<open>\<not>(p \<rightarrow> p)\<close>
      using "\<equiv>E" RAA by metis
  qed
  thus ?thesis
    using "\<equiv>\<^sub>d\<^sub>fI" "=-infix" by blast
qed

AOT_theorem thm_relation_negation_7: \<open>(p)\<^sup>- = (\<not>p)\<close>
  apply (rule df_relation_negation_0[THEN "=\<^sub>d\<^sub>fE"(1)])
  using "cqt:2[lambda0]"[axiom_inst] rel_neg_T_2_0 "propositions-lemma:1" id_trans by blast+

AOT_theorem thm_relation_negation_8: \<open>p = q \<rightarrow> (\<not>p) = (\<not>q)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>p = q\<close>
  moreover AOT_have \<open>(\<not>p)\<down>\<close> using "log-prop-prop:2".
  moreover AOT_have \<open>(\<not>p) = (\<not>p)\<close> using calculation(2) "=I" by blast
  ultimately AOT_show \<open>(\<not>p) = (\<not>q)\<close>
    using "=E" by fast
qed

AOT_theorem thm_relation_negation_9: \<open>p = q \<rightarrow> (p)\<^sup>- = (q)\<^sup>-\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>p = q\<close>
  AOT_hence \<open>(\<not>p) = (\<not>q)\<close> using thm_relation_negation_8 "\<rightarrow>E" by blast
  AOT_thus \<open>(p)\<^sup>- = (q)\<^sup>-\<close>
    using thm_relation_negation_7 id_sym id_trans by metis
qed

AOT_define Necessary :: \<open>\<Pi> \<Rightarrow> \<phi>\<close> ("Necessary'(_')")
  contingent_properties_1: \<open>Necessary([F]) \<equiv>\<^sub>d\<^sub>f \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]x\<^sub>1...x\<^sub>n\<close>

AOT_define Necessary0 :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("Necessary0'(_')")
  contingent_properties_1_0: \<open>Necessary0(p) \<equiv>\<^sub>d\<^sub>f \<box>p\<close>

AOT_define Impossible :: \<open>\<Pi> \<Rightarrow> \<phi>\<close> ("Impossible'(_')")
  contingent_properties_2: \<open>Impossible([F]) \<equiv>\<^sub>d\<^sub>f F\<down> & \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]x\<^sub>1...x\<^sub>n\<close>

AOT_define Impossible0 :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("Impossible0'(_')")
  contingent_properties_2_0: \<open>Impossible0(p) \<equiv>\<^sub>d\<^sub>f \<box>\<not>p\<close>

AOT_define NonContingent :: \<open>\<Pi> \<Rightarrow> \<phi>\<close> ("NonContingent'(_')")
  contingent_properties_3: \<open>NonContingent([F]) \<equiv>\<^sub>d\<^sub>f Necessary([F]) \<or> Impossible([F])\<close>

AOT_define NonContingent0 :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("NonContingent0'(_')")
  contingent_properties_3_0: \<open>NonContingent0(p) \<equiv>\<^sub>d\<^sub>f Necessary0(p) \<or> Impossible0(p)\<close>

AOT_define Contingent :: \<open>\<Pi> \<Rightarrow> \<phi>\<close> ("Contingent'(_')")
  contingent_properties_4: \<open>Contingent([F]) \<equiv>\<^sub>d\<^sub>f F\<down> & \<not>(Necessary([F]) \<or> Impossible([F]))\<close>

AOT_define Contingent0 :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("Contingent0'(_')")
  contingent_properties_4_0: \<open>Contingent0(p) \<equiv>\<^sub>d\<^sub>f \<not>(Necessary0(p) \<or> Impossible0(p))\<close>


AOT_theorem thm_cont_prop_1: \<open>NonContingent([F]) \<equiv> NonContingent([F]\<^sup>-)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>NonContingent([F])\<close>
  AOT_hence \<open>Necessary([F]) \<or> Impossible([F])\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF contingent_properties_3] by blast
  moreover {
    AOT_assume \<open>Necessary([F])\<close>
    AOT_hence \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]x\<^sub>1...x\<^sub>n)\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF contingent_properties_1] by blast
    moreover AOT_modally_strict {
      AOT_assume \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]x\<^sub>1...x\<^sub>n\<close>
      AOT_hence \<open>[F]x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n using "\<forall>E" by blast
      AOT_hence \<open>\<not>[F]\<^sup>-x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n
        by (meson "\<equiv>E"(6) "oth-class-taut:3:a" thm_relation_negation_2 "\<equiv>E"(1))
      AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]\<^sup>-x\<^sub>1...x\<^sub>n\<close> using "\<forall>I" by fast
    }
    ultimately AOT_have \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]\<^sup>-x\<^sub>1...x\<^sub>n)\<close>
      using "RN[prem]"[where \<Gamma>="{\<guillemotleft>\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]x\<^sub>1...x\<^sub>n\<guillemotright>}", simplified] by blast
    AOT_hence \<open>Impossible([F]\<^sup>-)\<close>
      using "\<equiv>Df"[OF contingent_properties_2, THEN "\<equiv>S"(1), OF rel_neg_T_3, THEN "\<equiv>E"(2)]
      by blast
  }
  moreover {
    AOT_assume \<open>Impossible([F])\<close>
    AOT_hence \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]x\<^sub>1...x\<^sub>n)\<close>
      using "\<equiv>Df"[OF contingent_properties_2, THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], THEN "\<equiv>E"(1)]
      by blast
    moreover AOT_modally_strict {
      AOT_assume \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]x\<^sub>1...x\<^sub>n\<close>
      AOT_hence \<open>\<not>[F]x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n using "\<forall>E" by blast
      AOT_hence \<open>[F]\<^sup>-x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n
        by (meson "\<equiv>E"(6) "oth-class-taut:3:a" thm_relation_negation_1 "\<equiv>E"(1))
      AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]\<^sup>-x\<^sub>1...x\<^sub>n\<close> using "\<forall>I" by fast
    }
    ultimately AOT_have \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]\<^sup>-x\<^sub>1...x\<^sub>n)\<close>
      using "RN[prem]"[where \<Gamma>="{\<guillemotleft>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]x\<^sub>1...x\<^sub>n\<guillemotright>}"] by blast
    AOT_hence \<open>Necessary([F]\<^sup>-)\<close>
      using "\<equiv>\<^sub>d\<^sub>fI"[OF contingent_properties_1] by blast
  }
  ultimately AOT_have \<open>Necessary([F]\<^sup>-) \<or> Impossible([F]\<^sup>-)\<close>
    using "\<or>E"(1) "\<or>I" "\<rightarrow>I" by metis
  AOT_thus \<open>NonContingent([F]\<^sup>-)\<close>
    using "\<equiv>\<^sub>d\<^sub>fI"[OF contingent_properties_3] by blast
next
  AOT_assume \<open>NonContingent([F]\<^sup>-)\<close>
  AOT_hence \<open>Necessary([F]\<^sup>-) \<or> Impossible([F]\<^sup>-)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF contingent_properties_3] by blast
  moreover {
    AOT_assume \<open>Necessary([F]\<^sup>-)\<close>
    AOT_hence \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]\<^sup>-x\<^sub>1...x\<^sub>n)\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF contingent_properties_1] by blast
    moreover AOT_modally_strict {
      AOT_assume \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]\<^sup>-x\<^sub>1...x\<^sub>n\<close>
      AOT_hence \<open>[F]\<^sup>-x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n using "\<forall>E" by blast
      AOT_hence \<open>\<not>[F]x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n
        by (meson "\<equiv>E"(6) "oth-class-taut:3:a" thm_relation_negation_1 "\<equiv>E"(2))
      AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]x\<^sub>1...x\<^sub>n\<close> using "\<forall>I" by fast
    }
    ultimately AOT_have \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]x\<^sub>1...x\<^sub>n\<close>
      using "RN[prem]"[where \<Gamma>="{\<guillemotleft>\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]\<^sup>-x\<^sub>1...x\<^sub>n\<guillemotright>}"] by blast
    AOT_hence \<open>Impossible([F])\<close>
      using "\<equiv>Df"[OF contingent_properties_2, THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], THEN "\<equiv>E"(2)]
      by blast
  }
  moreover {
    AOT_assume \<open>Impossible([F]\<^sup>-)\<close>
    AOT_hence \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]\<^sup>-x\<^sub>1...x\<^sub>n)\<close>
      using "\<equiv>Df"[OF contingent_properties_2, THEN "\<equiv>S"(1), OF rel_neg_T_3, THEN "\<equiv>E"(1)]
      by blast
    moreover AOT_modally_strict {
      AOT_assume \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]\<^sup>-x\<^sub>1...x\<^sub>n\<close>
      AOT_hence \<open>\<not>[F]\<^sup>-x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n using "\<forall>E" by blast
      AOT_hence \<open>[F]x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n 
        using thm_relation_negation_1[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1)]
              "useful-tautologies:1"[THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]x\<^sub>1...x\<^sub>n\<close> using "\<forall>I" by fast
    }
    ultimately AOT_have \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]x\<^sub>1...x\<^sub>n)\<close>
      using "RN[prem]"[where \<Gamma>="{\<guillemotleft>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>[F]\<^sup>-x\<^sub>1...x\<^sub>n\<guillemotright>}"] by blast
    AOT_hence \<open>Necessary([F])\<close>
      using "\<equiv>\<^sub>d\<^sub>fI"[OF contingent_properties_1] by blast
  }
  ultimately AOT_have \<open>Necessary([F]) \<or> Impossible([F])\<close>
    using "\<or>E"(1) "\<or>I" "\<rightarrow>I" by metis
  AOT_thus \<open>NonContingent([F])\<close>
    using "\<equiv>\<^sub>d\<^sub>fI"[OF contingent_properties_3] by blast
qed

AOT_theorem thm_cont_prop_2: \<open>Contingent([F]) \<equiv> \<diamond>\<exists>x [F]x & \<diamond>\<exists>x \<not>[F]x\<close>
proof -
  AOT_have \<open>Contingent([F]) \<equiv> \<not>(Necessary([F]) \<or> Impossible([F]))\<close>
    using contingent_properties_4[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst]]
    by blast
  also AOT_have \<open>... \<equiv> \<not>Necessary([F]) & \<not>Impossible([F])\<close>
    using "oth-class-taut:5:d" by fastforce
  also AOT_have \<open>... \<equiv> \<not>Impossible([F]) & \<not>Necessary([F])\<close>
    by (simp add: "Commutativity of &")
  also AOT_have \<open>... \<equiv> \<diamond>\<exists>x [F]x & \<not>Necessary([F])\<close>
  proof (rule "oth-class-taut:4:e"[THEN "\<rightarrow>E"])
    AOT_have \<open>\<not>Impossible([F]) \<equiv> \<not>\<box>\<not> \<exists>x [F]x\<close>
      apply (rule "oth-class-taut:4:b"[THEN "\<equiv>E"(1)])
      apply (AOT_subst "\<guillemotleft>\<exists>x [F]x\<guillemotright>" "\<guillemotleft>\<not> \<forall>x \<not>[F]x\<guillemotright>")
       apply (simp add: AOT_exists "\<equiv>Df")
      apply (AOT_subst_rev "\<guillemotleft>\<forall>x \<not>[F]x\<guillemotright>" "\<guillemotleft>\<not>\<not>\<forall>x \<not>[F]x\<guillemotright>" )
       apply (simp add: "oth-class-taut:3:b")
      using contingent_properties_2[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst]] by blast
    also AOT_have \<open>... \<equiv> \<diamond>\<exists>x [F]x\<close>
      using AOT_dia[THEN "\<equiv>Df", symmetric] by blast
    finally AOT_show \<open>\<not>Impossible([F]) \<equiv> \<diamond>\<exists>x [F]x\<close> .
  qed
  also AOT_have \<open>... \<equiv> \<diamond>\<exists>x [F]x & \<diamond>\<exists>x \<not>[F]x\<close>
  proof (rule "oth-class-taut:4:f"[THEN "\<rightarrow>E"])
    AOT_have \<open>\<not>Necessary([F]) \<equiv> \<not>\<box>\<not>\<exists>x \<not>[F]x\<close>
      apply (rule "oth-class-taut:4:b"[THEN "\<equiv>E"(1)])
      apply (AOT_subst "\<guillemotleft>\<exists>x \<not>[F]x\<guillemotright>" "\<guillemotleft>\<not> \<forall>x \<not>\<not>[F]x\<guillemotright>")
       apply (simp add: AOT_exists "\<equiv>Df")
      apply (AOT_subst_rev "\<lambda> \<kappa> . \<guillemotleft>[F]\<kappa>\<guillemotright>" "\<lambda> \<kappa> . \<guillemotleft>\<not>\<not>[F]\<kappa>\<guillemotright>")
       apply (simp add: "oth-class-taut:3:b")
      apply (AOT_subst_rev "\<guillemotleft>\<forall>x [F]x\<guillemotright>" "\<guillemotleft>\<not>\<not>\<forall>x [F]x\<guillemotright>")
      by (auto simp: "oth-class-taut:3:b" contingent_properties_1 "\<equiv>Df")
    also AOT_have \<open>... \<equiv> \<diamond>\<exists>x \<not>[F]x\<close>
      using AOT_dia[THEN "\<equiv>Df", symmetric] by blast
    finally AOT_show \<open>\<not>Necessary([F]) \<equiv> \<diamond>\<exists>x \<not>[F]x\<close>.
  qed
  finally show ?thesis.
qed

AOT_theorem thm_cont_prop_3: \<open>Contingent([F]) \<equiv> Contingent([F]\<^sup>-)\<close> for F::\<open><\<kappa>> AOT_var\<close>
proof -
  {
    fix \<Pi> :: \<open><\<kappa>>\<close>
    AOT_assume \<open>\<Pi>\<down>\<close>
    moreover AOT_have \<open>\<forall>F (Contingent([F]) \<equiv> \<diamond>\<exists>x [F]x & \<diamond>\<exists>x \<not>[F]x)\<close>
      using thm_cont_prop_2 GEN by fast
    ultimately  AOT_have \<open>Contingent([\<Pi>]) \<equiv> \<diamond>\<exists>x [\<Pi>]x & \<diamond>\<exists>x \<not>[\<Pi>]x\<close>
      using thm_cont_prop_2 "\<forall>E" by fast
  } note 1 = this
  AOT_have \<open>Contingent([F]) \<equiv> \<diamond>\<exists>x [F]x & \<diamond>\<exists>x \<not>[F]x\<close>
    using thm_cont_prop_2 by blast
  also AOT_have \<open>... \<equiv> \<diamond>\<exists>x \<not>[F]x & \<diamond>\<exists>x [F]x\<close>
    by (simp add: "Commutativity of &")
  also AOT_have \<open>... \<equiv> \<diamond>\<exists>x [F]\<^sup>-x & \<diamond>\<exists>x [F]x\<close>
    by (AOT_subst "\<lambda> \<kappa> . \<guillemotleft>[F]\<^sup>-\<kappa>\<guillemotright>"  "\<lambda>\<kappa> . \<guillemotleft>\<not>[F]\<kappa>\<guillemotright>")
       (auto simp: thm_relation_negation_1 "oth-class-taut:3:a")
  also AOT_have \<open>... \<equiv> \<diamond>\<exists>x [F]\<^sup>-x & \<diamond>\<exists>x \<not>[F]\<^sup>-x\<close>
    by (AOT_subst_rev "\<lambda> \<kappa> . \<guillemotleft>\<not>[F]\<^sup>-\<kappa>\<guillemotright>"  "\<lambda>\<kappa> . \<guillemotleft>[F]\<kappa>\<guillemotright>")
       (auto simp: thm_relation_negation_2 "oth-class-taut:3:a")
  also AOT_have \<open>... \<equiv> Contingent([F]\<^sup>-)\<close>
    using 1[OF rel_neg_T_3, symmetric] by blast
  finally show ?thesis.
qed

AOT_define concrete_if_concrete :: \<open>\<Pi>\<close> ("L")  L_def: \<open>L =\<^sub>d\<^sub>f [\<lambda>x E!x \<rightarrow> E!x]\<close>

AOT_theorem thm_noncont_e_e_1: \<open>Necessary(L)\<close>
proof -
  AOT_modally_strict {
    fix x
    AOT_have \<open>[\<lambda>x E!x \<rightarrow> E!x]\<down>\<close> by "cqt:2[lambda]"
    moreover AOT_have \<open>x\<down>\<close> using "cqt:2[const_var]"[axiom_inst] by blast
    moreover AOT_have \<open>E!x \<rightarrow> E!x\<close> using "if-p-then-p" by blast
    ultimately AOT_have \<open>[\<lambda>x E!x \<rightarrow> E!x]x\<close>
      using "\<beta>\<leftarrow>C" by blast
  }
  AOT_hence 0: \<open>\<box>\<forall>x [\<lambda>x E!x \<rightarrow> E!x]x\<close>
    using RN GEN by blast
  show ?thesis
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def])
     apply "cqt:2[lambda]"
    by (rule contingent_properties_1[THEN "\<equiv>\<^sub>d\<^sub>fI", OF 0])
qed

AOT_theorem thm_noncont_e_e_2: \<open>Impossible([L]\<^sup>-)\<close>
proof -
  AOT_modally_strict {
    fix x

    AOT_have 0: \<open>\<forall>F (\<not>[F]\<^sup>-x \<equiv> [F]x)\<close>
      using thm_relation_negation_2 GEN by fast
    AOT_have \<open>\<not>[\<lambda>x E!x \<rightarrow> E!x]\<^sup>-x \<equiv> [\<lambda>x E!x \<rightarrow> E!x]x\<close>
      by (rule 0[THEN "\<forall>E"(1)]) "cqt:2[lambda]"
    moreover {
      AOT_have \<open>[\<lambda>x E!x \<rightarrow> E!x]\<down>\<close> by "cqt:2[lambda]"
      moreover AOT_have \<open>x\<down>\<close> using "cqt:2[const_var]"[axiom_inst] by blast
      moreover AOT_have \<open>E!x \<rightarrow> E!x\<close> using "if-p-then-p" by blast
      ultimately AOT_have \<open>[\<lambda>x E!x \<rightarrow> E!x]x\<close>
        using "\<beta>\<leftarrow>C" by blast
    }
    ultimately AOT_have \<open>\<not>[\<lambda>x E!x \<rightarrow> E!x]\<^sup>-x\<close>
      using "\<equiv>E" by blast
  }
  AOT_hence 0: \<open>\<box>\<forall>x \<not>[\<lambda>x E!x \<rightarrow> E!x]\<^sup>-x\<close>
    using RN GEN by fast
  show ?thesis
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def])
     apply "cqt:2[lambda]"
    apply (rule contingent_properties_2[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "&I")
     using rel_neg_T_3
     apply blast
    using 0
    by blast
qed

AOT_theorem thm_noncont_e_e_3: \<open>NonContingent(L)\<close>
  using thm_noncont_e_e_1
  by (rule contingent_properties_3[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "\<or>I"(1)])

AOT_theorem thm_noncont_e_e_4: \<open>NonContingent([L]\<^sup>-)\<close>
proof -
  AOT_have 0: \<open>\<forall>F (NonContingent([F]) \<equiv> NonContingent([F]\<^sup>-))\<close>
    using thm_cont_prop_1 "\<forall>I" by fast
  moreover AOT_have 1: \<open>L\<down>\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
  AOT_show \<open>NonContingent([L]\<^sup>-)\<close>
    using "\<forall>E"(1)[OF 0, OF 1, THEN "\<equiv>E"(1), OF thm_noncont_e_e_3] by blast
qed

AOT_theorem thm_noncont_e_e_5: \<open>\<exists>F \<exists>G (F \<noteq> \<guillemotleft>G::<\<kappa>>\<guillemotright> & NonContingent([F]) & NonContingent([G]))\<close>
proof (rule "\<exists>I")+
  {
    AOT_have \<open>\<forall>F [F] \<noteq> [F]\<^sup>-\<close> using thm_relation_negation_5 GEN by fast
    moreover AOT_have \<open>L\<down>\<close>
      by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
    ultimately AOT_have \<open>L \<noteq> [L]\<^sup>-\<close> using "\<forall>E" by blast
  }
  AOT_thus \<open>L \<noteq> [L]\<^sup>- & NonContingent(L) & NonContingent([L]\<^sup>-)\<close>
    using thm_noncont_e_e_3 thm_noncont_e_e_4 "&I" by metis
next
  AOT_show \<open>[L]\<^sup>-\<down>\<close>
    using rel_neg_T_3 by blast
next
  AOT_show \<open>L\<down>\<close>
      by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
qed

AOT_theorem lem_cont_e_1: \<open>\<diamond>\<exists>x ([F]x & \<diamond>\<not>[F]x) \<equiv> \<diamond>\<exists>x (\<not>[F]x & \<diamond>[F]x)\<close>
proof -
  AOT_have \<open>\<diamond>\<exists>x ([F]x & \<diamond>\<not>[F]x) \<equiv> \<exists>x \<diamond>([F]x & \<diamond>\<not>[F]x)\<close>
    using "BF\<diamond>" "CBF\<diamond>" "\<equiv>I" by blast
  also AOT_have \<open>\<dots> \<equiv> \<exists>x (\<diamond>[F]x &  \<diamond>\<not>[F]x)\<close>
    by (AOT_subst \<open>\<lambda>\<kappa>. \<guillemotleft>\<diamond>([F]\<kappa> & \<diamond>\<not>[F]\<kappa>)\<guillemotright>\<close>  \<open>\<lambda> \<kappa> .  \<guillemotleft>\<diamond>[F]\<kappa> &  \<diamond>\<not>[F]\<kappa>\<guillemotright>\<close>)
       (auto simp: "S5Basic:11" "cqt-further:7")
  also AOT_have \<open>\<dots> \<equiv> \<exists>x (\<diamond>\<not>[F]x & \<diamond>[F]x)\<close>
    by (AOT_subst \<open>\<lambda>\<kappa>. \<guillemotleft>\<diamond>\<not>[F]\<kappa> & \<diamond>[F]\<kappa>\<guillemotright>\<close>  \<open>\<lambda> \<kappa> .  \<guillemotleft>\<diamond>[F]\<kappa> & \<diamond>\<not>[F]\<kappa>\<guillemotright>\<close>)
       (auto simp: "Commutativity of &" "cqt-further:7")
  also AOT_have \<open>\<dots> \<equiv> \<exists>x \<diamond>(\<not>[F]x & \<diamond>[F]x)\<close>
    by (AOT_subst \<open>\<lambda> \<kappa> .  \<guillemotleft>\<diamond>(\<not>[F]\<kappa> & \<diamond>[F]\<kappa>)\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>\<diamond>\<not>[F]\<kappa> & \<diamond>[F]\<kappa>\<guillemotright>\<close>)
       (auto simp: "S5Basic:11" "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<diamond>\<exists>x (\<not>[F]x & \<diamond>[F]x)\<close>
    using "BF\<diamond>" "CBF\<diamond>" "\<equiv>I" by fast
  finally show ?thesis.
qed

AOT_theorem lem_cont_e_2: \<open>\<diamond>\<exists>x ([F]x & \<diamond>\<not>[F]x) \<equiv> \<diamond>\<exists>x ([F]\<^sup>-x & \<diamond>\<not>[F]\<^sup>-x)\<close>
proof -
  AOT_have \<open>\<diamond>\<exists>x ([F]x & \<diamond>\<not>[F]x) \<equiv> \<diamond>\<exists>x (\<not>[F]x & \<diamond>[F]x)\<close>
    using lem_cont_e_1.
  also AOT_have \<open>\<dots> \<equiv> \<diamond>\<exists>x ([F]\<^sup>-x & \<diamond>\<not>[F]\<^sup>-x)\<close>
    apply (AOT_subst "\<lambda> \<kappa> . \<guillemotleft>\<not>[F]\<^sup>-\<kappa>\<guillemotright>" "\<lambda> \<kappa> . \<guillemotleft>[F]\<kappa>\<guillemotright>")
     apply (simp add: thm_relation_negation_2)
    apply (AOT_subst "\<lambda> \<kappa> . \<guillemotleft>[F]\<^sup>-\<kappa>\<guillemotright>" "\<lambda> \<kappa> . \<guillemotleft>\<not>[F]\<kappa>\<guillemotright>")
     apply (simp add: thm_relation_negation_1)
    by (simp add: "oth-class-taut:3:a")
  finally show ?thesis.
qed

(* TODO: note: commuted axiom 44.1 is cited as theorem 44.1 in the proof in PLM *)
AOT_theorem thm_cont_e_1: \<open>\<diamond>\<exists>x (E!x & \<diamond>\<not>E!x)\<close>
proof (rule "CBF\<diamond>"[THEN "\<rightarrow>E"])
  AOT_have \<open>\<exists>x \<diamond>(E!x & \<not>\<^bold>\<A>E!x)\<close> using "qml:4"[axiom_inst] "BF\<diamond>"[THEN "\<rightarrow>E"] by blast
  then AOT_obtain a where \<open>\<diamond>(E!a & \<not>\<^bold>\<A>E!a)\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>\<diamond>E!a & \<diamond>\<not>\<^bold>\<A>E!a\<close>
    using "KBasic2:3"[THEN "\<rightarrow>E"] by blast
  AOT_have \<xi>: \<open>\<diamond>E!a & \<diamond>\<^bold>\<A>\<not>E!a\<close>
    by (AOT_subst  "\<guillemotleft>\<^bold>\<A>\<not>E!a\<guillemotright>" "\<guillemotleft>\<not>\<^bold>\<A>E!a\<guillemotright>")
       (auto simp: "logic-actual-nec:1"[axiom_inst] \<theta>)
  AOT_have \<zeta>: \<open>\<diamond>E!a & \<^bold>\<A>\<not>E!a\<close>
    by (AOT_subst "\<guillemotleft>\<^bold>\<A>\<not>E!a\<guillemotright>" "\<guillemotleft>\<diamond>\<^bold>\<A>\<not>E!a\<guillemotright>")
       (auto simp add: "Act-Sub:4" \<xi>)
  AOT_hence \<open>\<diamond>E!a & \<diamond>\<not>E!a\<close>
    using "&E" "&I" "Act-Sub:3"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<diamond>(E!a & \<diamond>\<not>E!a)\<close> using "S5Basic:11"[THEN "\<equiv>E"(2)] by simp
  AOT_thus \<open>\<exists>x \<diamond>(E!x & \<diamond>\<not>E!x)\<close> using "\<exists>I"(2) by fast
qed

AOT_theorem thm_cont_e_2: \<open>\<diamond>\<exists>x (\<not>E!x & \<diamond>E!x)\<close>
proof -
  AOT_have \<open>\<forall>F (\<diamond>\<exists>x ([F]x & \<diamond>\<not>[F]x) \<equiv> \<diamond>\<exists>x (\<not>[F]x & \<diamond>[F]x))\<close>
    using lem_cont_e_1 GEN by fast
  AOT_hence \<open>(\<diamond>\<exists>x (E!x & \<diamond>\<not>E!x) \<equiv> \<diamond>\<exists>x (\<not>E!x & \<diamond>E!x))\<close>
    using "\<forall>E"(1) "cqt:2[concrete]"[axiom_inst] by blast
  thus ?thesis using thm_cont_e_1 "\<equiv>E" by blast
qed

AOT_theorem thm_cont_e_3: \<open>\<diamond>\<exists>x E!x\<close>
proof (rule "CBF\<diamond>"[THEN "\<rightarrow>E"])
  AOT_obtain a where \<open>\<diamond>(E!a & \<diamond>\<not>E!a)\<close>
    using "\<exists>E"[rotated, OF thm_cont_e_1[THEN "BF\<diamond>"[THEN "\<rightarrow>E"]]] by blast
  AOT_hence \<open>\<diamond>E!a\<close>
    using "KBasic2:3"[THEN "\<rightarrow>E", THEN "&E"(1)] by blast
  AOT_thus \<open>\<exists>x \<diamond>E!x\<close> using "\<exists>I" by fast
qed

AOT_theorem thm_cont_e_4: \<open>\<diamond>\<exists>x \<not>E!x\<close>
proof (rule "CBF\<diamond>"[THEN "\<rightarrow>E"])
  AOT_obtain a where \<open>\<diamond>(E!a & \<diamond>\<not>E!a)\<close>
    using "\<exists>E"[rotated, OF thm_cont_e_1[THEN "BF\<diamond>"[THEN "\<rightarrow>E"]]] by blast
  AOT_hence \<open>\<diamond>\<diamond>\<not>E!a\<close>
    using "KBasic2:3"[THEN "\<rightarrow>E", THEN "&E"(2)] by blast
  AOT_hence \<open>\<diamond>\<not>E!a\<close>
    using "4\<diamond>"[THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<exists>x \<diamond>\<not>E!x\<close> using "\<exists>I" by fast
qed

AOT_theorem thm_cont_e_5: \<open>Contingent([E!])\<close>
proof -
  AOT_have \<open>\<forall>F (Contingent([F]) \<equiv> \<diamond>\<exists>x [F]x & \<diamond>\<exists>x \<not>[F]x)\<close>
    using thm_cont_prop_2 GEN by fast
  AOT_hence \<open>Contingent([E!]) \<equiv> \<diamond>\<exists>x E!x & \<diamond>\<exists>x \<not>E!x\<close>
    using "\<forall>E"(1) "cqt:2[concrete]"[axiom_inst] by blast
  thus ?thesis
    using thm_cont_e_3 thm_cont_e_4 "\<equiv>E"(2) "&I" by blast
qed

AOT_theorem thm_cont_e_6: \<open>Contingent([E!]\<^sup>-)\<close>
proof -
  AOT_have \<open>\<forall>F (Contingent([\<guillemotleft>F::<\<kappa>>\<guillemotright>]) \<equiv> Contingent([F]\<^sup>-))\<close>
    using thm_cont_prop_3 GEN by fast
  AOT_hence \<open>Contingent([E!]) \<equiv> Contingent([E!]\<^sup>-)\<close>
    using "\<forall>E" "cqt:2[concrete]"[axiom_inst] by fast
  thus ?thesis using thm_cont_e_5 "\<equiv>E" by blast
qed

AOT_theorem thm_cont_e_7: \<open>\<exists>F\<exists>G (Contingent([\<guillemotleft>F::<\<kappa>>\<guillemotright>]) & Contingent([G]) & F \<noteq> G)\<close>
proof (rule "\<exists>I")+
  AOT_have \<open>\<forall>F [\<guillemotleft>F::<\<kappa>>\<guillemotright>] \<noteq> [F]\<^sup>-\<close> using thm_relation_negation_5 GEN by fast
  AOT_hence \<open>[E!] \<noteq> [E!]\<^sup>-\<close>
    using "\<forall>E" "cqt:2[concrete]"[axiom_inst] by fast
  AOT_thus \<open>Contingent([E!]) & Contingent([E!]\<^sup>-) & [E!] \<noteq> [E!]\<^sup>-\<close>
    using thm_cont_e_5 thm_cont_e_6 "&I" by metis
next
  AOT_show \<open>E!\<^sup>-\<down>\<close>
    by (fact AOT)
next
  AOT_show \<open>E!\<down>\<close> by (fact "cqt:2[concrete]"[axiom_inst])
qed

AOT_theorem property_facts_1: \<open>NonContingent([F]) \<rightarrow> \<not>\<exists>G (Contingent([G]) & G = F)\<close>
proof (rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_assume \<open>NonContingent([F])\<close>
  AOT_hence 1: \<open>Necessary([F]) \<or> Impossible([F])\<close>
    using contingent_properties_3[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_assume \<open>\<exists>G (Contingent([G]) & G = F)\<close>
  then AOT_obtain G where \<open>Contingent([G]) & G = F\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>Contingent([F])\<close> using "=E" "&E" by blast
  AOT_hence \<open>\<not>(Necessary([F]) \<or> Impossible([F]))\<close>
    using contingent_properties_4[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], THEN "\<equiv>E"(1)] by blast
  AOT_thus \<open>(Necessary([F]) \<or> Impossible([F])) & \<not>(Necessary([F]) \<or> Impossible([F]))\<close>
    using 1 "&I" by blast
qed

AOT_theorem property_facts_2: \<open>Contingent([F]) \<rightarrow> \<not>\<exists>G (NonContingent([G]) & G = F)\<close>
proof (rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_assume \<open>Contingent([F])\<close>
  AOT_hence 1: \<open>\<not>(Necessary([F]) \<or> Impossible([F]))\<close>
    using contingent_properties_4[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], THEN "\<equiv>E"(1)] by blast
  AOT_assume \<open>\<exists>G (NonContingent([G]) & G = F)\<close>
  then AOT_obtain G where \<open>NonContingent([G]) & G = F\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>NonContingent([F])\<close> using "=E" "&E" by blast
  AOT_hence \<open>Necessary([F]) \<or> Impossible([F])\<close>
    using contingent_properties_3[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_thus \<open>(Necessary([F]) \<or> Impossible([F])) & \<not>(Necessary([F]) \<or> Impossible([F]))\<close>
    using 1 "&I" by blast
qed

AOT_theorem property_facts_3: \<open>L \<noteq> [L]\<^sup>- & L \<noteq> E! & L \<noteq> E!\<^sup>- & [L]\<^sup>- \<noteq> [E!]\<^sup>- & E! \<noteq> [E!]\<^sup>-\<close>
proof -
  AOT_have noneqI: \<open>\<Pi> \<noteq> \<Pi>'\<close> if \<open>\<phi>{\<Pi>}\<close> and \<open>\<not>\<phi>{\<Pi>'}\<close> for \<phi> \<Pi> \<Pi>'
    apply (rule "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "raa-cor:2")
    using "=E"[where \<phi>=\<phi> and \<tau>=\<Pi> and \<sigma> = \<Pi>'] that "&I" by blast
  AOT_have contingent_denotes: \<open>\<Pi>\<down>\<close> if \<open>Contingent([\<Pi>])\<close> for \<Pi>
    using that contingent_properties_4[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1)] by blast
  AOT_have not_noncontingent_if_contingent: \<open>\<not>NonContingent([\<Pi>])\<close> if \<open>Contingent([\<Pi>])\<close> for \<Pi>
  proof(rule RAA(2))
    AOT_show \<open>\<not>(Necessary([\<Pi>]) \<or> Impossible([\<Pi>]))\<close>
      using that contingent_properties_4[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF contingent_denotes[OF that], THEN "\<equiv>E"(1)] by blast
  next
    AOT_assume \<open>NonContingent([\<Pi>])\<close>
    AOT_thus \<open>Necessary([\<Pi>]) \<or> Impossible([\<Pi>])\<close>
      using contingent_properties_3[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  qed

  show ?thesis
  proof (rule "&I")+
    AOT_show \<open>L \<noteq> [L]\<^sup>-\<close>
      apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def])
       apply "cqt:2[lambda]"
      apply (rule "\<forall>E"(1)[where \<phi>="\<lambda> \<Pi> . \<guillemotleft>\<Pi> \<noteq> [\<Pi>]\<^sup>-\<guillemotright>"])
       apply (rule GEN) apply (fact AOT)
      by "cqt:2[lambda]"
  next
    AOT_show \<open>L \<noteq> E!\<close>
      apply (rule noneqI)
      using thm_noncont_e_e_3 not_noncontingent_if_contingent[OF thm_cont_e_5]
      by auto
  next
    AOT_show \<open>L \<noteq> E!\<^sup>-\<close>
      apply (rule noneqI)
      using thm_noncont_e_e_3 apply fast
      apply (rule not_noncontingent_if_contingent)
      apply (rule "\<forall>E"(1)[where \<phi>="\<lambda> \<Pi> . \<guillemotleft>Contingent([\<Pi>]) \<equiv> Contingent([\<Pi>]\<^sup>-)\<guillemotright>", rotated, OF contingent_denotes, THEN "\<equiv>E"(1), rotated])
      using thm_cont_prop_3 GEN apply fast
      using thm_cont_e_5 by fast+
  next
    AOT_show \<open>[L]\<^sup>- \<noteq> E!\<^sup>-\<close>
      apply (rule noneqI)
      using thm_noncont_e_e_4 apply fast
      apply (rule not_noncontingent_if_contingent)
      apply (rule "\<forall>E"(1)[where \<phi>="\<lambda> \<Pi> . \<guillemotleft>Contingent([\<Pi>]) \<equiv> Contingent([\<Pi>]\<^sup>-)\<guillemotright>", rotated, OF contingent_denotes, THEN "\<equiv>E"(1), rotated])
      using thm_cont_prop_3 GEN apply fast
      using thm_cont_e_5 by fast+
  next
    AOT_show \<open>E! \<noteq> E!\<^sup>-\<close>
      apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def])
       apply "cqt:2[lambda]"
      apply (rule "\<forall>E"(1)[where \<phi>="\<lambda> \<Pi> . \<guillemotleft>\<Pi> \<noteq> [\<Pi>]\<^sup>-\<guillemotright>"])
       apply (rule GEN) apply (fact AOT)
      by (fact "cqt:2[concrete]"[axiom_inst])
  qed
qed

AOT_theorem thm_cont_propos_1: \<open>NonContingent0(p) \<equiv> NonContingent0(((p)\<^sup>-))\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>NonContingent0(p)\<close>
  AOT_hence \<open>Necessary0(p) \<or> Impossible0(p)\<close>
    using contingent_properties_3_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  moreover {
    AOT_assume \<open>Necessary0(p)\<close>
    AOT_hence 1: \<open>\<box>p\<close> using contingent_properties_1_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    AOT_have \<open>\<box>\<not>((p)\<^sup>-)\<close>
      by (AOT_subst "\<guillemotleft>\<not>((p)\<^sup>-)\<guillemotright>" "AOT_term_of_var p")
         (auto simp add: 1 thm_relation_negation_4)
    AOT_hence \<open>Impossible0(((p)\<^sup>-))\<close>
      by (rule contingent_properties_2_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  }
  moreover {
    AOT_assume \<open>Impossible0(p)\<close>
    AOT_hence 1: \<open>\<box>\<not>p\<close>
      by (rule contingent_properties_2_0[THEN "\<equiv>\<^sub>d\<^sub>fE"])
    AOT_have \<open>\<box>((p)\<^sup>-)\<close>
      by (AOT_subst "\<guillemotleft>((p)\<^sup>-)\<guillemotright>" "\<guillemotleft>\<not>p\<guillemotright>") 
         (auto simp: 1 thm_relation_negation_3)
    AOT_hence \<open>Necessary0(((p)\<^sup>-))\<close>
      by (rule contingent_properties_1_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  }
  ultimately AOT_have \<open>Necessary0(((p)\<^sup>-)) \<or> Impossible0(((p)\<^sup>-))\<close>
    using "\<or>E"(1) "\<or>I" "\<rightarrow>I" by metis
  AOT_thus \<open>NonContingent0(((p)\<^sup>-))\<close>
    using contingent_properties_3_0[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
next
  AOT_assume \<open>NonContingent0(((p)\<^sup>-))\<close>
  AOT_hence \<open>Necessary0(((p)\<^sup>-)) \<or> Impossible0(((p)\<^sup>-))\<close>
    using contingent_properties_3_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  moreover {
    AOT_assume \<open>Impossible0(((p)\<^sup>-))\<close>
    AOT_hence 1: \<open>\<box>\<not>((p)\<^sup>-)\<close>
      by (rule contingent_properties_2_0[THEN "\<equiv>\<^sub>d\<^sub>fE"])
    AOT_have \<open>\<box>p\<close>
      by (AOT_subst_rev "\<guillemotleft>\<not>((p)\<^sup>-)\<guillemotright>" "AOT_term_of_var p")
         (auto simp: 1 thm_relation_negation_4)
    AOT_hence \<open>Necessary0(p)\<close>
      using contingent_properties_1_0[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
  }
  moreover {
    AOT_assume \<open>Necessary0(((p)\<^sup>-))\<close>
    AOT_hence 1: \<open>\<box>((p)\<^sup>-)\<close>
      by (rule contingent_properties_1_0[THEN "\<equiv>\<^sub>d\<^sub>fE"])
    AOT_have \<open>\<box>\<not>p\<close>
      by (AOT_subst_rev "\<guillemotleft>((p)\<^sup>-)\<guillemotright>" "\<guillemotleft>\<not>p\<guillemotright>")
         (auto simp: 1 thm_relation_negation_3)
    AOT_hence \<open>Impossible0(p)\<close>
      by (rule contingent_properties_2_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  }
  ultimately AOT_have \<open>Necessary0(p) \<or> Impossible0(p)\<close>
    using "\<or>E"(1) "\<or>I" "\<rightarrow>I" by metis
  AOT_thus \<open>NonContingent0(p)\<close>
    using contingent_properties_3_0[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

AOT_theorem thm_cont_propos_2: \<open>Contingent0(\<phi>) \<equiv> \<diamond>\<phi> & \<diamond>\<not>\<phi>\<close>
proof -
  AOT_have \<open>Contingent0(\<phi>) \<equiv> \<not>(Necessary0(\<phi>) \<or> Impossible0(\<phi>))\<close>
    using contingent_properties_4_0[THEN "\<equiv>Df"] by simp
  also AOT_have \<open>\<dots> \<equiv> \<not>Necessary0(\<phi>) & \<not>Impossible0(\<phi>)\<close>
    by (fact AOT)
  also AOT_have \<open>\<dots> \<equiv> \<not>Impossible0(\<phi>) & \<not>Necessary0(\<phi>)\<close>
    by (fact AOT)
  also AOT_have \<open>\<dots> \<equiv> \<diamond>\<phi> & \<diamond>\<not>\<phi>\<close>
    apply (AOT_subst "\<guillemotleft>\<diamond>\<phi>\<guillemotright>" "\<guillemotleft>\<not>\<box>\<not>\<phi>\<guillemotright>")
     apply (simp add: AOT_dia "\<equiv>Df")
    apply (AOT_subst "\<guillemotleft>Impossible0(\<phi>)\<guillemotright>" "\<guillemotleft>\<box>\<not>\<phi>\<guillemotright>")
     apply (simp add: contingent_properties_2_0 "\<equiv>Df")
    apply (AOT_subst_rev "\<guillemotleft>\<not>\<box>\<phi>\<guillemotright>" "\<guillemotleft>\<diamond>\<not>\<phi>\<guillemotright>")
     apply (simp add: "KBasic:11")
    apply (AOT_subst "\<guillemotleft>Necessary0(\<phi>)\<guillemotright>" "\<guillemotleft>\<box>\<phi>\<guillemotright>")
     apply (simp add: contingent_properties_1_0 "\<equiv>Df")
    by (simp add: "oth-class-taut:3:a")
  finally show ?thesis.
qed

AOT_theorem thm_cont_propos_3: \<open>Contingent0(p) \<equiv> Contingent0(((p)\<^sup>-))\<close>
proof -
  AOT_have \<open>Contingent0(p) \<equiv> \<diamond>p & \<diamond>\<not>p\<close> using thm_cont_propos_2.
  also AOT_have \<open>\<dots> \<equiv> \<diamond>\<not>p & \<diamond>p\<close> by (fact AOT)
  also AOT_have \<open>\<dots> \<equiv> \<diamond>((p)\<^sup>-) & \<diamond>p\<close>
    by (AOT_subst "\<guillemotleft>((p)\<^sup>-)\<guillemotright>" "\<guillemotleft>\<not>p\<guillemotright>")
       (auto simp: thm_relation_negation_3 "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<diamond>((p)\<^sup>-) & \<diamond>\<not>((p)\<^sup>-)\<close>
    by (AOT_subst "\<guillemotleft>\<not>((p)\<^sup>-)\<guillemotright>" "AOT_term_of_var p")
       (auto simp: thm_relation_negation_4 "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> Contingent0(((p)\<^sup>-))\<close>
    using thm_cont_propos_2[symmetric] by blast
  finally show ?thesis.
qed

AOT_define noncontingent_prop :: \<open>\<phi>\<close> ("p\<^sub>0")
  p\<^sub>0_def: "(p\<^sub>0) =\<^sub>d\<^sub>f (\<forall>x (E!x \<rightarrow> E!x))"

AOT_theorem thm_noncont_propos_1:  \<open>Necessary0((p\<^sub>0))\<close>
proof(rule contingent_properties_1_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_show \<open>\<box>(p\<^sub>0)\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF p\<^sub>0_def])
    using "log-prop-prop:2" apply simp
    using "if-p-then-p" RN GEN by fast
qed

AOT_theorem thm_noncont_propos_2: \<open>Impossible0(((p\<^sub>0)\<^sup>-))\<close>
proof(rule contingent_properties_2_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_show \<open>\<box>\<not>((p\<^sub>0)\<^sup>-)\<close>
    apply (AOT_subst "\<guillemotleft>((p\<^sub>0)\<^sup>-)\<guillemotright>" "\<guillemotleft>\<not>p\<^sub>0\<guillemotright>")
    using thm_relation_negation_3 GEN "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] apply fast
    apply (AOT_subst_rev "\<guillemotleft>p\<^sub>0\<guillemotright>" "\<guillemotleft>\<not>\<not>p\<^sub>0\<guillemotright>" )
     apply (simp add: "oth-class-taut:3:b")
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF p\<^sub>0_def])
    using "log-prop-prop:2" apply simp
    using "if-p-then-p" RN GEN by fast
qed

AOT_theorem thm_noncont_propos_3: \<open>NonContingent0((p\<^sub>0))\<close>
  apply(rule contingent_properties_3_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  using thm_noncont_propos_1 "\<or>I" by blast

AOT_theorem thm_noncont_propos_4: \<open>NonContingent0(((p\<^sub>0)\<^sup>-))\<close>
  apply(rule contingent_properties_3_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  using thm_noncont_propos_2 "\<or>I" by blast

AOT_theorem thm_noncont_propos_5: \<open>\<exists>p\<exists>q (NonContingent0((p)) & NonContingent0((q)) & p \<noteq> q)\<close>
proof(rule "\<exists>I")+
  AOT_have 0: \<open>\<phi> \<noteq> (\<phi>)\<^sup>-\<close> for \<phi>
    using thm_relation_negation_6 "\<forall>I" "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by fast
  AOT_thus \<open>NonContingent0((p\<^sub>0)) & NonContingent0(((p\<^sub>0)\<^sup>-)) & (p\<^sub>0) \<noteq> (p\<^sub>0)\<^sup>-\<close>
    using thm_noncont_propos_3 thm_noncont_propos_4 "&I" by auto
qed(auto simp: "log-prop-prop:2")

AOT_act_theorem no_cnac: \<open>\<not>\<exists>x(E!x & \<not>\<^bold>\<A>E!x)\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>\<exists>x(E!x & \<not>\<^bold>\<A>E!x)\<close>
  then AOT_obtain a where a: \<open>E!a & \<not>\<^bold>\<A>E!a\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<^bold>\<A>\<not>E!a\<close> using "&E" "logic-actual-nec:1"[axiom_inst, THEN "\<equiv>E"(2)] by blast
  AOT_hence \<open>\<not>E!a\<close> using "logic-actual"[act_axiom_inst, THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>E!a & \<not>E!a\<close> using a "&E" "&I" by blast
  AOT_thus \<open>p & \<not>p\<close> for p using "raa-cor:1" by blast
qed

AOT_theorem pos_not_pna_1: \<open>\<not>\<^bold>\<A>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>\<^bold>\<A>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
  AOT_hence \<open>\<exists>x \<^bold>\<A>(E!x & \<not>\<^bold>\<A>E!x)\<close>
    using "Act-Basic:10"[THEN "\<equiv>E"(1)] by blast
  then AOT_obtain a where \<open>\<^bold>\<A>(E!a & \<not>\<^bold>\<A>E!a)\<close> using "\<exists>E"[rotated] by blast
  AOT_hence 1: \<open>\<^bold>\<A>E!a & \<^bold>\<A>\<not>\<^bold>\<A>E!a\<close> using "Act-Basic:2"[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<not>\<^bold>\<A>\<^bold>\<A>E!a\<close> using "&E"(2) "logic-actual-nec:1"[axiom_inst, THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<not>\<^bold>\<A>E!a\<close> using "logic-actual-nec:4"[axiom_inst, THEN "\<equiv>E"(1)] RAA by blast
  AOT_thus \<open>p & \<not>p\<close> for p using 1[THEN "&E"(1)] "&I" "raa-cor:1" by blast
qed

AOT_theorem pos_not_pna_2: \<open>\<diamond>\<not>\<exists>x(E!x & \<not>\<^bold>\<A>E!x)\<close>
proof (rule RAA(1))
  AOT_show \<open>\<not>\<^bold>\<A>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close> using pos_not_pna_1 by blast
next
  AOT_assume \<open>\<not>\<diamond>\<not>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
  AOT_hence \<open>\<box>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
    using "KBasic:12"[THEN "\<equiv>E"(2)] by blast
  AOT_thus \<open>\<^bold>\<A>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
    using "nec-imp-act"[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem pos_not_pna_3: \<open>\<exists>x (\<diamond>E!x & \<not>\<^bold>\<A>E!x)\<close>
proof -
  AOT_obtain a where \<open>\<diamond>(E!a & \<not>\<^bold>\<A>E!a)\<close>
    using "qml:4"[axiom_inst] "BF\<diamond>"[THEN "\<rightarrow>E"] "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>\<diamond>E!a\<close> and \<xi>: \<open>\<diamond>\<not>\<^bold>\<A>E!a\<close> using "KBasic2:3"[THEN "\<rightarrow>E"] "&E" by blast+
  AOT_have \<open>\<not>\<box>\<^bold>\<A>E!a\<close> using \<xi> "KBasic:11"[THEN "\<equiv>E"(2)] by blast
  AOT_hence \<open>\<not>\<^bold>\<A>E!a\<close> using "Act-Basic:6"[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)] by blast
  AOT_hence \<open>\<diamond>E!a & \<not>\<^bold>\<A>E!a\<close> using \<theta> "&I" by blast
  thus ?thesis using "\<exists>I" by fast
qed

AOT_define contingent_prop :: \<phi> ("q\<^sub>0")
  q\<^sub>0_def: \<open>(q\<^sub>0) =\<^sub>d\<^sub>f (\<exists>x (E!x & \<not>\<^bold>\<A>E!x))\<close>

AOT_theorem q\<^sub>0_prop: \<open>\<diamond>q\<^sub>0 & \<diamond>\<not>q\<^sub>0\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF q\<^sub>0_def])
  apply (fact "log-prop-prop:2")
  apply (rule "&I")
   apply (fact "qml:4"[axiom_inst])
  by (fact pos_not_pna_2)

AOT_theorem basic_prop_1: \<open>Contingent0((q\<^sub>0))\<close>
proof(rule contingent_properties_4_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_have \<open>\<not>Necessary0((q\<^sub>0)) & \<not>Impossible0((q\<^sub>0))\<close>
  proof (rule "&I"; rule "=\<^sub>d\<^sub>fI"(2)[OF q\<^sub>0_def]; (rule "log-prop-prop:2" | rule "raa-cor:2"))
    AOT_assume \<open>Necessary0(\<exists>x (E!x & \<not>\<^bold>\<A>E!x))\<close>
    AOT_hence \<open>\<box>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
      using contingent_properties_1_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    AOT_hence \<open>\<^bold>\<A>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
      using "Act-Basic:8"[THEN "\<rightarrow>E"] "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>\<^bold>\<A>\<exists>x (E!x & \<not>\<^bold>\<A>E!x) & \<not>\<^bold>\<A>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
      using pos_not_pna_1 "&I" by blast
  next
    AOT_assume \<open>Impossible0(\<exists>x (E!x & \<not>\<^bold>\<A>E!x))\<close>
    AOT_hence \<open>\<box>\<not>(\<exists>x (E!x & \<not>\<^bold>\<A>E!x))\<close>
      using contingent_properties_2_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    AOT_hence \<open>\<not>\<diamond>(\<exists>x (E!x & \<not>\<^bold>\<A>E!x))\<close> using "KBasic2:1"[THEN "\<equiv>E"(1)] by blast
    AOT_thus \<open>\<diamond>(\<exists>x (E!x & \<not>\<^bold>\<A>E!x)) & \<not>\<diamond>(\<exists>x (E!x & \<not>\<^bold>\<A>E!x))\<close>
      using "qml:4"[axiom_inst] "&I" by blast
  qed
  AOT_thus \<open>\<not>(Necessary0((q\<^sub>0)) \<or> Impossible0((q\<^sub>0)))\<close>
    using "oth-class-taut:5:d" "\<equiv>E"(2) by blast
qed

AOT_theorem basic_prop_2: \<open>\<exists>p Contingent0((p))\<close>
  using "\<exists>I"(1)[rotated, OF "log-prop-prop:2"] basic_prop_1 by blast

AOT_theorem basic_prop_3: \<open>Contingent0(((q\<^sub>0)\<^sup>-))\<close>
  apply (AOT_subst "\<guillemotleft>(q\<^sub>0)\<^sup>-\<guillemotright>" "\<guillemotleft>\<not>q\<^sub>0\<guillemotright>")
   apply (insert thm_relation_negation_3 "\<forall>I" "\<forall>E"(1)[rotated, OF "log-prop-prop:2"]; fast)
  apply (rule contingent_properties_4_0[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  apply (rule "oth-class-taut:5:d"[THEN "\<equiv>E"(2)])
  apply (rule "&I")
   apply (rule contingent_properties_1_0[THEN "df-rules-formulas[3]", THEN "useful-tautologies:5"[THEN "\<rightarrow>E"], THEN "\<rightarrow>E"])
   apply (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fE"])
   apply (rule "=\<^sub>d\<^sub>fE"(2)[OF q\<^sub>0_def])
    apply (rule "log-prop-prop:2")
   apply (rule q\<^sub>0_prop[THEN "&E"(1)])
  apply (rule contingent_properties_2_0[THEN "df-rules-formulas[3]", THEN "useful-tautologies:5"[THEN "\<rightarrow>E"], THEN "\<rightarrow>E"])
  apply (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  by (rule q\<^sub>0_prop[THEN "&E"(2)])

AOT_theorem basic_prop_4: \<open>\<exists>p\<exists>q (p \<noteq> q & Contingent0(p) & Contingent0(q))\<close>
proof(rule "\<exists>I")+
  AOT_have 0: \<open>\<phi> \<noteq> (\<phi>)\<^sup>-\<close> for \<phi>
    using thm_relation_negation_6 "\<forall>I" "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by fast
  AOT_show \<open>(q\<^sub>0) \<noteq> (q\<^sub>0)\<^sup>- & Contingent0(q\<^sub>0) & Contingent0(((q\<^sub>0)\<^sup>-))\<close>
    using basic_prop_1 basic_prop_3 "&I" 0 by presburger
qed(auto simp: "log-prop-prop:2")

AOT_theorem proposition_facts_1: \<open>NonContingent0(p) \<rightarrow> \<not>\<exists>q (Contingent0(q) & q = p)\<close>
proof(rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_assume \<open>NonContingent0(p)\<close>
  AOT_hence 1: \<open>Necessary0(p) \<or> Impossible0(p)\<close>
    using contingent_properties_3_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_assume \<open>\<exists>q (Contingent0(q) & q = p)\<close>
  then AOT_obtain q where \<open>Contingent0(q) & q = p\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>Contingent0(p)\<close> using "=E" "&E" by fast
  AOT_thus \<open>(Necessary0(p) \<or> Impossible0(p)) & \<not>(Necessary0(p) \<or> Impossible0(p))\<close>
    using contingent_properties_4_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] 1 "&I" by blast
qed

AOT_theorem proposition_facts_2: \<open>Contingent0(p) \<rightarrow> \<not>\<exists>q (NonContingent0(q) & q = p)\<close>
proof(rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_assume \<open>Contingent0(p)\<close>
  AOT_hence 1: \<open>\<not>(Necessary0(p) \<or> Impossible0(p))\<close>
    using contingent_properties_4_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_assume \<open>\<exists>q (NonContingent0(q) & q = p)\<close>
  then AOT_obtain q where \<open>NonContingent0(q) & q = p\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>NonContingent0(p)\<close> using "=E" "&E" by fast
  AOT_thus \<open>(Necessary0(p) \<or> Impossible0(p)) & \<not>(Necessary0(p) \<or> Impossible0(p))\<close>
    using contingent_properties_3_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] 1 "&I" by blast
qed

AOT_theorem proposition_facts_3: \<open>(p\<^sub>0) \<noteq> (p\<^sub>0)\<^sup>- & (p\<^sub>0) \<noteq> (q\<^sub>0) & (p\<^sub>0) \<noteq> (q\<^sub>0)\<^sup>- & (p\<^sub>0)\<^sup>- \<noteq> (q\<^sub>0)\<^sup>- & (q\<^sub>0) \<noteq> (q\<^sub>0)\<^sup>-\<close>
proof -
  {
    fix \<chi> \<phi> \<psi>
    AOT_assume \<open>\<chi>{\<phi>}\<close>
    moreover AOT_assume \<open>\<not>\<chi>{\<psi>}\<close>
    ultimately AOT_have \<open>\<not>(\<chi>{\<phi>} \<equiv> \<chi>{\<psi>})\<close>
      using RAA "\<equiv>E" by metis
    moreover {
      AOT_have \<open>\<forall>p\<forall>q ((\<not>(\<chi>{p} \<equiv> \<chi>{q})) \<rightarrow> p \<noteq> q)\<close>
        by (rule "\<forall>I"; rule "\<forall>I"; rule pos_not_equiv_ne_4_0)
      AOT_hence \<open>((\<not>(\<chi>{\<phi>} \<equiv> \<chi>{\<psi>})) \<rightarrow> \<phi> \<noteq> \<psi>)\<close>
        using "\<forall>E" "log-prop-prop:2" by blast
    }
    ultimately AOT_have \<open>\<phi> \<noteq> \<psi>\<close>
      using "\<rightarrow>E" by blast
  } note 0 = this
  AOT_have contingent_neg: \<open>Contingent0(\<phi>) \<equiv> Contingent0(((\<phi>)\<^sup>-))\<close> for \<phi>
    using thm_cont_propos_3 "\<forall>I" "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by fast
  AOT_have not_noncontingent_if_contingent: \<open>\<not>NonContingent0(\<phi>)\<close> if \<open>Contingent0(\<phi>)\<close> for \<phi>
    apply (rule contingent_properties_3_0[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)])
    using that contingent_properties_4_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  show ?thesis
    apply (rule "&I")+
    using thm_relation_negation_6 "\<forall>I" "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] apply fast
       apply (rule 0)
    using thm_noncont_propos_3 apply fast
       apply (rule not_noncontingent_if_contingent)
       apply (fact AOT)
      apply (rule 0)
    apply (rule thm_noncont_propos_3)
      apply (rule not_noncontingent_if_contingent)
      apply (rule contingent_neg[THEN "\<equiv>E"(1)])
      apply (fact AOT)
     apply (rule 0)
    apply (rule thm_noncont_propos_4)
      apply (rule not_noncontingent_if_contingent)
      apply (rule contingent_neg[THEN "\<equiv>E"(1)])
     apply (fact AOT)
    using thm_relation_negation_6 "\<forall>I" "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by fast
qed

AOT_define cont_tf_1 :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("ContingentlyTrue'(_')")
  cont_tf_1: \<open>ContingentlyTrue(p) \<equiv>\<^sub>d\<^sub>f p & \<diamond>\<not>p\<close>

AOT_define cont_tf_2 :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("ContingentlyFalse'(_')")
  cont_tf_2: \<open>ContingentlyFalse(p) \<equiv>\<^sub>d\<^sub>f \<not>p & \<diamond>p\<close>

AOT_theorem cont_true_cont_1: \<open>ContingentlyTrue((p)) \<rightarrow> Contingent0((p))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>ContingentlyTrue((p))\<close>
  AOT_hence 1: \<open>p\<close> and 2: \<open>\<diamond>\<not>p\<close> using cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>\<not>Necessary0((p))\<close>
    apply (rule contingent_properties_1_0[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)])
    using 2 "KBasic:11"[THEN "\<equiv>E"(2)] by blast
  moreover AOT_have \<open>\<not>Impossible0((p))\<close>
    apply (rule contingent_properties_2_0[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)])
    apply (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fE"])
    using "T\<diamond>"[THEN "\<rightarrow>E", OF 1].
  ultimately AOT_have \<open>\<not>(Necessary0((p)) \<or> Impossible0((p)))\<close>
    using DeMorgan(2)[THEN "\<equiv>E"(2)] "&I" by blast
  AOT_thus \<open>Contingent0((p))\<close>
    using contingent_properties_4_0[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

AOT_theorem cont_true_cont_2: \<open>ContingentlyFalse((p)) \<rightarrow> Contingent0((p))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>ContingentlyFalse((p))\<close>
  AOT_hence 1: \<open>\<not>p\<close> and 2: \<open>\<diamond>p\<close> using cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>\<not>Necessary0((p))\<close>
    apply (rule contingent_properties_1_0[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)])
    using "KBasic:11"[THEN "\<equiv>E"(2)] "T\<diamond>"[THEN "\<rightarrow>E", OF 1] by blast
  moreover AOT_have \<open>\<not>Impossible0((p))\<close>
    apply (rule contingent_properties_2_0[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)])
    apply (rule AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fE"])
    using 2.
  ultimately AOT_have \<open>\<not>(Necessary0((p)) \<or> Impossible0((p)))\<close>
    using DeMorgan(2)[THEN "\<equiv>E"(2)] "&I" by blast
  AOT_thus \<open>Contingent0((p))\<close>
    using contingent_properties_4_0[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

AOT_theorem cont_true_cont_3: \<open>ContingentlyTrue((p)) \<equiv> ContingentlyFalse(((p)\<^sup>-))\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>ContingentlyTrue((p))\<close>
  AOT_hence 0: \<open>p & \<diamond>\<not>p\<close> using cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have 1: \<open>ContingentlyFalse(\<not>p)\<close>
    apply (rule cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    apply (AOT_subst_rev "AOT_term_of_var p" "\<guillemotleft>\<not>\<not>p\<guillemotright>")
    by (auto simp: "oth-class-taut:3:b" 0)
  AOT_show \<open>ContingentlyFalse(((p)\<^sup>-))\<close>
    apply (AOT_subst "\<guillemotleft>(p)\<^sup>-\<guillemotright>" "\<guillemotleft>\<not>p\<guillemotright>")
    by (auto simp: thm_relation_negation_3 1)
next
  AOT_assume 1: \<open>ContingentlyFalse(((p)\<^sup>-))\<close>
  AOT_have \<open>ContingentlyFalse(\<not>p)\<close>
    by (AOT_subst_rev "\<guillemotleft>(p)\<^sup>-\<guillemotright>" "\<guillemotleft>\<not>p\<guillemotright>")
       (auto simp: thm_relation_negation_3 1)
  AOT_hence \<open>\<not>\<not>p & \<diamond>\<not>p\<close> using cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence \<open>p & \<diamond>\<not>p\<close>
    using "&I" "&E" "useful-tautologies:1"[THEN "\<rightarrow>E"] by metis
  AOT_thus \<open>ContingentlyTrue((p))\<close>
    using cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

AOT_theorem cont_true_cont_4: \<open>ContingentlyFalse((p)) \<equiv> ContingentlyTrue(((p)\<^sup>-))\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>ContingentlyFalse(p)\<close>
  AOT_hence 0: \<open>\<not>p & \<diamond>p\<close>
    using cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have \<open>\<not>p & \<diamond>\<not>\<not>p\<close>
    by (AOT_subst_rev "AOT_term_of_var p" "\<guillemotleft>\<not>\<not>p\<guillemotright>")
       (auto simp: "oth-class-taut:3:b" 0)
  AOT_hence 1: \<open>ContingentlyTrue(\<not>p)\<close>
    by (rule cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_show \<open>ContingentlyTrue(((p)\<^sup>-))\<close>
    by (AOT_subst "\<guillemotleft>(p)\<^sup>-\<guillemotright>" "\<guillemotleft>\<not>p\<guillemotright>")
       (auto simp: thm_relation_negation_3 1)
next
  AOT_assume 1: \<open>ContingentlyTrue(((p)\<^sup>-))\<close>
  AOT_have \<open>ContingentlyTrue(\<not>p)\<close>
    by (AOT_subst_rev "\<guillemotleft>(p)\<^sup>-\<guillemotright>" "\<guillemotleft>\<not>p\<guillemotright>")
       (auto simp add: thm_relation_negation_3 1)
  AOT_hence 2: \<open>\<not>p & \<diamond>\<not>\<not>p\<close> using cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have \<open>\<diamond>p\<close>
    by (AOT_subst "AOT_term_of_var p" "\<guillemotleft>\<not>\<not>p\<guillemotright>")
       (auto simp add: "oth-class-taut:3:b" 2[THEN "&E"(2)])
  AOT_hence \<open>\<not>p & \<diamond>p\<close> using 2[THEN "&E"(1)] "&I" by blast
  AOT_thus \<open>ContingentlyFalse(p)\<close>
    by (rule cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed

AOT_theorem cont_true_cont_5: \<open>(ContingentlyTrue((p)) & Necessary0((q))) \<rightarrow> p \<noteq> q\<close>
proof (rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); rule "raa-cor:1")
  AOT_assume \<open>ContingentlyTrue((p))\<close>
  AOT_hence \<open>\<diamond>\<not>p\<close>
    using cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence 0: \<open>\<not>\<box>p\<close> using "KBasic:11"[THEN "\<equiv>E"(2)] by blast
  AOT_assume \<open>Necessary0((q))\<close>
  moreover AOT_assume \<open>\<not>(p \<noteq> q)\<close>
  AOT_hence \<open>p = q\<close>
    using "=-infix"[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1)]
          "useful-tautologies:1"[THEN "\<rightarrow>E"] by blast
  ultimately AOT_have \<open>Necessary0((p))\<close> using "=E" id_sym by blast
  AOT_hence \<open>\<box>p\<close>
    using contingent_properties_1_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_thus \<open>\<box>p & \<not>\<box>p\<close> using 0 "&I" by blast
qed

AOT_theorem cont_true_cont_6: \<open>(ContingentlyFalse((p)) & Impossible0((q))) \<rightarrow> p \<noteq> q\<close>
proof (rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); rule "raa-cor:1")
  AOT_assume \<open>ContingentlyFalse((p))\<close>
  AOT_hence \<open>\<diamond>p\<close>
    using cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence 1: \<open>\<not>\<box>\<not>p\<close>
    using AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_assume \<open>Impossible0((q))\<close>
  moreover AOT_assume \<open>\<not>(p \<noteq> q)\<close>
  AOT_hence \<open>p = q\<close>
    using "=-infix"[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1)]
          "useful-tautologies:1"[THEN "\<rightarrow>E"] by blast
  ultimately AOT_have \<open>Impossible0((p))\<close> using "=E" id_sym by blast
  AOT_hence \<open>\<box>\<not>p\<close>
    using contingent_properties_2_0[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_thus \<open>\<box>\<not>p & \<not>\<box>\<not>p\<close> using 1 "&I" by blast
qed

AOT_act_theorem q0cf_1: \<open>ContingentlyFalse(q\<^sub>0)\<close>
  apply (rule cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF q\<^sub>0_def])
   apply (fact "log-prop-prop:2")
  apply (rule "&I")
   apply (fact no_cnac)
  by (fact "qml:4"[axiom_inst])

AOT_act_theorem q0cf_2: \<open>ContingentlyTrue(((q\<^sub>0)\<^sup>-))\<close>
  apply (rule cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF q\<^sub>0_def])
   apply (fact "log-prop-prop:2")
  apply (rule "&I")
     apply (rule thm_relation_negation_3[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2)])
     apply (fact no_cnac)
    apply (rule "=E"[rotated, OF thm_relation_negation_7[unvarify p, OF "log-prop-prop:2", THEN id_sym]])
  apply (AOT_subst_rev "\<guillemotleft>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<guillemotright>" "\<guillemotleft>\<not>\<not>(\<exists>x  (E!x & \<not>\<^bold>\<A>E!x))\<guillemotright>")
  by (auto simp: "oth-class-taut:3:b" "qml:4"[axiom_inst])

(* TODO: q0cf-rem skipped for now *)

AOT_theorem cont_tf_thm_1: \<open>\<exists>p ContingentlyTrue((p))\<close>
proof(rule "\<or>E"(1)[OF "exc-mid"]; rule "\<rightarrow>I"; rule "\<exists>I")
  AOT_assume \<open>q\<^sub>0\<close>
  AOT_hence \<open>q\<^sub>0 & \<diamond>\<not>q\<^sub>0\<close> using q\<^sub>0_prop[THEN "&E"(2)] "&I" by blast
  AOT_thus \<open>ContingentlyTrue(q\<^sub>0)\<close>
    by (rule cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
next
  AOT_assume \<open>\<not>q\<^sub>0\<close>
  AOT_hence \<open>\<not>q\<^sub>0 & \<diamond>q\<^sub>0\<close> using q\<^sub>0_prop[THEN "&E"(1)] "&I" by blast
  AOT_hence \<open>ContingentlyFalse(q\<^sub>0)\<close>
    by (rule cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_thus \<open>ContingentlyTrue(((q\<^sub>0)\<^sup>-))\<close>
    by (rule cont_true_cont_4[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)])
qed(auto simp: "log-prop-prop:2")


AOT_theorem cont_tf_thm_2: \<open>\<exists>p ContingentlyFalse((p))\<close>
proof(rule "\<or>E"(1)[OF "exc-mid"]; rule "\<rightarrow>I"; rule "\<exists>I")
  AOT_assume \<open>q\<^sub>0\<close>
  AOT_hence \<open>q\<^sub>0 & \<diamond>\<not>q\<^sub>0\<close> using q\<^sub>0_prop[THEN "&E"(2)] "&I" by blast
  AOT_hence \<open>ContingentlyTrue(q\<^sub>0)\<close>
    by (rule cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_thus \<open>ContingentlyFalse(((q\<^sub>0)\<^sup>-))\<close>
    by (rule cont_true_cont_3[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)])
next
  AOT_assume \<open>\<not>q\<^sub>0\<close>
  AOT_hence \<open>\<not>q\<^sub>0 & \<diamond>q\<^sub>0\<close> using q\<^sub>0_prop[THEN "&E"(1)] "&I" by blast
  AOT_thus \<open>ContingentlyFalse(q\<^sub>0)\<close>
    by (rule cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed(auto simp: "log-prop-prop:2")

(* TODO: inspect modally strict subproof involving obtained variable *)
AOT_theorem property_facts1_1: \<open>\<exists>F\<exists>x ([F]x & \<diamond>\<not>[F]x)\<close>
proof -
  fix x
  AOT_obtain p\<^sub>1 where \<open>ContingentlyTrue((p\<^sub>1))\<close>
    using cont_tf_thm_1 "\<exists>E"[rotated] by blast
  AOT_hence 1: \<open>p\<^sub>1 & \<diamond>\<not>p\<^sub>1\<close> using cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_modally_strict {
    AOT_have \<open>for arbitrary p: \<^bold>\<turnstile>\<^sub>\<box> ([\<lambda>z p]x \<equiv> p)\<close>
      by (rule beta_C_cor_3[THEN "\<forall>E"(2)]) cqt_2_lambda_inst_prover
    AOT_hence \<open>for arbitrary p: \<^bold>\<turnstile>\<^sub>\<box> \<box> ([\<lambda>z p]x \<equiv> p)\<close>
      by (rule RN)
    AOT_hence \<open>\<forall>p \<box>([\<lambda>z p]x \<equiv> p)\<close> using GEN by fast
    AOT_hence \<open>\<box>([\<lambda>z p\<^sub>1]x \<equiv> p\<^sub>1)\<close> using "\<forall>E" by fast
  } note 2 = this
  AOT_hence \<open>\<box>([\<lambda>z p\<^sub>1]x \<equiv> p\<^sub>1)\<close> using "\<forall>E" by blast
  AOT_hence \<open>[\<lambda>z p\<^sub>1]x\<close> using 1[THEN "&E"(1)] "qml:2"[axiom_inst, THEN "\<rightarrow>E"] "\<equiv>E"(2) by blast
  moreover AOT_have \<open>\<diamond>\<not>[\<lambda>z p\<^sub>1]x\<close>
    apply (AOT_subst_using subst: 2[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]])
    using 1[THEN "&E"(2)] by blast
  ultimately AOT_have \<open>[\<lambda>z p\<^sub>1]x & \<diamond>\<not>[\<lambda>z p\<^sub>1]x\<close> using "&I" by blast
  AOT_hence \<open>\<exists>x ([\<lambda>z p\<^sub>1]x & \<diamond>\<not>[\<lambda>z p\<^sub>1]x)\<close> using "\<exists>I"(2) by fast
  moreover AOT_have \<open>[\<lambda>z p\<^sub>1]\<down>\<close> by "cqt:2[lambda]"
  ultimately AOT_show \<open>\<exists>F\<exists>x ([F]x & \<diamond>\<not>[F]x)\<close> by (rule "\<exists>I"(1))
qed

(* TODO: inspect modally strict subproof involving obtained variable *)
AOT_theorem property_facts1_2: \<open>\<exists>F\<exists>x (\<not>[F]x & \<diamond>[F]x)\<close>
proof -
  fix x
  AOT_obtain p\<^sub>1 where \<open>ContingentlyFalse((p\<^sub>1))\<close>
    using cont_tf_thm_2 "\<exists>E"[rotated] by blast
  AOT_hence 1: \<open>\<not>p\<^sub>1 & \<diamond>p\<^sub>1\<close> using cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_modally_strict {
    AOT_have \<open>for arbitrary p: \<^bold>\<turnstile>\<^sub>\<box> ([\<lambda>z p]x \<equiv> p)\<close>
      by (rule beta_C_cor_3[THEN "\<forall>E"(2)]) cqt_2_lambda_inst_prover
    AOT_hence \<open>for arbitrary p: \<^bold>\<turnstile>\<^sub>\<box> (\<not>[\<lambda>z p]x \<equiv> \<not>p)\<close>
      using "oth-class-taut:4:b" "\<equiv>E" by blast
    AOT_hence \<open>for arbitrary p: \<^bold>\<turnstile>\<^sub>\<box> \<box>(\<not>[\<lambda>z p]x \<equiv> \<not>p)\<close>
      by (rule RN)
    AOT_hence \<open>\<forall>p \<box>(\<not>[\<lambda>z p]x \<equiv> \<not>p)\<close> using GEN by fast
    AOT_hence \<open>\<box>(\<not>[\<lambda>z p\<^sub>1]x \<equiv> \<not>p\<^sub>1)\<close> using "\<forall>E" by fast
  } note 2 = this
  AOT_hence \<open>\<box>(\<not>[\<lambda>z p\<^sub>1]x \<equiv> \<not>p\<^sub>1)\<close> using "\<forall>E" by blast
  AOT_hence 3: \<open>\<not>[\<lambda>z p\<^sub>1]x\<close> using 1[THEN "&E"(1)] "qml:2"[axiom_inst, THEN "\<rightarrow>E"] "\<equiv>E"(2) by blast
  AOT_modally_strict {
    AOT_have \<open>for arbitrary p: \<^bold>\<turnstile>\<^sub>\<box> ([\<lambda>z p]x \<equiv> p)\<close>
      by (rule beta_C_cor_3[THEN "\<forall>E"(2)]) cqt_2_lambda_inst_prover
    AOT_hence \<open>for arbitrary p: \<^bold>\<turnstile>\<^sub>\<box> \<box>([\<lambda>z p]x \<equiv> p)\<close>
      by (rule RN)
    AOT_hence \<open>\<forall>p \<box>([\<lambda>z p]x \<equiv> p)\<close> using GEN by fast
    AOT_hence \<open>\<box>([\<lambda>z p\<^sub>1]x \<equiv> p\<^sub>1)\<close> using "\<forall>E" by fast
  } note 4 = this
  AOT_have \<open>\<diamond>[\<lambda>z p\<^sub>1]x\<close>
    apply (AOT_subst_using subst: 4[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]])
    using 1[THEN "&E"(2)] by blast
  AOT_hence \<open>\<not>[\<lambda>z p\<^sub>1]x & \<diamond>[\<lambda>z p\<^sub>1]x\<close> using 3 "&I" by blast
  AOT_hence \<open>\<exists>x (\<not>[\<lambda>z p\<^sub>1]x & \<diamond>[\<lambda>z p\<^sub>1]x)\<close> using "\<exists>I"(2) by fast
  moreover AOT_have \<open>[\<lambda>z p\<^sub>1]\<down>\<close> by "cqt:2[lambda]"
  ultimately AOT_show \<open>\<exists>F\<exists>x (\<not>[F]x & \<diamond>[F]x)\<close> by (rule "\<exists>I"(1))
qed

context
begin

private AOT_lemma eqnotnec_123_Aux_\<zeta>: \<open>[L]x \<equiv> (E!x \<rightarrow> E!x)\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def])
     apply "cqt:2[lambda]"
    apply (rule beta_C_meta[THEN "\<rightarrow>E"])
  by "cqt:2[lambda]"

private AOT_lemma eqnotnec_123_Aux_\<omega>: \<open>[\<lambda>z \<phi>]x \<equiv> \<phi>\<close>
    by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"

private AOT_lemma eqnotnec_123_Aux_\<theta>: \<open>\<phi> \<equiv> \<forall>x([L]x \<equiv> [\<lambda>z \<phi>]x)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I"; (rule "\<forall>I")?)
  fix x
  AOT_assume 1: \<open>\<phi>\<close>
  AOT_have \<open>[L]x \<equiv> (E!x \<rightarrow> E!x)\<close> using eqnotnec_123_Aux_\<zeta>.
  also AOT_have \<open>\<dots> \<equiv> \<phi>\<close>
    using "if-p-then-p" 1 "\<equiv>I" "\<rightarrow>I" by simp
  also AOT_have \<open>\<dots> \<equiv> [\<lambda>z \<phi>]x\<close>
    using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] eqnotnec_123_Aux_\<omega> by blast
  finally AOT_show \<open>[L]x \<equiv> [\<lambda>z \<phi>]x\<close>.
next
  fix x
  AOT_assume \<open>\<forall>x([L]x \<equiv> [\<lambda>z \<phi>]x)\<close>
  AOT_hence \<open>[L]x \<equiv> [\<lambda>z \<phi>]x\<close> using "\<forall>E" by blast
  also AOT_have \<open>\<dots> \<equiv> \<phi>\<close> using eqnotnec_123_Aux_\<omega>.
  finally AOT_have \<open>\<phi> \<equiv> [L]x\<close> using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by blast
  also AOT_have \<open>\<dots> \<equiv> E!x \<rightarrow> E!x\<close> using eqnotnec_123_Aux_\<zeta>.
  finally AOT_show \<open>\<phi>\<close> using "\<equiv>E" "if-p-then-p" by fast
qed
private lemmas eqnotnec_123_Aux_\<xi> =  eqnotnec_123_Aux_\<theta>[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)],
                      THEN AOT_equiv[THEN "\<equiv>Df", THEN "\<equiv>E"(1), THEN "&E"(1)],
                      THEN "RM\<diamond>"]
private lemmas eqnotnec_123_Aux_\<xi>' = eqnotnec_123_Aux_\<theta>[THEN AOT_equiv[THEN "\<equiv>Df", THEN "\<equiv>E"(1), THEN "&E"(1)], THEN "RM\<diamond>"]

AOT_theorem eqnotnec_1: \<open>\<exists>F\<exists>G(\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<not>\<forall>x([F]x \<equiv> [G]x))\<close>
proof-
  AOT_obtain p\<^sub>1 where \<open>ContingentlyTrue(p\<^sub>1)\<close> using cont_tf_thm_1 "\<exists>E"[rotated] by blast
  AOT_hence \<open>p\<^sub>1 & \<diamond>\<not>p\<^sub>1\<close> using cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence \<open>\<forall>x ([L]x \<equiv> [\<lambda>z p\<^sub>1]x) & \<diamond>\<not>\<forall>x([L]x \<equiv> [\<lambda>z p\<^sub>1]x)\<close>
    apply - apply (rule "&I")
    using "&E" eqnotnec_123_Aux_\<theta>[THEN "\<equiv>E"(1)] eqnotnec_123_Aux_\<xi> "\<rightarrow>E" by fast+
  AOT_hence \<open>\<exists>G (\<forall>x([L]x \<equiv> [G]x) & \<diamond>\<not>\<forall>x([L]x \<equiv> [G]x))\<close>
    by (rule "\<exists>I") "cqt:2[lambda]"
  AOT_thus \<open>\<exists>F\<exists>G (\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<not>\<forall>x([F]x \<equiv> [G]x))\<close>
    apply (rule "\<exists>I")
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
qed

AOT_theorem eqnotnec_2: \<open>\<exists>F\<exists>G(\<not>\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
proof-
  AOT_obtain p\<^sub>1 where \<open>ContingentlyFalse(p\<^sub>1)\<close> using cont_tf_thm_2 "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<not>p\<^sub>1 & \<diamond>p\<^sub>1\<close> using cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence \<open>\<not>\<forall>x ([L]x \<equiv> [\<lambda>z p\<^sub>1]x) & \<diamond>\<forall>x([L]x \<equiv> [\<lambda>z p\<^sub>1]x)\<close>
    apply - apply (rule "&I")
    using "&E" eqnotnec_123_Aux_\<theta>[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1)] eqnotnec_123_Aux_\<xi>' "\<rightarrow>E" by fast+
  AOT_hence \<open>\<exists>G (\<not>\<forall>x([L]x \<equiv> [G]x) & \<diamond>\<forall>x([L]x \<equiv> [G]x))\<close>
    by (rule "\<exists>I") "cqt:2[lambda]"
  AOT_thus \<open>\<exists>F\<exists>G (\<not>\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
    apply (rule "\<exists>I")
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
qed

AOT_theorem eqnotnec_3: \<open>\<exists>F\<exists>G(\<^bold>\<A>\<not>\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
proof-
  AOT_have \<open>\<not>\<^bold>\<A>q\<^sub>0\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF q\<^sub>0_def])
     apply (fact "log-prop-prop:2")
    by (fact AOT)
  AOT_hence \<open>\<^bold>\<A>\<not>q\<^sub>0\<close>
    using "logic-actual-nec:1"[axiom_inst, THEN "\<equiv>E"(2)] by blast
  AOT_hence \<open>\<^bold>\<A>\<not>\<forall>x ([L]x \<equiv> [\<lambda>z q\<^sub>0]x)\<close>
    using eqnotnec_123_Aux_\<theta>[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)],
            THEN AOT_equiv[THEN "\<equiv>Df", THEN "\<equiv>E"(1), THEN "&E"(1)],
            THEN "RA[2]", THEN "act-cond"[THEN "\<rightarrow>E"], THEN "\<rightarrow>E"] by blast
  moreover AOT_have \<open>\<diamond>\<forall>x ([L]x \<equiv> [\<lambda>z q\<^sub>0]x)\<close> using eqnotnec_123_Aux_\<xi>'[THEN "\<rightarrow>E"] q\<^sub>0_prop[THEN "&E"(1)] by blast
  ultimately AOT_have \<open>\<^bold>\<A>\<not>\<forall>x ([L]x \<equiv> [\<lambda>z q\<^sub>0]x) & \<diamond>\<forall>x ([L]x \<equiv> [\<lambda>z q\<^sub>0]x)\<close> using "&I" by blast
  AOT_hence \<open>\<exists>G (\<^bold>\<A>\<not>\<forall>x([L]x \<equiv> [G]x) & \<diamond>\<forall>x([L]x \<equiv> [G]x))\<close>
    by (rule "\<exists>I") "cqt:2[lambda]"
  AOT_thus \<open>\<exists>F\<exists>G (\<^bold>\<A>\<not>\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
    apply (rule "\<exists>I")
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
qed

end

(* TODO[IMPORTANT]: proof of 219.4 \<zeta>: appeal to (159.2) requires a theorem, but the result has local
   assumptions! *)
AOT_theorem eqnotnec_4: \<open>\<forall>F\<exists>G(\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<not>\<forall>x([F]x \<equiv> [G]x))\<close>
proof(rule GEN)
  fix F

  AOT_have Aux_A: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<psi> \<rightarrow> \<forall>x([F]x \<equiv> [\<lambda>z [F]z & \<psi>]x)\<close> for \<psi>
  proof(rule "\<rightarrow>I"; rule GEN)
    AOT_modally_strict {
    fix x
    AOT_assume 0: \<open>\<psi>\<close>
    AOT_have \<open>[\<lambda>z [F]z & \<psi>]x \<equiv> [F]x & \<psi>\<close>
      by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
    also AOT_have \<open>... \<equiv> [F]x\<close>
      apply (rule "\<equiv>I"; rule "\<rightarrow>I")
      using  "\<or>E"(3)[rotated, OF "useful-tautologies:2"[THEN "\<rightarrow>E"], OF 0] "&E" apply blast
      using 0 "&I" by blast
    finally AOT_show \<open>[F]x \<equiv> [\<lambda>z [F]z & \<psi>]x\<close>
      using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by blast
    }
  qed

  AOT_have Aux_B: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<psi> \<rightarrow> \<forall>x([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> for \<psi>
  proof (rule "\<rightarrow>I"; rule GEN)
    AOT_modally_strict {
      fix x
      AOT_assume 0: \<open>\<psi>\<close>
      AOT_have \<open>[\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]x \<equiv> (([F]x & \<psi>) \<or> \<not>\<psi>)\<close>
        by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      also AOT_have \<open>... \<equiv> [F]x\<close>
        apply (rule "\<equiv>I"; rule "\<rightarrow>I")
        using  "\<or>E"(3)[rotated, OF "useful-tautologies:2"[THEN "\<rightarrow>E"], OF 0] "&E" apply blast
        apply (rule "\<or>I"(1)) using 0 "&I" by blast
      finally AOT_show \<open>[F]x \<equiv> [\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]x\<close>
        using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by blast
    }
  qed

  AOT_have Aux_C: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<not>\<psi> \<rightarrow> \<diamond>\<not>\<forall>z([\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z)\<close> for \<psi>
  proof(rule "RM\<diamond>"; rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_modally_strict {
      AOT_assume 0: \<open>\<not>\<psi>\<close>
      AOT_assume \<open>\<forall>z ([\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z)\<close>
      AOT_hence \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
      moreover AOT_have \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [F]z & \<psi>\<close> for z
          by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      moreover AOT_have \<open>[\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]z \<equiv> (([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z
        by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      ultimately AOT_have \<open>[F]z & \<psi> \<equiv> (([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z
        using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] "\<equiv>E"(5) by meson
      moreover AOT_have \<open>(([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z using 0 "\<or>I" by blast
      ultimately AOT_have \<open>\<psi>\<close> using "\<equiv>E" "&E" by metis
      AOT_thus \<open>\<psi> & \<not>\<psi>\<close> using 0 "&I" by blast
    }
  qed

  AOT_have Aux_D: \<open>\<box>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z) \<rightarrow> (\<diamond>\<not>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x) \<equiv> \<diamond>\<not>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x))\<close> for \<psi>
  proof (rule "\<rightarrow>I")
    AOT_assume A: \<open>\<box>\<forall>z([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
    AOT_show \<open>\<diamond>\<not>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x) \<equiv> \<diamond>\<not>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close>
    proof(rule "\<equiv>I"; rule "KBasic:13"[THEN "\<rightarrow>E"];
          rule "RN[prem]"[where \<Gamma>="{\<guillemotleft>\<forall>z([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<guillemotright>}", simplified];
          (rule "useful-tautologies:5"[THEN "\<rightarrow>E"]; rule "\<rightarrow>I")?)
      AOT_modally_strict {
        AOT_assume \<open>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
        AOT_hence 1: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi>]z\<close> for z using "\<forall>E" by blast
        AOT_assume \<open>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close>
        AOT_hence 2: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
        AOT_have \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<equiv>E" 1 2 by meson
        AOT_thus \<open>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> by (rule GEN)
      }
    next
      AOT_modally_strict {
        AOT_assume \<open>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
        AOT_hence 1: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi>]z\<close> for z using "\<forall>E" by blast
        AOT_assume \<open>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close>
        AOT_hence 2: \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
        AOT_have \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using 1 2 "\<equiv>E" by meson
        AOT_thus \<open> \<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> by (rule GEN)
      }
    qed(auto simp: A)
  qed

  AOT_obtain p\<^sub>1 where p\<^sub>1_prop: \<open>p\<^sub>1 & \<diamond>\<not>p\<^sub>1\<close> using cont_tf_thm_1 "\<exists>E"[rotated] cont_tf_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  {
    AOT_assume 1: \<open>\<box>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x)\<close>
    AOT_have 2: \<open>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x)\<close>
      using Aux_B[THEN "\<rightarrow>E", OF p\<^sub>1_prop[THEN "&E"(1)]].
    AOT_have \<open>\<diamond>\<not>\<forall>x([\<lambda>z [F]z & p\<^sub>1]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x)\<close>
      using Aux_C[THEN "\<rightarrow>E", OF p\<^sub>1_prop[THEN "&E"(2)]].
    AOT_hence 3: \<open>\<diamond>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x)\<close>
      using Aux_D[THEN "\<rightarrow>E", OF 1, THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x) & \<diamond>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x)\<close> using 2 "&I" by blast
    AOT_hence \<open>\<exists>G (\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<not>\<forall>x([F]x \<equiv> [G]x))\<close>
      by (rule "\<exists>I"(1)) "cqt:2[lambda]"
  }
  moreover {
    AOT_assume 2: \<open>\<not>\<box>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x)\<close>
    AOT_hence \<open>\<diamond>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x)\<close>
      using "KBasic:11"[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x) & \<diamond>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x)\<close>
      using Aux_A[THEN "\<rightarrow>E", OF p\<^sub>1_prop[THEN "&E"(1)]] "&I" by blast
    AOT_hence \<open>\<exists>G (\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<not>\<forall>x([F]x \<equiv> [G]x))\<close>
      by (rule "\<exists>I"(1)) "cqt:2[lambda]"
  }
  ultimately AOT_show \<open>\<exists>G (\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<not>\<forall>x([F]x \<equiv> [G]x))\<close>
    using "\<or>E"(1)[OF "exc-mid"] "\<rightarrow>I" by blast
qed

AOT_theorem eqnotnec_5: \<open>\<forall>F\<exists>G(\<not>\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
proof(rule GEN)
  fix F

  AOT_have Aux_A: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<psi> \<rightarrow> \<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & \<psi>]x)\<close> for \<psi>
  proof(rule "RM\<diamond>"; rule "\<rightarrow>I"; rule GEN)
    AOT_modally_strict {
    fix x
    AOT_assume 0: \<open>\<psi>\<close>
    AOT_have \<open>[\<lambda>z [F]z & \<psi>]x \<equiv> [F]x & \<psi>\<close>
      by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
    also AOT_have \<open>... \<equiv> [F]x\<close>
      apply (rule "\<equiv>I"; rule "\<rightarrow>I")
      using  "\<or>E"(3)[rotated, OF "useful-tautologies:2"[THEN "\<rightarrow>E"], OF 0] "&E" apply blast
      using 0 "&I" by blast
    finally AOT_show \<open>[F]x \<equiv> [\<lambda>z [F]z & \<psi>]x\<close>
      using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by blast
    }
  qed

  AOT_have Aux_B: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<psi> \<rightarrow> \<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> for \<psi>
  proof (rule "RM\<diamond>"; rule "\<rightarrow>I"; rule GEN)
    AOT_modally_strict {
      fix x
      AOT_assume 0: \<open>\<psi>\<close>
      AOT_have \<open>[\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]x \<equiv> (([F]x & \<psi>) \<or> \<not>\<psi>)\<close>
        by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      also AOT_have \<open>... \<equiv> [F]x\<close>
        apply (rule "\<equiv>I"; rule "\<rightarrow>I")
        using  "\<or>E"(3)[rotated, OF "useful-tautologies:2"[THEN "\<rightarrow>E"], OF 0] "&E" apply blast
        apply (rule "\<or>I"(1)) using 0 "&I" by blast
      finally AOT_show \<open>[F]x \<equiv> [\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]x\<close>
        using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by blast
    }
  qed

  AOT_have Aux_C: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<not>\<psi> \<rightarrow> \<not>\<forall>z([\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z)\<close> for \<psi>
  proof(rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_modally_strict {
      AOT_assume 0: \<open>\<not>\<psi>\<close>
      AOT_assume \<open>\<forall>z ([\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z)\<close>
      AOT_hence \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
      moreover AOT_have \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [F]z & \<psi>\<close> for z
          by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      moreover AOT_have \<open>[\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]z \<equiv> (([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z
        by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      ultimately AOT_have \<open>[F]z & \<psi> \<equiv> (([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z
        using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] "\<equiv>E"(5) by meson
      moreover AOT_have \<open>(([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z using 0 "\<or>I" by blast
      ultimately AOT_have \<open>\<psi>\<close> using "\<equiv>E" "&E" by metis
      AOT_thus \<open>\<psi> & \<not>\<psi>\<close> using 0 "&I" by blast
    }
  qed

  AOT_have Aux_D: \<open>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z) \<rightarrow> (\<not>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x) \<equiv> \<not>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x))\<close> for \<psi>
  proof (rule "\<rightarrow>I"; rule "\<equiv>I"; (rule "useful-tautologies:5"[THEN "\<rightarrow>E"]; rule "\<rightarrow>I")?)
    AOT_modally_strict {
      AOT_assume \<open>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
      AOT_hence 1: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi>]z\<close> for z using "\<forall>E" by blast
      AOT_assume \<open>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close>
      AOT_hence 2: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
      AOT_have \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<equiv>E" 1 2 by meson
      AOT_thus \<open>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> by (rule GEN)
    }
  next
    AOT_modally_strict {
      AOT_assume \<open>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
      AOT_hence 1: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi>]z\<close> for z using "\<forall>E" by blast
      AOT_assume \<open>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close>
      AOT_hence 2: \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
      AOT_have \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using 1 2 "\<equiv>E" by meson
      AOT_thus \<open> \<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> by (rule GEN)
    }
  qed

  AOT_obtain p\<^sub>1 where p\<^sub>1_prop: \<open>\<not>p\<^sub>1 & \<diamond>p\<^sub>1\<close> using cont_tf_thm_2 "\<exists>E"[rotated] cont_tf_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  {
    AOT_assume 1: \<open>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x)\<close>
    AOT_have 2: \<open>\<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x)\<close>
      using Aux_B[THEN "\<rightarrow>E", OF p\<^sub>1_prop[THEN "&E"(2)]].
    AOT_have \<open>\<not>\<forall>x([\<lambda>z [F]z & p\<^sub>1]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x)\<close>
      using Aux_C[THEN "\<rightarrow>E", OF p\<^sub>1_prop[THEN "&E"(1)]].
    AOT_hence 3: \<open>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x)\<close>
      using Aux_D[THEN "\<rightarrow>E", OF 1, THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x) & \<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1 \<or> \<not>p\<^sub>1]x)\<close> using 2 "&I" by blast
    AOT_hence \<open>\<exists>G (\<not>\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
      by (rule "\<exists>I"(1)) "cqt:2[lambda]"
  }
  moreover {
    AOT_assume 2: \<open>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x)\<close>
    AOT_hence \<open>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x)\<close>
      using "KBasic:11"[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<not>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x) & \<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & p\<^sub>1]x)\<close>
      using Aux_A[THEN "\<rightarrow>E", OF p\<^sub>1_prop[THEN "&E"(2)]] "&I" by blast
    AOT_hence \<open>\<exists>G (\<not>\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
      by (rule "\<exists>I"(1)) "cqt:2[lambda]"
  }
  ultimately AOT_show \<open>\<exists>G (\<not>\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
    using "\<or>E"(1)[OF "exc-mid"] "\<rightarrow>I" by blast
qed

AOT_theorem eqnotnec_6: \<open>\<forall>F\<exists>G(\<^bold>\<A>\<not>\<forall>x([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
proof(rule GEN)
  fix F

  AOT_have Aux_A: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<psi> \<rightarrow> \<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & \<psi>]x)\<close> for \<psi>
  proof(rule "RM\<diamond>"; rule "\<rightarrow>I"; rule GEN)
    AOT_modally_strict {
    fix x
    AOT_assume 0: \<open>\<psi>\<close>
    AOT_have \<open>[\<lambda>z [F]z & \<psi>]x \<equiv> [F]x & \<psi>\<close>
      by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
    also AOT_have \<open>... \<equiv> [F]x\<close>
      apply (rule "\<equiv>I"; rule "\<rightarrow>I")
      using  "\<or>E"(3)[rotated, OF "useful-tautologies:2"[THEN "\<rightarrow>E"], OF 0] "&E" apply blast
      using 0 "&I" by blast
    finally AOT_show \<open>[F]x \<equiv> [\<lambda>z [F]z & \<psi>]x\<close>
      using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by blast
    }
  qed

  AOT_have Aux_B: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<psi> \<rightarrow> \<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> for \<psi>
  proof (rule "RM\<diamond>"; rule "\<rightarrow>I"; rule GEN)
    AOT_modally_strict {
      fix x
      AOT_assume 0: \<open>\<psi>\<close>
      AOT_have \<open>[\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]x \<equiv> (([F]x & \<psi>) \<or> \<not>\<psi>)\<close>
        by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      also AOT_have \<open>... \<equiv> [F]x\<close>
        apply (rule "\<equiv>I"; rule "\<rightarrow>I")
        using  "\<or>E"(3)[rotated, OF "useful-tautologies:2"[THEN "\<rightarrow>E"], OF 0] "&E" apply blast
        apply (rule "\<or>I"(1)) using 0 "&I" by blast
      finally AOT_show \<open>[F]x \<equiv> [\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]x\<close>
        using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by blast
    }
  qed

  AOT_have Aux_C: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<not>\<psi> \<rightarrow> \<^bold>\<A>\<not>\<forall>z([\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z)\<close> for \<psi>
  proof(rule "act-cond"[THEN "\<rightarrow>E"]; rule "RA[2]"; rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_modally_strict {
      AOT_assume 0: \<open>\<not>\<psi>\<close>
      AOT_assume \<open>\<forall>z ([\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z)\<close>
      AOT_hence \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
      moreover AOT_have \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [F]z & \<psi>\<close> for z
          by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      moreover AOT_have \<open>[\<lambda>z ([F]z & \<psi>) \<or> \<not>\<psi>]z \<equiv> (([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z
        by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
      ultimately AOT_have \<open>[F]z & \<psi> \<equiv> (([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z
        using "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] "\<equiv>E"(5) by meson
      moreover AOT_have \<open>(([F]z & \<psi>) \<or> \<not>\<psi>)\<close> for z using 0 "\<or>I" by blast
      ultimately AOT_have \<open>\<psi>\<close> using "\<equiv>E" "&E" by metis
      AOT_thus \<open>\<psi> & \<not>\<psi>\<close> using 0 "&I" by blast
    }
  qed

  AOT_have Aux_D: \<open>\<^bold>\<A>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z) \<rightarrow> (\<^bold>\<A>\<not>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x) \<equiv> \<^bold>\<A>\<not>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x))\<close> for \<psi>
  proof (rule "\<rightarrow>I"; rule "Act-Basic:5"[THEN "\<equiv>E"(1)])
    AOT_assume \<open>\<^bold>\<A>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
    AOT_thus \<open>\<^bold>\<A>(\<not>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x) \<equiv> \<not>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x))\<close>
    proof (rule "RA[3]"[where \<Gamma>="{\<guillemotleft>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<guillemotright>}", simplified, rotated])
      AOT_modally_strict {
        AOT_assume \<open>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
        AOT_thus \<open>\<not>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x) \<equiv> \<not>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close>
          apply -
        proof(rule "\<equiv>I"; (rule "useful-tautologies:5"[THEN "\<rightarrow>E"]; rule "\<rightarrow>I")?)
        AOT_modally_strict {
          AOT_assume \<open>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
          AOT_hence 1: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi>]z\<close> for z using "\<forall>E" by blast
          AOT_assume \<open>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close>
          AOT_hence 2: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
          AOT_have \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<equiv>E" 1 2 by meson
          AOT_thus \<open>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> by (rule GEN)
        }
      next
        AOT_modally_strict {
          AOT_assume \<open>\<forall>z ([F]z \<equiv> [\<lambda>z [F]z & \<psi>]z)\<close>
          AOT_hence 1: \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi>]z\<close> for z using "\<forall>E" by blast
          AOT_assume \<open>\<forall>x ([\<lambda>z [F]z & \<psi>]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close>
          AOT_hence 2: \<open>[\<lambda>z [F]z & \<psi>]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using "\<forall>E" by blast
          AOT_have \<open>[F]z \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]z\<close> for z using 1 2 "\<equiv>E" by meson
          AOT_thus \<open> \<forall>x ([F]x \<equiv> [\<lambda>z [F]z & \<psi> \<or> \<not>\<psi>]x)\<close> by (rule GEN)
        }
      qed
      }
    qed
  qed

  AOT_have \<open>\<not>\<^bold>\<A>q\<^sub>0\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF q\<^sub>0_def])
     apply (fact "log-prop-prop:2")
    by (fact AOT)
  AOT_hence q\<^sub>0_prop_1: \<open>\<^bold>\<A>\<not>q\<^sub>0\<close>
    using "logic-actual-nec:1"[axiom_inst, THEN "\<equiv>E"(2)] by blast
  {
    AOT_assume 1: \<open>\<^bold>\<A>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0]x)\<close>
    AOT_have 2: \<open>\<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0 \<or> \<not>q\<^sub>0]x)\<close>
      using Aux_B[THEN "\<rightarrow>E", OF q\<^sub>0_prop[THEN "&E"(1)]].
    AOT_have \<open>\<^bold>\<A>\<not>\<forall>x([\<lambda>z [F]z & q\<^sub>0]x \<equiv> [\<lambda>z [F]z & q\<^sub>0 \<or> \<not>q\<^sub>0]x)\<close>
      using Aux_C[THEN "\<rightarrow>E", OF q\<^sub>0_prop_1].
    AOT_hence 3: \<open>\<^bold>\<A>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0 \<or> \<not>q\<^sub>0]x)\<close>
      using Aux_D[THEN "\<rightarrow>E", OF 1, THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<^bold>\<A>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0 \<or> \<not>q\<^sub>0]x) & \<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0 \<or> \<not>q\<^sub>0]x)\<close> using 2 "&I" by blast
    AOT_hence \<open>\<exists>G (\<^bold>\<A>\<not>\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
      by (rule "\<exists>I"(1)) "cqt:2[lambda]"
  }
  moreover {
    AOT_assume 2: \<open>\<not>\<^bold>\<A>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0]x)\<close>
    AOT_hence \<open>\<^bold>\<A>\<not>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0]x)\<close>
      using "logic-actual-nec:1"[axiom_inst, THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>\<^bold>\<A>\<not>\<forall>x ([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0]x) & \<diamond>\<forall>x([F]x \<equiv> [\<lambda>z [F]z & q\<^sub>0]x)\<close>
      using Aux_A[THEN "\<rightarrow>E", OF q\<^sub>0_prop[THEN "&E"(1)]] "&I" by blast
    AOT_hence \<open>\<exists>G (\<^bold>\<A>\<not>\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
      by (rule "\<exists>I"(1)) "cqt:2[lambda]"
  }
  ultimately AOT_show \<open>\<exists>G (\<^bold>\<A>\<not>\<forall>x ([F]x \<equiv> [G]x) & \<diamond>\<forall>x([F]x \<equiv> [G]x))\<close>
    using "\<or>E"(1)[OF "exc-mid"] "\<rightarrow>I" by blast
qed

AOT_theorem oa_contingent_1: \<open>O! \<noteq> A!\<close>
proof(rule "\<equiv>\<^sub>d\<^sub>fI"[OF "=-infix"]; rule "raa-cor:2")
  fix x
  AOT_assume 1: \<open>O! = A!\<close>
  AOT_hence \<open>[\<lambda>x \<diamond>E!x] = A!\<close>
    by (rule "=\<^sub>d\<^sub>fE"(2)[OF AOT_ordinary, rotated]) "cqt:2[lambda]"
  AOT_hence \<open>[\<lambda>x \<diamond>E!x] = [\<lambda>x \<not>\<diamond>E!x]\<close>
    by (rule "=\<^sub>d\<^sub>fE"(2)[OF AOT_abstract, rotated]) "cqt:2[lambda]"
  moreover AOT_have \<open>[\<lambda>x \<diamond>E!x]x \<equiv> \<diamond>E!x\<close>
    by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  ultimately AOT_have \<open>[\<lambda>x \<not>\<diamond>E!x]x \<equiv> \<diamond>E!x\<close>
    using "=E" by fast
  moreover AOT_have \<open>[\<lambda>x \<not>\<diamond>E!x]x \<equiv> \<not>\<diamond>E!x\<close>
    by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  ultimately AOT_have \<open>\<diamond>E!x \<equiv> \<not>\<diamond>E!x\<close> using "\<equiv>E"(6) "Commutativity of \<equiv>"[THEN "\<equiv>E"(1)] by blast
  AOT_thus "(\<diamond>E!x \<equiv> \<not>\<diamond>E!x) & \<not>(\<diamond>E!x \<equiv> \<not>\<diamond>E!x)" using "oth-class-taut:3:c" "&I" by blast
qed

AOT_theorem oa_contingent_2: \<open>O!x \<equiv> \<not>A!x\<close>
proof -
  AOT_have \<open>O!x \<equiv> [\<lambda>x \<diamond>E!x]x\<close>
    apply (rule "\<equiv>I"; rule "\<rightarrow>I")
     apply (rule "=\<^sub>d\<^sub>fE"(2)[OF AOT_ordinary])
      apply "cqt:2[lambda]"
     apply argo
    apply (rule  "=\<^sub>d\<^sub>fI"(2)[OF AOT_ordinary])
     apply "cqt:2[lambda]"
    by argo
  also AOT_have \<open>\<dots> \<equiv> \<diamond>E!x\<close>
    by (rule beta_C_meta[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  also AOT_have \<open>\<dots> \<equiv> \<not>\<not>\<diamond>E!x\<close>
    using "oth-class-taut:3:b".
  also AOT_have \<open>\<dots> \<equiv> \<not>[\<lambda>x \<not>\<diamond>E!x]x\<close>
    by (rule beta_C_meta[THEN "\<rightarrow>E", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], symmetric]) "cqt:2[lambda]"
  also AOT_have \<open>\<dots> \<equiv> \<not>A!x\<close>
    apply (rule "\<equiv>I"; rule "\<rightarrow>I")
     apply (rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_abstract])
      apply "cqt:2[lambda]"
     apply argo
    apply (rule "=\<^sub>d\<^sub>fE"(2)[OF AOT_abstract])
     apply "cqt:2[lambda]"
    by argo
  finally show ?thesis.
qed

AOT_theorem oa_contingent_3: \<open>A!x \<equiv> \<not>O!x\<close>
  by (AOT_subst "\<guillemotleft>A!x\<guillemotright>" "\<guillemotleft>\<not>\<not>A!x\<guillemotright>")
     (auto simp add: "oth-class-taut:3:b" oa_contingent_2[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], symmetric])

AOT_theorem oa_contingent_4: \<open>Contingent(O!)\<close>
proof (rule thm_cont_prop_2[unvarify F, OF "oa-exist:1", THEN "\<equiv>E"(2)]; rule "&I")
  AOT_have \<open>\<diamond>\<exists>x E!x\<close> using thm_cont_e_3 .
  AOT_hence \<open>\<exists>x \<diamond>E!x\<close> using "BF\<diamond>"[THEN "\<rightarrow>E"] by blast
  then AOT_obtain a where \<open>\<diamond>E!a\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>[\<lambda>x \<diamond>E!x]a\<close>
    by (rule beta_C_meta[THEN "\<rightarrow>E", THEN "\<equiv>E"(2), rotated]) "cqt:2[lambda]"
  AOT_hence \<open>O!a\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_ordinary, rotated]) "cqt:2[lambda]"
  AOT_hence \<open>\<exists>x O!x\<close> using "\<exists>I" by blast
  AOT_thus \<open>\<diamond>\<exists>x O!x\<close> using "T\<diamond>"[THEN "\<rightarrow>E"] by blast
next
  AOT_obtain a where \<open>A!a\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] "&E" by blast
  AOT_hence \<open>\<not>O!a\<close> using oa_contingent_3[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<exists>x \<not>O!x\<close> using "\<exists>I" by fast
  AOT_thus \<open>\<diamond>\<exists>x \<not>O!x\<close> using "T\<diamond>"[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem oa_contingent_5: \<open>Contingent(A!)\<close>
proof (rule thm_cont_prop_2[unvarify F, OF "oa-exist:2", THEN "\<equiv>E"(2)]; rule "&I")
  AOT_obtain a where \<open>A!a\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] "&E" by blast
  AOT_hence \<open>\<exists>x A!x\<close> using "\<exists>I" by fast
  AOT_thus \<open>\<diamond>\<exists>x A!x\<close> using "T\<diamond>"[THEN "\<rightarrow>E"] by blast
next
  AOT_have \<open>\<diamond>\<exists>x E!x\<close> using thm_cont_e_3 .
  AOT_hence \<open>\<exists>x \<diamond>E!x\<close> using "BF\<diamond>"[THEN "\<rightarrow>E"] by blast
  then AOT_obtain a where \<open>\<diamond>E!a\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>[\<lambda>x \<diamond>E!x]a\<close>
    by (rule beta_C_meta[THEN "\<rightarrow>E", THEN "\<equiv>E"(2), rotated]) "cqt:2[lambda]"
  AOT_hence \<open>O!a\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_ordinary, rotated]) "cqt:2[lambda]"
  AOT_hence \<open>\<not>A!a\<close> using oa_contingent_2[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<exists>x \<not>A!x\<close> using "\<exists>I" by fast
  AOT_thus \<open>\<diamond>\<exists>x \<not>A!x\<close> using "T\<diamond>"[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem oa_contingent_7: \<open>O!\<^sup>-x \<equiv> \<not>A!\<^sup>-x\<close>
proof -
  AOT_have \<open>O!x \<equiv> \<not>A!x\<close>
    using oa_contingent_2 by blast
  also AOT_have \<open>\<dots> \<equiv> A!\<^sup>-x\<close>
    using thm_relation_negation_1[symmetric, unvarify F, OF "oa-exist:2"].
  finally AOT_have 1: \<open>O!x \<equiv> A!\<^sup>-x\<close>.

  AOT_have \<open>A!x \<equiv> \<not>O!x\<close>
    using oa_contingent_3 by blast
  also AOT_have \<open>\<dots> \<equiv> O!\<^sup>-x\<close>
    using thm_relation_negation_1[symmetric, unvarify F, OF "oa-exist:1"].
  finally AOT_have 2: \<open>A!x \<equiv> O!\<^sup>-x\<close>.

  AOT_show \<open>O!\<^sup>-x \<equiv> \<not>A!\<^sup>-x\<close>
    using 1[THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)]] oa_contingent_3[of _ x] 2[symmetric]
          "\<equiv>E"(5) by blast
qed

AOT_theorem oa_contingent_6: \<open>O!\<^sup>- \<noteq> A!\<^sup>-\<close>
proof (rule "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "raa-cor:2")
  AOT_assume 1: \<open>O!\<^sup>- = A!\<^sup>-\<close>
  fix x
  AOT_have \<open>A!\<^sup>-x \<equiv> O!\<^sup>-x\<close>
    apply (rule "=E"[rotated, OF 1]) by (fact "oth-class-taut:3:a")
  AOT_hence \<open>A!\<^sup>-x \<equiv> \<not>A!\<^sup>-x\<close>
    using oa_contingent_7 "\<equiv>E" by fast
  AOT_thus \<open>(A!\<^sup>-x \<equiv> \<not>A!\<^sup>-x) & \<not>(A!\<^sup>-x \<equiv> \<not>A!\<^sup>-x)\<close> using "oth-class-taut:3:c" "&I" by blast
qed

AOT_theorem oa_contingent_8: \<open>Contingent(O!\<^sup>-)\<close>
  using thm_cont_prop_3[unvarify F, OF "oa-exist:1", THEN "\<equiv>E"(1), OF oa_contingent_4].

AOT_theorem oa_contingent_9: \<open>Contingent(A!\<^sup>-)\<close>
  using thm_cont_prop_3[unvarify F, OF "oa-exist:2", THEN "\<equiv>E"(1), OF oa_contingent_5].

AOT_define WeaklyContingent :: \<open>\<Pi> \<Rightarrow> \<phi>\<close> ("WeaklyContingent'(_')")
  df_cont_nec: "WeaklyContingent([F]) \<equiv>\<^sub>d\<^sub>f Contingent([F]) & \<forall>x (\<diamond>[F]x \<rightarrow> \<box>[F]x)"

AOT_theorem cont_nec_fact1_1: \<open>WeaklyContingent([F]) \<equiv> WeaklyContingent([F]\<^sup>-)\<close>
proof -
  AOT_have \<open>WeaklyContingent([F]) \<equiv> Contingent([F]) & \<forall>x (\<diamond>[F]x \<rightarrow> \<box>[F]x)\<close>
    using df_cont_nec[THEN "\<equiv>Df"] by blast
  also AOT_have \<open>... \<equiv> Contingent([F]\<^sup>-) & \<forall>x (\<diamond>[F]x \<rightarrow> \<box>[F]x)\<close>
    apply (rule "oth-class-taut:8:f"[THEN "\<equiv>E"(2)]; rule "\<rightarrow>I")
    using thm_cont_prop_3.
  also AOT_have \<open>\<dots> \<equiv> Contingent([F]\<^sup>-) & \<forall>x (\<diamond>[F]\<^sup>-x \<rightarrow> \<box>[F]\<^sup>-x)\<close>
  proof (rule "oth-class-taut:8:e"[THEN "\<equiv>E"(2)]; rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I"; rule GEN; rule "\<rightarrow>I")
    fix x
    AOT_assume 0: \<open>\<forall>x (\<diamond>[F]x \<rightarrow> \<box>[F]x)\<close>
    AOT_assume 1: \<open>\<diamond>[F]\<^sup>-x\<close>
    AOT_have \<open>\<diamond>\<not>[F]x\<close>
      by (AOT_subst_rev "\<guillemotleft>[F]\<^sup>-x\<guillemotright>" "\<guillemotleft>\<not>[F]x\<guillemotright>")
         (auto simp add: thm_relation_negation_1 1)
    AOT_hence 2: \<open>\<not>\<box>[F]x\<close>
      using "KBasic:11"[THEN "\<equiv>E"(2)] by blast
    AOT_show \<open>\<box>[F]\<^sup>-x\<close>
    proof (rule "raa-cor:1")
      AOT_assume 3: \<open>\<not>\<box>[F]\<^sup>-x\<close>
      AOT_have \<open>\<not>\<box>\<not>[F]x\<close>
        by (AOT_subst_rev "\<guillemotleft>[F]\<^sup>-x\<guillemotright>" "\<guillemotleft>\<not>[F]x\<guillemotright>")
           (auto simp add: thm_relation_negation_1 3)
      AOT_hence \<open>\<diamond>[F]x\<close>
        using AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fI"] by simp
      AOT_hence \<open>\<box>[F]x\<close> using 0 "\<forall>E" "\<rightarrow>E" by fast
      AOT_thus \<open>\<box>[F]x & \<not>\<box>[F]x\<close> using "&I" 2 by blast
    qed
  next
    fix x
    AOT_assume 0: \<open>\<forall>x (\<diamond>[F]\<^sup>-x \<rightarrow> \<box>[F]\<^sup>-x)\<close>
    AOT_assume 1: \<open>\<diamond>[F]x\<close>
    AOT_have \<open>\<diamond>\<not>[F]\<^sup>-x\<close>
      by (AOT_subst "\<guillemotleft>\<not>[F]\<^sup>-x\<guillemotright>" "\<guillemotleft>[F]x\<guillemotright>")
         (auto simp: thm_relation_negation_2 1)
    AOT_hence 2: \<open>\<not>\<box>[F]\<^sup>-x\<close>
      using "KBasic:11"[THEN "\<equiv>E"(2)] by blast
    AOT_show \<open>\<box>[F]x\<close>
    proof (rule "raa-cor:1")
      AOT_assume 3: \<open>\<not>\<box>[F]x\<close>
      AOT_have \<open>\<not>\<box>\<not>[F]\<^sup>-x\<close>
        by (AOT_subst "\<guillemotleft>\<not>[F]\<^sup>-x\<guillemotright>" "\<guillemotleft>[F]x\<guillemotright>")
           (auto simp add: thm_relation_negation_2 3)
      AOT_hence \<open>\<diamond>[F]\<^sup>-x\<close>
        using AOT_dia[THEN "\<equiv>\<^sub>d\<^sub>fI"] by simp
      AOT_hence \<open>\<box>[F]\<^sup>-x\<close> using 0 "\<forall>E" "\<rightarrow>E" by fast
      AOT_thus \<open>\<box>[F]\<^sup>-x & \<not>\<box>[F]\<^sup>-x\<close> using "&I" 2 by blast
    qed
  qed
  also AOT_have \<open>\<dots> \<equiv> WeaklyContingent([F]\<^sup>-)\<close>
    using df_cont_nec[THEN "\<equiv>Df", symmetric] by blast
  finally show ?thesis.
qed

AOT_theorem cont_nec_fact1_2: \<open>(WeaklyContingent([F]) & \<not>WeaklyContingent([G])) \<rightarrow> F \<noteq> G\<close>
proof (rule "\<rightarrow>I"; rule "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "raa-cor:2")
  AOT_assume 1: \<open>WeaklyContingent([F]) & \<not>WeaklyContingent([G])\<close>
  AOT_hence \<open>WeaklyContingent([F])\<close> using "&E" by blast
  moreover AOT_assume \<open>F = G\<close>
  ultimately AOT_have \<open>WeaklyContingent([G])\<close>
    using "=E" by blast
  AOT_thus \<open>WeaklyContingent([G]) & \<not>WeaklyContingent([G])\<close>
    using 1 "&I" "&E" by blast
qed

AOT_theorem cont_nec_fact2_1: \<open>WeaklyContingent(O!)\<close>
proof (rule df_cont_nec[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "&I")
  AOT_show \<open>Contingent(O!)\<close>
    using oa_contingent_4.
next
  AOT_show \<open>\<forall>x (\<diamond>[O!]x \<rightarrow> \<box>[O!]x)\<close>
    apply (rule GEN; rule "\<rightarrow>I")
    using oa_facts_5[THEN "\<equiv>E"(1)] by blast
qed


AOT_theorem cont_nec_fact2_2: \<open>WeaklyContingent(A!)\<close>
proof (rule df_cont_nec[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "&I")
  AOT_show \<open>Contingent(A!)\<close>
    using oa_contingent_5.
next
  AOT_show \<open>\<forall>x (\<diamond>[A!]x \<rightarrow> \<box>[A!]x)\<close>
    apply (rule GEN; rule "\<rightarrow>I")
    using oa_facts_6[THEN "\<equiv>E"(1)] by blast
qed

AOT_theorem cont_nec_fact2_3: \<open>\<not>WeaklyContingent(E!)\<close>
proof (rule df_cont_nec[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)];
       rule DeMorgan(1)[THEN "\<equiv>E"(2)]; rule "\<or>I"(2); rule "raa-cor:2")
  AOT_have \<open>\<diamond>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close> using "qml:4"[axiom_inst].
  AOT_hence \<open>\<exists>x \<diamond>(E!x & \<not>\<^bold>\<A>E!x)\<close> using "BF\<diamond>"[THEN "\<rightarrow>E"] by blast
  then AOT_obtain a where \<open>\<diamond>(E!a & \<not>\<^bold>\<A>E!a)\<close> using "\<exists>E"[rotated] by blast
  AOT_hence 1: \<open>\<diamond>E!a & \<diamond>\<not>\<^bold>\<A>E!a\<close> using "KBasic2:3"[THEN "\<rightarrow>E"] by simp
  moreover AOT_assume \<open>\<forall>x (\<diamond>[E!]x \<rightarrow> \<box>[E!]x)\<close>
  ultimately AOT_have \<open>\<box>E!a\<close> using "&E" "\<forall>E" "\<rightarrow>E" by fast
  AOT_hence \<open>\<^bold>\<A>E!a\<close> using "nec-imp-act"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<box>\<^bold>\<A>E!a\<close> using "qml-act:1"[axiom_inst, THEN "\<rightarrow>E"] by blast
  moreover AOT_have \<open>\<not>\<box>\<^bold>\<A>E!a\<close> using "KBasic:11"[THEN "\<equiv>E"(2)] 1[THEN "&E"(2)] by meson
  ultimately AOT_have \<open>\<box>\<^bold>\<A>E!a & \<not>\<box>\<^bold>\<A>E!a\<close> using "&I" by blast
  AOT_thus \<open>p & \<not>p\<close> for p using "raa-cor:1" by blast
qed

AOT_theorem cont_nec_fact2_4: \<open>\<not>WeaklyContingent(L)\<close>
  apply (rule df_cont_nec[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)];
       rule DeMorgan(1)[THEN "\<equiv>E"(2)]; rule "\<or>I"(1))
  apply (rule contingent_properties_4[THEN "\<equiv>Df", THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(2)])
  apply (rule DeMorgan(1)[THEN "\<equiv>E"(2)]; rule "\<or>I"(2); rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
  using thm_noncont_e_e_3[THEN contingent_properties_3[THEN "\<equiv>\<^sub>d\<^sub>fE"]].

(* TODO: cleanup *)
AOT_theorem cont_nec_fact2_5: \<open>O! \<noteq> E! & O! \<noteq> E!\<^sup>- & O! \<noteq> L & O! \<noteq> L\<^sup>-\<close>
proof -
  AOT_have 1: \<open>L\<down>\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
  {
    fix \<phi> and \<Pi> and \<Pi>'
    AOT_have A: \<open>\<not>(\<phi>{\<Pi>'} \<equiv> \<phi>{\<Pi>})\<close> if  \<open>\<phi>{\<Pi>}\<close> and \<open>\<not>\<phi>{\<Pi>'}\<close>
    proof (rule "raa-cor:2")
      AOT_assume \<open>\<phi>{\<Pi>'} \<equiv> \<phi>{\<Pi>}\<close>
      AOT_hence \<open>\<phi>{\<Pi>'}\<close> using that(1) "\<equiv>E" by blast
      AOT_thus \<open>\<phi>{\<Pi>'} & \<not>\<phi>{\<Pi>'}\<close> using that(2) "&I" by blast
    qed
    AOT_have \<open>\<Pi>' \<noteq> \<Pi>\<close> if \<open>\<Pi>\<down>\<close> and \<open>\<Pi>'\<down>\<close> and \<open>\<phi>{\<Pi>}\<close> and \<open>\<not>\<phi>{\<Pi>'}\<close>
      using pos_not_equiv_ne_4[unvarify F G, THEN "\<rightarrow>E", OF that(1,2), OF A[OF that(3, 4)]].
  } note 0 = this
  show ?thesis
    apply(safe intro!: "&I"; rule 0)
    using "cqt:2[concrete]"[axiom_inst] apply blast
    using "oa-exist:1" apply blast
    using cont_nec_fact2_3 apply fast
    apply (rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
    using cont_nec_fact2_1 apply fast
    using rel_neg_T_3 apply fast
    using "oa-exist:1" apply blast
    using cont_nec_fact1_1[unvarify F, THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1), rotated, OF cont_nec_fact2_3, OF "cqt:2[concrete]"[axiom_inst]] apply fast
    apply (rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
    using cont_nec_fact2_1 apply blast
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]; "cqt:2[lambda]")
    using "oa-exist:1" apply fast
    using cont_nec_fact2_4 apply fast
    apply (rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
    using cont_nec_fact2_1 apply fast
    using rel_neg_T_3 apply fast
    using "oa-exist:1" apply fast
    apply (rule cont_nec_fact1_1[unvarify F, THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1), rotated, OF cont_nec_fact2_4])
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]; "cqt:2[lambda]")
    apply (rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
    using cont_nec_fact2_1 by blast
qed

(* TODO: cleanup together with above *)
AOT_theorem cont_nec_fact2_6: \<open>A! \<noteq> E! & A! \<noteq> E!\<^sup>- & A! \<noteq> L & A! \<noteq> L\<^sup>-\<close>
proof -
  AOT_have 1: \<open>L\<down>\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
  {
    fix \<phi> and \<Pi> and \<Pi>'
    AOT_have A: \<open>\<not>(\<phi>{\<Pi>'} \<equiv> \<phi>{\<Pi>})\<close> if  \<open>\<phi>{\<Pi>}\<close> and \<open>\<not>\<phi>{\<Pi>'}\<close>
    proof (rule "raa-cor:2")
      AOT_assume \<open>\<phi>{\<Pi>'} \<equiv> \<phi>{\<Pi>}\<close>
      AOT_hence \<open>\<phi>{\<Pi>'}\<close> using that(1) "\<equiv>E" by blast
      AOT_thus \<open>\<phi>{\<Pi>'} & \<not>\<phi>{\<Pi>'}\<close> using that(2) "&I" by blast
    qed
    AOT_have \<open>\<Pi>' \<noteq> \<Pi>\<close> if \<open>\<Pi>\<down>\<close> and \<open>\<Pi>'\<down>\<close> and \<open>\<phi>{\<Pi>}\<close> and \<open>\<not>\<phi>{\<Pi>'}\<close>
      using pos_not_equiv_ne_4[unvarify F G, THEN "\<rightarrow>E", OF that(1,2), OF A[OF that(3, 4)]].
  } note 0 = this
  show ?thesis
    apply(safe intro!: "&I"; rule 0)
    using "cqt:2[concrete]"[axiom_inst] apply blast
    using "oa-exist:2" apply blast
    using cont_nec_fact2_3 apply fast
    apply (rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
    using cont_nec_fact2_2 apply fast
    using rel_neg_T_3 apply fast
    using "oa-exist:2" apply blast
    using cont_nec_fact1_1[unvarify F, THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1), rotated, OF cont_nec_fact2_3, OF "cqt:2[concrete]"[axiom_inst]] apply fast
    apply (rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
    using cont_nec_fact2_2 apply blast
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]; "cqt:2[lambda]")
    using "oa-exist:2" apply fast
    using cont_nec_fact2_4 apply fast
    apply (rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
    using cont_nec_fact2_2 apply fast
    using rel_neg_T_3 apply fast
    using "oa-exist:2" apply fast
    apply (rule cont_nec_fact1_1[unvarify F, THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1), rotated, OF cont_nec_fact2_4])
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]; "cqt:2[lambda]")
    apply (rule "useful-tautologies:2"[THEN "\<rightarrow>E"])
    using cont_nec_fact2_2 by blast
qed

AOT_define necessary_or_contingently_false :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("\<^bold>\<Delta>_" [49] 54)
  \<open>\<^bold>\<Delta>p \<equiv>\<^sub>d\<^sub>f \<box>p \<or> (\<not>\<^bold>\<A>p & \<diamond>p)\<close>

AOT_theorem sixteen:
 shows \<open>\<exists>F\<^sub>1\<exists>F\<^sub>2\<exists>F\<^sub>3\<exists>F\<^sub>4\<exists>F\<^sub>5\<exists>F\<^sub>6\<exists>F\<^sub>7\<exists>F\<^sub>8\<exists>F\<^sub>9\<exists>F\<^sub>1\<^sub>0\<exists>F\<^sub>1\<^sub>1\<exists>F\<^sub>1\<^sub>2\<exists>F\<^sub>1\<^sub>3\<exists>F\<^sub>1\<^sub>4\<exists>F\<^sub>1\<^sub>5\<exists>F\<^sub>1\<^sub>6 (
\<guillemotleft>F\<^sub>1::<\<kappa>>\<guillemotright> \<noteq> F\<^sub>2 & F\<^sub>1 \<noteq> F\<^sub>3 & F\<^sub>1 \<noteq> F\<^sub>4 & F\<^sub>1 \<noteq> F\<^sub>5 & F\<^sub>1 \<noteq> F\<^sub>6 & F\<^sub>1 \<noteq> F\<^sub>7 & F\<^sub>1 \<noteq> F\<^sub>8 & F\<^sub>1 \<noteq> F\<^sub>9 & F\<^sub>1 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>1 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>1 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>1 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>1 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>1 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>1 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>2 \<noteq> F\<^sub>3 & F\<^sub>2 \<noteq> F\<^sub>4 & F\<^sub>2 \<noteq> F\<^sub>5 & F\<^sub>2 \<noteq> F\<^sub>6 & F\<^sub>2 \<noteq> F\<^sub>7 & F\<^sub>2 \<noteq> F\<^sub>8 & F\<^sub>2 \<noteq> F\<^sub>9 & F\<^sub>2 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>2 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>2 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>2 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>2 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>2 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>2 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>3 \<noteq> F\<^sub>4 & F\<^sub>3 \<noteq> F\<^sub>5 & F\<^sub>3 \<noteq> F\<^sub>6 & F\<^sub>3 \<noteq> F\<^sub>7 & F\<^sub>3 \<noteq> F\<^sub>8 & F\<^sub>3 \<noteq> F\<^sub>9 & F\<^sub>3 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>3 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>3 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>3 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>3 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>3 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>3 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>4 \<noteq> F\<^sub>5 & F\<^sub>4 \<noteq> F\<^sub>6 & F\<^sub>4 \<noteq> F\<^sub>7 & F\<^sub>4 \<noteq> F\<^sub>8 & F\<^sub>4 \<noteq> F\<^sub>9 & F\<^sub>4 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>4 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>4 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>4 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>4 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>4 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>4 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>5 \<noteq> F\<^sub>6 & F\<^sub>5 \<noteq> F\<^sub>7 & F\<^sub>5 \<noteq> F\<^sub>8 & F\<^sub>5 \<noteq> F\<^sub>9 & F\<^sub>5 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>5 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>5 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>5 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>5 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>5 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>5 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>6 \<noteq> F\<^sub>7 & F\<^sub>6 \<noteq> F\<^sub>8 & F\<^sub>6 \<noteq> F\<^sub>9 & F\<^sub>6 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>6 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>6 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>6 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>6 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>6 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>6 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>7 \<noteq> F\<^sub>8 & F\<^sub>7 \<noteq> F\<^sub>9 & F\<^sub>7 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>7 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>7 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>7 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>7 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>7 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>7 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>8 \<noteq> F\<^sub>9 & F\<^sub>8 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>8 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>8 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>8 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>8 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>8 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>8 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>9 \<noteq> F\<^sub>1\<^sub>0 & F\<^sub>9 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>9 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>9 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>9 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>9 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>9 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>1\<^sub>0 \<noteq> F\<^sub>1\<^sub>1 & F\<^sub>1\<^sub>0 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>1\<^sub>0 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>1\<^sub>0 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>1\<^sub>0 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>1\<^sub>0 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>1\<^sub>1 \<noteq> F\<^sub>1\<^sub>2 & F\<^sub>1\<^sub>1 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>1\<^sub>1 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>1\<^sub>1 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>1\<^sub>1 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>1\<^sub>2 \<noteq> F\<^sub>1\<^sub>3 & F\<^sub>1\<^sub>2 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>1\<^sub>2 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>1\<^sub>2 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>1\<^sub>3 \<noteq> F\<^sub>1\<^sub>4 & F\<^sub>1\<^sub>3 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>1\<^sub>3 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>1\<^sub>4 \<noteq> F\<^sub>1\<^sub>5 & F\<^sub>1\<^sub>4 \<noteq> F\<^sub>1\<^sub>6 &
F\<^sub>1\<^sub>5 \<noteq> F\<^sub>1\<^sub>6)\<close> 
proof -

  AOT_have Delta_pos: \<open>\<^bold>\<Delta>\<phi> \<rightarrow> \<diamond>\<phi>\<close> for \<phi>
  proof(rule "\<rightarrow>I")
    AOT_assume \<open>\<^bold>\<Delta>\<phi>\<close>
    AOT_hence \<open>\<box>\<phi> \<or> (\<not>\<^bold>\<A>\<phi> & \<diamond>\<phi>)\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF necessary_or_contingently_false] by blast
    moreover {
      AOT_assume \<open>\<box>\<phi>\<close>
      AOT_hence \<open>\<diamond>\<phi>\<close>
        by (metis "B\<diamond>" "T\<diamond>" "vdash-properties:10")
    }
    moreover {
      AOT_assume \<open>\<not>\<^bold>\<A>\<phi> & \<diamond>\<phi>\<close>
      AOT_hence \<open>\<diamond>\<phi>\<close>
        using "&E" by blast
    }
    ultimately AOT_show \<open>\<diamond>\<phi>\<close>
      by (metis "\<or>E"(2) "raa-cor:1") 
  qed

  AOT_have act_and_not_nec_not_delta: \<open>\<not>\<^bold>\<Delta>\<phi>\<close> if \<open>\<^bold>\<A>\<phi>\<close> and \<open>\<not>\<box>\<phi>\<close> for \<phi>
    using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "\<or>E"(2) necessary_or_contingently_false "raa-cor:3" that(1) that(2) by blast
  AOT_have act_and_pos_not_not_delta: \<open>\<not>\<^bold>\<Delta>\<phi>\<close> if \<open>\<^bold>\<A>\<phi>\<close> and \<open>\<diamond>\<not>\<phi>\<close> for \<phi>
    using "KBasic:11" act_and_not_nec_not_delta "\<equiv>E"(2) that(1) that(2) by blast
  AOT_have impossible_delta: \<open>\<not>\<^bold>\<Delta>\<phi>\<close> if \<open>\<not>\<diamond>\<phi>\<close> for \<phi>
    using Delta_pos "modus-tollens:1" that by blast
  AOT_have not_act_and_pos_delta: \<open>\<^bold>\<Delta>\<phi>\<close> if \<open>\<not>\<^bold>\<A>\<phi>\<close> and \<open>\<diamond>\<phi>\<close> for \<phi>
    by (meson "\<equiv>\<^sub>d\<^sub>fI" "&I" "\<or>I"(2) necessary_or_contingently_false that(1) that(2))
  AOT_have nec_delta: \<open>\<^bold>\<Delta>\<phi>\<close> if \<open>\<box>\<phi>\<close> for \<phi>
    using "\<equiv>\<^sub>d\<^sub>fI" "\<or>I"(1) necessary_or_contingently_false that by blast

  AOT_obtain a where a_prop: \<open>A!a\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] "&E" by blast
  AOT_obtain b where b_prop: \<open>\<diamond>[E!]b & \<not>\<^bold>\<A>[E!]b\<close>
    using pos_not_pna_3 using "\<exists>E"[rotated] by blast

  AOT_have b_ord: \<open>[O!]b\<close>
  proof(rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_ordinary])
    AOT_show \<open>[\<lambda>x \<diamond>[E!]x]\<down>\<close> by "cqt:2[lambda]"
  next
    AOT_show \<open>[\<lambda>x \<diamond>[E!]x]b\<close>
    proof (rule betaC_2_a; ("cqt:2[lambda]")?)
      AOT_show \<open>b\<down>\<close> by (rule "cqt:2[const_var]"[axiom_inst])
      AOT_show \<open>\<diamond>[E!]b\<close> by (fact b_prop[THEN "&E"(1)])
    qed
  qed

  AOT_have nec_not_L_neg: \<open>\<box>\<not>[L\<^sup>-]x\<close> for x
    using thm_noncont_e_e_2 contingent_properties_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"
          CBF[THEN "\<rightarrow>E"] "\<forall>E" by blast
  AOT_have nec_L: \<open>\<box>[L]x\<close> for x
    using thm_noncont_e_e_1 contingent_properties_1[THEN "\<equiv>\<^sub>d\<^sub>fE"]
      CBF[THEN "\<rightarrow>E"] "\<forall>E" by blast

  AOT_have act_ord_b: \<open>\<^bold>\<A>[O!]b\<close>
    using b_ord "\<equiv>E"(1) oa_facts_7 by blast
  AOT_have delta_ord_b: \<open>\<^bold>\<Delta>[O!]b\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fI" b_ord "\<or>I"(1) necessary_or_contingently_false oa_facts_1 "vdash-properties:10")
  AOT_have not_act_ord_a: \<open>\<not>\<^bold>\<A>[O!]a\<close>
    by (meson a_prop "\<equiv>E"(1) "\<equiv>E"(3) oa_contingent_3 oa_facts_7)
  AOT_have not_delta_ord_a: \<open>\<not>\<^bold>\<Delta>[O!]a\<close>
    by (metis Delta_pos "\<equiv>E"(4) not_act_ord_a oa_facts_3 oa_facts_7 "reductio-aa:1" "vdash-properties:10")

  AOT_have not_act_abs_b: \<open>\<not>\<^bold>\<A>[A!]b\<close>
    by (meson b_ord "\<equiv>E"(1) "\<equiv>E"(3) oa_contingent_2 oa_facts_8)
  AOT_have not_delta_abs_b: \<open>\<not>\<^bold>\<Delta>[A!]b\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<^bold>\<Delta>[A!]b\<close>
    AOT_hence \<open>\<diamond>[A!]b\<close>
      by (metis Delta_pos "vdash-properties:10")
    AOT_thus \<open>[A!]b & \<not>[A!]b\<close>
      by (metis b_ord "&I" "\<equiv>E"(1) oa_contingent_2 oa_facts_4 "vdash-properties:10")
  qed
  AOT_have act_abs_a: \<open>\<^bold>\<A>[A!]a\<close>
    using a_prop "\<equiv>E"(1) oa_facts_8 by blast
  AOT_have delta_abs_a: \<open>\<^bold>\<Delta>[A!]a\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fI" a_prop oa_facts_2 "vdash-properties:10" "\<or>I"(1) necessary_or_contingently_false)

  AOT_have not_act_concrete_b: \<open>\<not>\<^bold>\<A>[E!]b\<close>
    using b_prop "&E"(2) by blast
  AOT_have delta_concrete_b: \<open>\<^bold>\<Delta>[E!]b\<close>
  proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF necessary_or_contingently_false]; rule "\<or>I"(2); rule "&I")
    AOT_show \<open>\<not>\<^bold>\<A>[E!]b\<close> using b_prop "&E"(2) by blast
  next
    AOT_show \<open>\<diamond>[E!]b\<close> using b_prop "&E"(1) by blast
  qed
  AOT_have not_act_concrete_a: \<open>\<not>\<^bold>\<A>[E!]a\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>\<^bold>\<A>[E!]a\<close>
    AOT_hence 1: \<open>\<diamond>[E!]a\<close> by (metis "Act-Sub:3" "vdash-properties:10")
    AOT_have \<open>[A!]a\<close> by (simp add: a_prop)
    AOT_hence \<open>[\<lambda>x \<not>\<diamond>[E!]x]a\<close>
      by (rule "=\<^sub>d\<^sub>fE"(2)[OF AOT_abstract, rotated]) "cqt:2[lambda]"
    AOT_hence \<open>\<not>\<diamond>[E!]a\<close> using betaC_1_a by blast
    AOT_thus \<open>\<diamond>[E!]a & \<not>\<diamond>[E!]a\<close> using 1 "&I" by blast
  qed
  AOT_have not_delta_concrete_a: \<open>\<not>\<^bold>\<Delta>[E!]a\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>\<^bold>\<Delta>[E!]a\<close>
    AOT_hence 1: \<open>\<diamond>[E!]a\<close> by (metis Delta_pos "vdash-properties:10")
    AOT_have \<open>[A!]a\<close> by (simp add: a_prop)
    AOT_hence \<open>[\<lambda>x \<not>\<diamond>[E!]x]a\<close>
      by (rule "=\<^sub>d\<^sub>fE"(2)[OF AOT_abstract, rotated]) "cqt:2[lambda]"
    AOT_hence \<open>\<not>\<diamond>[E!]a\<close> using betaC_1_a by blast
    AOT_thus \<open>\<diamond>[E!]a & \<not>\<diamond>[E!]a\<close> using 1 "&I" by blast
  qed

  AOT_have not_act_q_zero: \<open>\<not>\<^bold>\<A>q\<^sub>0\<close>
    by (meson "log-prop-prop:2" pos_not_pna_1 q\<^sub>0_def "reductio-aa:1" "rule-id-def:2:a[zero]")
  AOT_have delta_q_zero: \<open>\<^bold>\<Delta>q\<^sub>0\<close>
  proof(rule "\<equiv>\<^sub>d\<^sub>fI"[OF necessary_or_contingently_false]; rule "\<or>I"(2); rule "&I")
    AOT_show \<open>\<not>\<^bold>\<A>q\<^sub>0\<close> using not_act_q_zero.
    AOT_show \<open>\<diamond>q\<^sub>0\<close> by (meson "&E"(1) q\<^sub>0_prop)
  qed
  AOT_have act_not_q_zero: \<open>\<^bold>\<A>\<not>q\<^sub>0\<close> using "Act-Basic:1" "\<or>E"(2) not_act_q_zero by blast
  AOT_have not_delta_not_q_zero: \<open>\<not>\<^bold>\<Delta>\<not>q\<^sub>0\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" AOT_dia "Act-Basic:1" act_and_not_nec_not_delta "&E"(1) "\<or>E"(2) not_act_q_zero q\<^sub>0_prop by blast

  AOT_have \<open>[L\<^sup>-]\<down>\<close> by (simp add: rel_neg_T_3)
  moreover AOT_have \<open>\<not>\<^bold>\<A>[L\<^sup>-]b & \<not>\<^bold>\<Delta>[L\<^sup>-]b & \<not>\<^bold>\<A>[L\<^sup>-]a & \<not>\<^bold>\<Delta>[L\<^sup>-]a\<close>
  proof (safe intro!: "&I")
    AOT_show \<open>\<not>\<^bold>\<A>[L\<^sup>-]b\<close> by (meson "\<equiv>E"(1) "logic-actual-nec:1"[axiom_inst] "nec-imp-act" nec_not_L_neg "\<rightarrow>E")
    AOT_show \<open>\<not>\<^bold>\<Delta>[L\<^sup>-]b\<close> by (meson Delta_pos "KBasic2:1" "\<equiv>E"(1) "modus-tollens:1" nec_not_L_neg)
    AOT_show \<open>\<not>\<^bold>\<A>[L\<^sup>-]a\<close> by (meson "\<equiv>E"(1) "logic-actual-nec:1"[axiom_inst] "nec-imp-act" nec_not_L_neg "\<rightarrow>E")
    AOT_show \<open>\<not>\<^bold>\<Delta>[L\<^sup>-]a\<close> using Delta_pos "KBasic2:1" "\<equiv>E"(1) "modus-tollens:1" nec_not_L_neg by blast
  qed
  ultimately AOT_obtain F\<^sub>0 where \<open>\<not>\<^bold>\<A>[F\<^sub>0]b & \<not>\<^bold>\<Delta>[F\<^sub>0]b & \<not>\<^bold>\<A>[F\<^sub>0]a & \<not>\<^bold>\<Delta>[F\<^sub>0]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<not>\<^bold>\<A>[F\<^sub>0]b\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>0]b\<close> and \<open>\<not>\<^bold>\<A>[F\<^sub>0]a\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>0]a\<close>
    using "&E" by blast+
  note props = this

  let ?\<Pi> = "\<guillemotleft>[\<lambda>y [A!]y & q\<^sub>0]\<guillemotright>"
  AOT_modally_strict {
    AOT_have \<open>[\<guillemotleft>?\<Pi>\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have\<open>\<not>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<not>\<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<not>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]a & \<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]a\<close>
  proof(safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>\<not>\<^bold>\<A>([A!]b & q\<^sub>0)\<close>
      using "Act-Basic:2" "&E"(1) "\<equiv>E"(1) not_act_abs_b "raa-cor:3" by blast
  next AOT_show \<open>\<not>\<^bold>\<Delta>([A!]b & q\<^sub>0)\<close>
      by (metis Delta_pos "KBasic2:3" "&E"(1) "\<equiv>E"(4) not_act_abs_b oa_facts_4 oa_facts_8 "raa-cor:3" "vdash-properties:10")
  next AOT_show \<open>\<not>\<^bold>\<A>([A!]a & q\<^sub>0)\<close>
      using "Act-Basic:2" "&E"(2) "\<equiv>E"(1) not_act_q_zero "raa-cor:3" by blast
  next AOT_show \<open>\<^bold>\<Delta>([A!]a & q\<^sub>0)\<close>
    proof (rule not_act_and_pos_delta)
      AOT_show \<open>\<not>\<^bold>\<A>([A!]a & q\<^sub>0)\<close>
        using "Act-Basic:2" "&E"(2) "\<equiv>E"(4) not_act_q_zero "raa-cor:3" by blast
    next AOT_show \<open>\<diamond>([A!]a & q\<^sub>0)\<close>
        by (metis "&I" "\<rightarrow>E" Delta_pos "KBasic:16" "&E"(1) delta_abs_a "\<equiv>E"(1) oa_facts_6 q\<^sub>0_prop)
    qed
  qed
  ultimately AOT_obtain F\<^sub>1 where \<open>\<not>\<^bold>\<A>[F\<^sub>1]b & \<not>\<^bold>\<Delta>[F\<^sub>1]b & \<not>\<^bold>\<A>[F\<^sub>1]a & \<^bold>\<Delta>[F\<^sub>1]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<not>\<^bold>\<A>[F\<^sub>1]b\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>1]b\<close> and \<open>\<not>\<^bold>\<A>[F\<^sub>1]a\<close> and \<open>\<^bold>\<Delta>[F\<^sub>1]a\<close>
    using "&E" by blast+
  note props = props this

  let ?\<Pi> = "\<guillemotleft>[\<lambda>y [A!]y & \<not>q\<^sub>0]\<guillemotright>"
  AOT_modally_strict {
    AOT_have \<open>[\<guillemotleft>?\<Pi>\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<not>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<not>\<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]a & \<not>\<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]a\<close>
  proof(safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>\<not>\<^bold>\<A>([A!]b & \<not>q\<^sub>0)\<close>
      using "Act-Basic:2" "&E"(1) "\<equiv>E"(1) not_act_abs_b "raa-cor:3" by blast
  next AOT_show \<open>\<not>\<^bold>\<Delta>([A!]b & \<not>q\<^sub>0)\<close>
      by (meson "RM\<diamond>" Delta_pos "Conjunction Simplification"(1) "\<equiv>E"(4) "modus-tollens:1" not_act_abs_b oa_facts_4 oa_facts_8)
  next AOT_show \<open>\<^bold>\<A>([A!]a & \<not>q\<^sub>0)\<close>
      by (metis "Act-Basic:1" "Act-Basic:2" act_abs_a "&I" "\<or>E"(2) "\<equiv>E"(3) not_act_q_zero "raa-cor:3")
  next AOT_show \<open>\<not>\<^bold>\<Delta>([A!]a & \<not>q\<^sub>0)\<close>
    proof (rule act_and_not_nec_not_delta)
      AOT_show \<open>\<^bold>\<A>([A!]a & \<not>q\<^sub>0)\<close>
        by (metis "Act-Basic:1" "Act-Basic:2" act_abs_a "&I" "\<or>E"(2) "\<equiv>E"(3) not_act_q_zero "raa-cor:3")
    next
      AOT_show \<open>\<not>\<box>([A!]a & \<not>q\<^sub>0)\<close>
        by (metis "KBasic2:1" "KBasic:3" "&E"(1) "&E"(2) "\<equiv>E"(4) q\<^sub>0_prop "raa-cor:3")
    qed
  qed
  ultimately AOT_obtain F\<^sub>2 where \<open>\<not>\<^bold>\<A>[F\<^sub>2]b & \<not>\<^bold>\<Delta>[F\<^sub>2]b & \<^bold>\<A>[F\<^sub>2]a & \<not>\<^bold>\<Delta>[F\<^sub>2]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<not>\<^bold>\<A>[F\<^sub>2]b\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>2]b\<close> and \<open>\<^bold>\<A>[F\<^sub>2]a\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>2]a\<close>
    using "&E" by blast+
  note props = props this

  AOT_have abstract_prop: \<open>\<not>\<^bold>\<A>[A!]b & \<not>\<^bold>\<Delta>[A!]b & \<^bold>\<A>[A!]a & \<^bold>\<Delta>[A!]a\<close>
    using act_abs_a "&I" delta_abs_a not_act_abs_b not_delta_abs_b by presburger
  then AOT_obtain F\<^sub>3 where \<open>\<not>\<^bold>\<A>[F\<^sub>3]b & \<not>\<^bold>\<Delta>[F\<^sub>3]b & \<^bold>\<A>[F\<^sub>3]a & \<^bold>\<Delta>[F\<^sub>3]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] "oa-exist:2" by fastforce
  AOT_hence \<open>\<not>\<^bold>\<A>[F\<^sub>3]b\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>3]b\<close> and \<open>\<^bold>\<A>[F\<^sub>3]a\<close> and \<open>\<^bold>\<Delta>[F\<^sub>3]a\<close>
    using "&E" by blast+
  note props = props this

  AOT_have \<open>\<not>\<^bold>\<A>[E!]b & \<^bold>\<Delta>[E!]b & \<not>\<^bold>\<A>[E!]a & \<not>\<^bold>\<Delta>[E!]a\<close>
    by (meson "&I" delta_concrete_b not_act_concrete_a not_act_concrete_b not_delta_concrete_a)
  then AOT_obtain F\<^sub>4 where \<open>\<not>\<^bold>\<A>[F\<^sub>4]b & \<^bold>\<Delta>[F\<^sub>4]b & \<not>\<^bold>\<A>[F\<^sub>4]a & \<not>\<^bold>\<Delta>[F\<^sub>4]a\<close>
    using "cqt:2[concrete]"[axiom_inst] "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<not>\<^bold>\<A>[F\<^sub>4]b\<close> and \<open>\<^bold>\<Delta>[F\<^sub>4]b\<close> and \<open>\<not>\<^bold>\<A>[F\<^sub>4]a\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>4]a\<close>
    using "&E" by blast+
  note props = props this

  AOT_modally_strict {
    AOT_have \<open>[\<lambda>y q\<^sub>0]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<not>\<^bold>\<A>[\<lambda>y q\<^sub>0]b & \<^bold>\<Delta>[\<lambda>y q\<^sub>0]b & \<not>\<^bold>\<A>[\<lambda>y q\<^sub>0]a & \<^bold>\<Delta>[\<lambda>y q\<^sub>0]a\<close>
    by (safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
       (auto simp: not_act_q_zero delta_q_zero)
  ultimately AOT_obtain F\<^sub>5 where \<open>\<not>\<^bold>\<A>[F\<^sub>5]b & \<^bold>\<Delta>[F\<^sub>5]b & \<not>\<^bold>\<A>[F\<^sub>5]a & \<^bold>\<Delta>[F\<^sub>5]a\<close>
    using "cqt:2[concrete]"[axiom_inst] "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<not>\<^bold>\<A>[F\<^sub>5]b\<close> and \<open>\<^bold>\<Delta>[F\<^sub>5]b\<close> and \<open>\<not>\<^bold>\<A>[F\<^sub>5]a\<close> and \<open>\<^bold>\<Delta>[F\<^sub>5]a\<close>
    using "&E" by blast+
  note props = props this

  let ?\<Pi> = "\<guillemotleft>[\<lambda>y [E!]y \<or> ([A!]y & \<not>q\<^sub>0)]\<guillemotright>"
  AOT_modally_strict {
    AOT_have \<open>[\<guillemotleft>?\<Pi>\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<not>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]a & \<not>\<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]a\<close>
  proof(safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_have \<open>\<^bold>\<A>\<not>([A!]b & \<not>q\<^sub>0)\<close>
      by (metis "Act-Basic:1" "Act-Basic:2" abstract_prop "&E"(1) "\<or>E"(2)
                "\<equiv>E"(1) "raa-cor:3")
    moreover AOT_have \<open>\<not>\<^bold>\<A>[E!]b\<close>
      using b_prop "&E"(2) by blast
    ultimately AOT_have 2: \<open>\<^bold>\<A>(\<not>[E!]b & \<not>([A!]b & \<not>q\<^sub>0))\<close>
      by (metis "Act-Basic:2" "Act-Sub:1" "&I" "\<equiv>E"(3) "raa-cor:1")
    AOT_have \<open>\<^bold>\<A>\<not>([E!]b \<or> ([A!]b & \<not>q\<^sub>0))\<close>
      by (AOT_subst \<open>\<guillemotleft>\<not>([E!]b \<or> ([A!]b & \<not>q\<^sub>0))\<guillemotright>\<close> \<open>\<guillemotleft>\<not>[E!]b & \<not>([A!]b & \<not>q\<^sub>0)\<guillemotright>\<close>)
         (auto simp: "oth-class-taut:5:d" 2)
    AOT_thus \<open>\<not>\<^bold>\<A>([E!]b \<or> ([A!]b & \<not>q\<^sub>0))\<close>
      by (metis "\<not>\<not>I" "Act-Sub:1" "\<equiv>E"(4))
  next
    AOT_show \<open>\<^bold>\<Delta>([E!]b \<or> ([A!]b & \<not>q\<^sub>0))\<close>
    proof (rule not_act_and_pos_delta)
      AOT_show \<open>\<not>\<^bold>\<A>([E!]b \<or> ([A!]b & \<not>q\<^sub>0))\<close>
        by (metis "Act-Basic:2" "Act-Basic:9" "\<or>E"(2) "Conjunction Simplification"(1) "\<equiv>E"(4) "modus-tollens:1" not_act_abs_b not_act_concrete_b "raa-cor:3")
    next
      AOT_show \<open>\<diamond>([E!]b \<or> ([A!]b & \<not>q\<^sub>0))\<close>
        using "KBasic2:2" b_prop "&E"(1) "\<or>I"(1) "\<equiv>E"(3) "raa-cor:3" by blast
    qed
  next AOT_show \<open>\<^bold>\<A>([E!]a \<or> ([A!]a & \<not>q\<^sub>0))\<close>
      by (metis "Act-Basic:1" "Act-Basic:2" "Act-Basic:9" act_abs_a "&I" "\<or>I"(2) "\<or>E"(2) "\<equiv>E"(3) not_act_q_zero "raa-cor:1")
  next AOT_show \<open>\<not>\<^bold>\<Delta>([E!]a \<or> ([A!]a & \<not>q\<^sub>0))\<close>
    proof (rule act_and_not_nec_not_delta)
      AOT_show \<open>\<^bold>\<A>([E!]a \<or> ([A!]a & \<not>q\<^sub>0))\<close>
        by (metis "Act-Basic:1" "Act-Basic:2" "Act-Basic:9" act_abs_a "&I" "\<or>I"(2) "\<or>E"(2) "\<equiv>E"(3) not_act_q_zero "raa-cor:1")
    next
      AOT_have \<open>\<box>\<not>[E!]a\<close>
        by (metis "\<equiv>\<^sub>d\<^sub>fI" AOT_dia "&I" "\<or>I"(2) necessary_or_contingently_false not_act_concrete_a not_delta_concrete_a "raa-cor:3")
      moreover AOT_have \<open>\<diamond>\<not>([A!]a & \<not>q\<^sub>0)\<close>
        by (metis "KBasic2:1" "KBasic:11" "KBasic:3" "&E"(1) "&E"(2) "\<equiv>E"(1) q\<^sub>0_prop "raa-cor:3")
      ultimately AOT_have \<open>\<diamond>(\<not>[E!]a & \<not>([A!]a & \<not>q\<^sub>0))\<close> by (metis "KBasic:16" "&I" "vdash-properties:10")
      AOT_hence \<open>\<diamond>\<not>([E!]a \<or> ([A!]a & \<not>q\<^sub>0))\<close>
        by (metis "RE\<diamond>" "\<equiv>E"(2) "oth-class-taut:5:d")
      AOT_thus \<open>\<not>\<box>([E!]a \<or> ([A!]a & \<not>q\<^sub>0))\<close> by (metis "KBasic:12" "\<equiv>E"(1) "raa-cor:3")
    qed
  qed
  ultimately AOT_obtain F\<^sub>6 where \<open>\<not>\<^bold>\<A>[F\<^sub>6]b & \<^bold>\<Delta>[F\<^sub>6]b & \<^bold>\<A>[F\<^sub>6]a & \<not>\<^bold>\<Delta>[F\<^sub>6]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<not>\<^bold>\<A>[F\<^sub>6]b\<close> and \<open>\<^bold>\<Delta>[F\<^sub>6]b\<close> and \<open>\<^bold>\<A>[F\<^sub>6]a\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>6]a\<close>
    using "&E" by blast+
  note props = props this

  let ?\<Pi> = "\<guillemotleft>[\<lambda>y [A!]y \<or> [E!]y]\<guillemotright>"
  AOT_modally_strict {
    AOT_have \<open>[\<guillemotleft>?\<Pi>\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<not>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]a & \<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]a\<close>
  proof(safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>\<not>\<^bold>\<A>([A!]b \<or> [E!]b)\<close>
      using "Act-Basic:9" "\<or>E"(2) "\<equiv>E"(4) not_act_abs_b not_act_concrete_b "raa-cor:3" by blast
  next AOT_show \<open>\<^bold>\<Delta>([A!]b \<or> [E!]b)\<close>
    proof (rule not_act_and_pos_delta)
      AOT_show \<open>\<not>\<^bold>\<A>([A!]b \<or> [E!]b)\<close>
        using "Act-Basic:9" "\<or>E"(2) "\<equiv>E"(4) not_act_abs_b not_act_concrete_b "raa-cor:3" by blast
    next AOT_show \<open>\<diamond>([A!]b \<or> [E!]b)\<close>
        using "KBasic2:2" b_prop "&E"(1) "\<or>I"(2) "\<equiv>E"(2) by blast
    qed
  next AOT_show \<open>\<^bold>\<A>([A!]a \<or> [E!]a)\<close>
      by (meson "Act-Basic:9" act_abs_a "\<or>I"(1) "\<equiv>E"(2))
  next AOT_show \<open>\<^bold>\<Delta>([A!]a \<or> [E!]a) \<close>
    proof (rule nec_delta)
      AOT_show \<open>\<box>([A!]a \<or> [E!]a)\<close>
        by (metis "KBasic:15" act_abs_a act_and_not_nec_not_delta "Disjunction Addition"(1) delta_abs_a "raa-cor:3" "vdash-properties:10")
    qed
  qed
  ultimately AOT_obtain F\<^sub>7 where \<open>\<not>\<^bold>\<A>[F\<^sub>7]b & \<^bold>\<Delta>[F\<^sub>7]b & \<^bold>\<A>[F\<^sub>7]a & \<^bold>\<Delta>[F\<^sub>7]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<not>\<^bold>\<A>[F\<^sub>7]b\<close> and \<open>\<^bold>\<Delta>[F\<^sub>7]b\<close> and \<open>\<^bold>\<A>[F\<^sub>7]a\<close> and \<open>\<^bold>\<Delta>[F\<^sub>7]a\<close>
    using "&E" by blast+
  note props = props this

  let ?\<Pi> = "\<guillemotleft>[\<lambda>y [O!]y & \<not>[E!]y]\<guillemotright>"
  AOT_modally_strict {
    AOT_have \<open>[\<guillemotleft>?\<Pi>\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<not>\<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<not>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]a & \<not>\<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]a\<close>
  proof(safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>\<^bold>\<A>([O!]b & \<not>[E!]b)\<close>
      by (metis "Act-Basic:1" "Act-Basic:2" act_ord_b "&I" "\<or>E"(2) "\<equiv>E"(3) not_act_concrete_b "raa-cor:3")
  next AOT_show \<open>\<not>\<^bold>\<Delta>([O!]b & \<not>[E!]b)\<close>
      by (metis (no_types, hide_lams) AOT_dia "Act-Sub:1" "RM:1" act_and_not_nec_not_delta "act-conj-act:3"
                act_ord_b b_prop "&I" "&E"(1) "Conjunction Simplification"(2) "df-rules-formulas[3]"
                "\<equiv>E"(3) "raa-cor:1" "\<rightarrow>E")
  next AOT_show \<open>\<not>\<^bold>\<A>([O!]a & \<not>[E!]a)\<close>
      using "Act-Basic:2" "&E"(1) "\<equiv>E"(1) not_act_ord_a "raa-cor:3" by blast
  next AOT_have \<open>\<not>\<diamond>([O!]a & \<not>[E!]a)\<close>
      by (metis "KBasic2:3" "&E"(1) "\<equiv>E"(4) not_act_ord_a oa_facts_3 oa_facts_7 "raa-cor:3" "vdash-properties:10")
    AOT_thus \<open>\<not>\<^bold>\<Delta>([O!]a & \<not>[E!]a)\<close>
      by (rule impossible_delta)
  qed      
  ultimately AOT_obtain F\<^sub>8 where \<open>\<^bold>\<A>[F\<^sub>8]b & \<not>\<^bold>\<Delta>[F\<^sub>8]b & \<not>\<^bold>\<A>[F\<^sub>8]a & \<not>\<^bold>\<Delta>[F\<^sub>8]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<^bold>\<A>[F\<^sub>8]b\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>8]b\<close> and \<open>\<not>\<^bold>\<A>[F\<^sub>8]a\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>8]a\<close>
    using "&E" by blast+
  note props = props this

  (* TODO_PLM: binary property 9 wrong in PLM *)
  let ?\<Pi> = "\<guillemotleft>[\<lambda>y \<not>[E!]y & ([O!]y \<or> q\<^sub>0)]\<guillemotright>"
  AOT_modally_strict {
    AOT_have \<open>[\<guillemotleft>?\<Pi>\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<not>\<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<not>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]a & \<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]a\<close>
  proof(safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>\<^bold>\<A>(\<not>[E!]b & ([O!]b \<or> q\<^sub>0))\<close>
      by (metis "Act-Basic:1" "Act-Basic:2" "Act-Basic:9" act_ord_b "&I" "\<or>I"(1)
                "\<or>E"(2) "\<equiv>E"(3) not_act_concrete_b "raa-cor:1")
  next AOT_show \<open>\<not>\<^bold>\<Delta>(\<not>[E!]b & ([O!]b \<or> q\<^sub>0))\<close>
    proof (rule act_and_pos_not_not_delta)
      AOT_show \<open>\<^bold>\<A>(\<not>[E!]b & ([O!]b \<or> q\<^sub>0))\<close>
        by (metis "Act-Basic:1" "Act-Basic:2" "Act-Basic:9" act_ord_b "&I" "\<or>I"(1)
                  "\<or>E"(2) "\<equiv>E"(3) not_act_concrete_b "raa-cor:1")
    next
      AOT_show \<open>\<diamond>\<not>(\<not>[E!]b & ([O!]b \<or> q\<^sub>0))\<close>
      proof (AOT_subst \<open>\<guillemotleft>\<not>(\<not>[E!]b & ([O!]b \<or> q\<^sub>0))\<guillemotright>\<close> \<open>\<guillemotleft>[E!]b \<or> \<not>([O!]b \<or> q\<^sub>0)\<guillemotright>\<close>)
        AOT_modally_strict {
          AOT_show \<open>\<not>(\<not>[E!]b & ([O!]b \<or> q\<^sub>0)) \<equiv> [E!]b \<or> \<not>([O!]b \<or> q\<^sub>0)\<close>
            by (metis "&I" "&E"(1) "&E"(2) "\<or>I"(1) "\<or>I"(2) "\<or>E"(2) "deduction-theorem" "\<equiv>I" "reductio-aa:1")
        }
      next
        AOT_show \<open>\<diamond>([E!]b \<or> \<not>([O!]b \<or> q\<^sub>0))\<close>
          using "KBasic2:2" b_prop "&E"(1) "\<or>I"(1) "\<equiv>E"(3) "raa-cor:3" by blast
       qed
     qed
   next
     AOT_show \<open>\<not>\<^bold>\<A>(\<not>[E!]a & ([O!]a \<or> q\<^sub>0))\<close>
       using "Act-Basic:2" "Act-Basic:9" "&E"(2) "\<or>E"(3) "\<equiv>E"(1) not_act_ord_a not_act_q_zero "reductio-aa:2" by blast
   next
     AOT_show \<open>\<^bold>\<Delta>(\<not>[E!]a & ([O!]a \<or> q\<^sub>0))\<close>
     proof (rule not_act_and_pos_delta)
       AOT_show \<open>\<not>\<^bold>\<A>(\<not>[E!]a & ([O!]a \<or> q\<^sub>0))\<close>
         by (metis "Act-Basic:2" "Act-Basic:9" "&E"(2) "\<or>E"(3) "\<equiv>E"(1) not_act_ord_a not_act_q_zero "reductio-aa:2")
     next
       AOT_have \<open>\<box>\<not>[E!]a\<close>
         using "KBasic2:1" "\<equiv>E"(2) not_act_and_pos_delta not_act_concrete_a not_delta_concrete_a "raa-cor:5" by blast
       moreover AOT_have \<open>\<diamond>([O!]a \<or> q\<^sub>0)\<close>
         by (metis "KBasic2:2" "&E"(1) "\<or>I"(2) "\<equiv>E"(3) q\<^sub>0_prop "raa-cor:3")
       ultimately AOT_show \<open>\<diamond>(\<not>[E!]a & ([O!]a \<or> q\<^sub>0))\<close>
         by (metis "KBasic:16" "&I" "vdash-properties:10")
     qed
   qed
  ultimately AOT_obtain F\<^sub>9 where \<open>\<^bold>\<A>[F\<^sub>9]b & \<not>\<^bold>\<Delta>[F\<^sub>9]b & \<not>\<^bold>\<A>[F\<^sub>9]a & \<^bold>\<Delta>[F\<^sub>9]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<^bold>\<A>[F\<^sub>9]b\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>9]b\<close> and \<open>\<not>\<^bold>\<A>[F\<^sub>9]a\<close> and \<open>\<^bold>\<Delta>[F\<^sub>9]a\<close>
    using "&E" by blast+
  note props = props this

  AOT_modally_strict {
    AOT_have \<open>[\<lambda>y \<not>q\<^sub>0]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<^bold>\<A>[\<lambda>y \<not>q\<^sub>0]b & \<not>\<^bold>\<Delta>[\<lambda>y \<not>q\<^sub>0]b & \<^bold>\<A>[\<lambda>y \<not>q\<^sub>0]a & \<not>\<^bold>\<Delta>[\<lambda>y \<not>q\<^sub>0]a\<close>
    by (safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1]; auto simp: act_not_q_zero not_delta_not_q_zero)
  ultimately AOT_obtain F\<^sub>1\<^sub>0 where \<open>\<^bold>\<A>[F\<^sub>1\<^sub>0]b & \<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>0]b & \<^bold>\<A>[F\<^sub>1\<^sub>0]a & \<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>0]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<^bold>\<A>[F\<^sub>1\<^sub>0]b\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>0]b\<close> and \<open>\<^bold>\<A>[F\<^sub>1\<^sub>0]a\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>0]a\<close>
    using "&E" by blast+
  note props = props this

  AOT_modally_strict {
    AOT_have \<open>[\<lambda>y \<not>[E!]y]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<^bold>\<A>[\<lambda>y \<not>[E!]y]b & \<not>\<^bold>\<Delta>[\<lambda>y \<not>[E!]y]b & \<^bold>\<A>[\<lambda>y \<not>[E!]y]a & \<^bold>\<Delta>[\<lambda>y \<not>[E!]y]a\<close>
  proof (safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>\<^bold>\<A>\<not>[E!]b\<close>
      using "Act-Basic:1" "\<or>E"(2) not_act_concrete_b by blast
  next AOT_show \<open>\<not>\<^bold>\<Delta>\<not>[E!]b\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" AOT_dia "Act-Basic:1" act_and_not_nec_not_delta b_prop "&E"(1) "\<or>E"(2) not_act_concrete_b by blast
  next AOT_show \<open>\<^bold>\<A>\<not>[E!]a\<close>
      using "Act-Basic:1" "\<or>E"(2) not_act_concrete_a by blast
  next AOT_show \<open>\<^bold>\<Delta>\<not>[E!]a\<close>
      using "KBasic2:1" "\<equiv>E"(2) nec_delta not_act_and_pos_delta not_act_concrete_a not_delta_concrete_a "reductio-aa:1" by blast
  qed
  ultimately AOT_obtain F\<^sub>1\<^sub>1 where \<open>\<^bold>\<A>[F\<^sub>1\<^sub>1]b & \<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>1]b & \<^bold>\<A>[F\<^sub>1\<^sub>1]a & \<^bold>\<Delta>[F\<^sub>1\<^sub>1]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<^bold>\<A>[F\<^sub>1\<^sub>1]b\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>1]b\<close> and \<open>\<^bold>\<A>[F\<^sub>1\<^sub>1]a\<close> and \<open>\<^bold>\<Delta>[F\<^sub>1\<^sub>1]a\<close>
    using "&E" by blast+
  note props = props this

  AOT_have \<open>\<^bold>\<A>[O!]b & \<^bold>\<Delta>[O!]b & \<not>\<^bold>\<A>[O!]a & \<not>\<^bold>\<Delta>[O!]a\<close>
    by (simp add: act_ord_b "&I" delta_ord_b not_act_ord_a not_delta_ord_a)
  then AOT_obtain F\<^sub>1\<^sub>2 where \<open>\<^bold>\<A>[F\<^sub>1\<^sub>2]b & \<^bold>\<Delta>[F\<^sub>1\<^sub>2]b & \<not>\<^bold>\<A>[F\<^sub>1\<^sub>2]a & \<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>2]a\<close>
    using "oa-exist:1" "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<^bold>\<A>[F\<^sub>1\<^sub>2]b\<close> and \<open>\<^bold>\<Delta>[F\<^sub>1\<^sub>2]b\<close> and \<open>\<not>\<^bold>\<A>[F\<^sub>1\<^sub>2]a\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>2]a\<close>
    using "&E" by blast+
  note props = props this

  let ?\<Pi> = "\<guillemotleft>[\<lambda>y [O!]y \<or> q\<^sub>0]\<guillemotright>"
  AOT_modally_strict {
    AOT_have \<open>[\<guillemotleft>?\<Pi>\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<not>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]a & \<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]a\<close>
  proof (safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>\<^bold>\<A>([O!]b \<or> q\<^sub>0)\<close>
      by (meson "Act-Basic:9" act_ord_b "\<or>I"(1) "\<equiv>E"(2))
  next AOT_show \<open>\<^bold>\<Delta>([O!]b \<or> q\<^sub>0)\<close>
      by (meson "KBasic:15" b_ord "\<or>I"(1) nec_delta oa_facts_1 "vdash-properties:10")
  next AOT_show \<open>\<not>\<^bold>\<A>([O!]a \<or> q\<^sub>0)\<close>
      using "Act-Basic:9" "\<or>E"(2) "\<equiv>E"(4) not_act_ord_a not_act_q_zero "raa-cor:3" by blast
  next AOT_show \<open>\<^bold>\<Delta>([O!]a \<or> q\<^sub>0)\<close>
    proof (rule not_act_and_pos_delta)
      AOT_show \<open>\<not>\<^bold>\<A>([O!]a \<or> q\<^sub>0)\<close>
        using "Act-Basic:9" "\<or>E"(2) "\<equiv>E"(4) not_act_ord_a not_act_q_zero "raa-cor:3" by blast
    next AOT_show \<open>\<diamond>([O!]a \<or> q\<^sub>0)\<close>
        using "KBasic2:2" "&E"(1) "\<or>I"(2) "\<equiv>E"(2) q\<^sub>0_prop by blast
    qed
  qed
  ultimately AOT_obtain F\<^sub>1\<^sub>3 where \<open>\<^bold>\<A>[F\<^sub>1\<^sub>3]b & \<^bold>\<Delta>[F\<^sub>1\<^sub>3]b & \<not>\<^bold>\<A>[F\<^sub>1\<^sub>3]a & \<^bold>\<Delta>[F\<^sub>1\<^sub>3]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<^bold>\<A>[F\<^sub>1\<^sub>3]b\<close> and \<open>\<^bold>\<Delta>[F\<^sub>1\<^sub>3]b\<close> and \<open>\<not>\<^bold>\<A>[F\<^sub>1\<^sub>3]a\<close> and \<open>\<^bold>\<Delta>[F\<^sub>1\<^sub>3]a\<close>
    using "&E" by blast+
  note props = props this

  let ?\<Pi> = "\<guillemotleft>[\<lambda>y [O!]y \<or> \<not>q\<^sub>0]\<guillemotright>"
  AOT_modally_strict {
     AOT_have \<open>[\<guillemotleft>?\<Pi>\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
  } note 1 = this
  moreover AOT_have \<open>\<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]b & \<^bold>\<A>[\<guillemotleft>?\<Pi>\<guillemotright>]a & \<not>\<^bold>\<Delta>[\<guillemotleft>?\<Pi>\<guillemotright>]a\<close>
  proof (safe intro!: "&I"; AOT_subst_using subst: beta_C_meta[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>\<^bold>\<A>([O!]b \<or> \<not>q\<^sub>0)\<close>
      by (meson "Act-Basic:9" act_not_q_zero "\<or>I"(2) "\<equiv>E"(2))
  next AOT_show \<open>\<^bold>\<Delta>([O!]b \<or> \<not>q\<^sub>0)\<close>
      by (meson "KBasic:15" b_ord "\<or>I"(1) nec_delta oa_facts_1 "vdash-properties:10")
  next AOT_show \<open>\<^bold>\<A>([O!]a \<or> \<not>q\<^sub>0)\<close>
      by (meson "Act-Basic:9" act_not_q_zero "\<or>I"(2) "\<equiv>E"(2))
  next AOT_show \<open>\<not>\<^bold>\<Delta>([O!]a \<or> \<not>q\<^sub>0)\<close>
    proof(rule act_and_pos_not_not_delta)
      AOT_show \<open>\<^bold>\<A>([O!]a \<or> \<not>q\<^sub>0)\<close>
        by (meson "Act-Basic:9" act_not_q_zero "\<or>I"(2) "\<equiv>E"(2))
    next
      AOT_have \<open>\<box>\<not>[O!]a\<close>
        using "KBasic2:1" "\<equiv>E"(2) not_act_and_pos_delta not_act_ord_a not_delta_ord_a "raa-cor:6" by blast
      moreover AOT_have \<open>\<diamond>q\<^sub>0\<close>
        by (meson "&E"(1) q\<^sub>0_prop)
      ultimately AOT_have 2: \<open>\<diamond>(\<not>[O!]a & q\<^sub>0)\<close>
         by (metis "KBasic:16" "&I" "vdash-properties:10")
      AOT_show \<open>\<diamond>\<not>([O!]a \<or> \<not>q\<^sub>0)\<close>
      proof (AOT_subst_rev \<open>\<guillemotleft>\<not>[O!]a & q\<^sub>0\<guillemotright>\<close> \<open>\<guillemotleft>\<not>([O!]a \<or> \<not>q\<^sub>0)\<guillemotright>\<close>)
        AOT_modally_strict {
          AOT_show \<open>\<not>[O!]a & q\<^sub>0 \<equiv> \<not>([O!]a \<or> \<not>q\<^sub>0)\<close>
            by (metis "&I" "&E"(1) "&E"(2) "\<or>I"(1) "\<or>I"(2)
                      "\<or>E"(3) "deduction-theorem" "\<equiv>I" "raa-cor:3")
        }
      next
        AOT_show \<open>\<diamond>(\<not>[O!]a & q\<^sub>0)\<close>
          using "2" by blast
      qed
    qed
  qed
  ultimately AOT_obtain F\<^sub>1\<^sub>4 where \<open>\<^bold>\<A>[F\<^sub>1\<^sub>4]b & \<^bold>\<Delta>[F\<^sub>1\<^sub>4]b & \<^bold>\<A>[F\<^sub>1\<^sub>4]a & \<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>4]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<^bold>\<A>[F\<^sub>1\<^sub>4]b\<close> and \<open>\<^bold>\<Delta>[F\<^sub>1\<^sub>4]b\<close> and \<open>\<^bold>\<A>[F\<^sub>1\<^sub>4]a\<close> and \<open>\<not>\<^bold>\<Delta>[F\<^sub>1\<^sub>4]a\<close>
    using "&E" by blast+
  note props = props this

  AOT_have \<open>[L]\<down>\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF L_def]) "cqt:2[lambda]"+
  moreover AOT_have \<open>\<^bold>\<A>[L]b & \<^bold>\<Delta>[L]b & \<^bold>\<A>[L]a & \<^bold>\<Delta>[L]a\<close>
  proof (safe intro!: "&I")
    AOT_show \<open>\<^bold>\<A>[L]b\<close>
      by (meson nec_L "nec-imp-act" "vdash-properties:10")
    next AOT_show \<open>\<^bold>\<Delta>[L]b\<close> using nec_L nec_delta by blast
    next AOT_show \<open>\<^bold>\<A>[L]a\<close> by (meson nec_L "nec-imp-act" "vdash-properties:10")
    next AOT_show \<open>\<^bold>\<Delta>[L]a\<close> using nec_L nec_delta by blast
  qed
  ultimately AOT_obtain F\<^sub>1\<^sub>5 where \<open>\<^bold>\<A>[F\<^sub>1\<^sub>5]b & \<^bold>\<Delta>[F\<^sub>1\<^sub>5]b & \<^bold>\<A>[F\<^sub>1\<^sub>5]a & \<^bold>\<Delta>[F\<^sub>1\<^sub>5]a\<close>
    using "\<exists>I"(1)[rotated, THEN "\<exists>E"[rotated]] by fastforce
  AOT_hence \<open>\<^bold>\<A>[F\<^sub>1\<^sub>5]b\<close> and \<open>\<^bold>\<Delta>[F\<^sub>1\<^sub>5]b\<close> and \<open>\<^bold>\<A>[F\<^sub>1\<^sub>5]a\<close> and \<open>\<^bold>\<Delta>[F\<^sub>1\<^sub>5]a\<close>
    using "&E" by blast+
  note props = props this

  show ?thesis
    by (rule "\<exists>I"(2)[where \<beta>=F\<^sub>0]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>1]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>2];
           rule "\<exists>I"(2)[where \<beta>=F\<^sub>3]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>4]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>5];
           rule "\<exists>I"(2)[where \<beta>=F\<^sub>6]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>7]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>8];
           rule "\<exists>I"(2)[where \<beta>=F\<^sub>9]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>1\<^sub>0]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>1\<^sub>1];
           rule "\<exists>I"(2)[where \<beta>=F\<^sub>1\<^sub>2]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>1\<^sub>3]; rule "\<exists>I"(2)[where \<beta>=F\<^sub>1\<^sub>4];
           rule "\<exists>I"(2)[where \<beta>=F\<^sub>1\<^sub>5]; safe intro!: "&I")
       (match conclusion in "[?v \<Turnstile> [F] \<noteq> [G]]" for F G \<Rightarrow> \<open>
        match props in A: "[?v \<Turnstile> \<not>\<phi>{F}]" for \<phi> \<Rightarrow> \<open>
        match (\<phi>) in "\<lambda>a . ?p" \<Rightarrow> \<open>fail\<close> \<bar> "\<lambda>a . a" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>
        match props in B: "[?v \<Turnstile> \<phi>{G}]" \<Rightarrow> \<open>
        fact pos_not_equiv_ne_4[where F=F and G=G and \<phi>=\<phi>, THEN "\<rightarrow>E",
                                OF "oth-class-taut:4:h"[THEN "\<equiv>E"(2)],
                                OF "Disjunction Addition"(2)[THEN "\<rightarrow>E"],
                                OF "&I", OF A, OF B]\<close>\<close>\<close>\<close>)+
qed

AOT_theorem o_objects_exist_1: \<open>\<box>\<exists>x O!x\<close>
proof(rule RN)
  AOT_modally_strict {
    AOT_obtain a where \<open>\<diamond>(E!a & \<not>\<^bold>\<A>[E!]a)\<close>
      using "\<exists>E"[rotated, OF "qml:4"[axiom_inst, THEN "BF\<diamond>"[THEN "\<rightarrow>E"]]] by blast
    AOT_hence 1: \<open>\<diamond>E!a\<close> by (metis "KBasic2:3" "&E"(1) "\<rightarrow>E")
    AOT_have \<open>[\<lambda>x \<diamond>[E!]x]a\<close>
    proof (rule betaC_2_a; "cqt:2[lambda]"?)
      AOT_show \<open>a\<down>\<close> using "cqt:2[const_var]"[axiom_inst] by blast
    next
      AOT_show \<open>\<diamond>E!a\<close> by (fact 1)
    qed
    AOT_hence \<open>O!a\<close> by (rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_ordinary, rotated]) "cqt:2[lambda]"
    AOT_thus \<open>\<exists>x [O!]x\<close> by (rule "\<exists>I")
  }
qed

AOT_theorem o_objects_exist_2: \<open>\<box>\<exists>x A!x\<close>
proof (rule RN)
  AOT_modally_strict {
    AOT_obtain a where \<open>[A!]a\<close>
      using "A-objects"[axiom_inst] "\<exists>E"[rotated] "&E" by blast
    AOT_thus \<open>\<exists>x A!x\<close> using "\<exists>I" by blast
  }
qed

AOT_theorem o_objects_exist_3: \<open>\<box>\<not>\<forall>x O!x\<close>
  by (rule RN) (metis (no_types, hide_lams) "\<exists>E" "cqt-orig:1[const_var]" "\<equiv>E"(4) "modus-tollens:1" o_objects_exist_2 oa_contingent_2 "qml:2"[axiom_inst] "reductio-aa:2")

AOT_theorem o_objects_exist_4: \<open>\<box>\<not>\<forall>x A!x\<close>
  by (rule RN) (metis (mono_tags, hide_lams) "\<exists>E" "cqt-orig:1[const_var]" "\<equiv>E"(1) "modus-tollens:1" o_objects_exist_1 oa_contingent_2 "qml:2"[axiom_inst] "\<rightarrow>E")

AOT_theorem o_objects_exist_5: \<open>\<box>\<not>\<forall>x E!x\<close>
proof (rule RN; rule "raa-cor:2")
  AOT_modally_strict {
    AOT_assume \<open>\<forall>x E!x\<close>
    moreover AOT_obtain a where abs: \<open>A!a\<close>
      using o_objects_exist_2[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] "\<exists>E"[rotated] by blast
    ultimately AOT_have \<open>E!a\<close> using "\<forall>E" by blast
    AOT_hence 1: \<open>\<diamond>E!a\<close> by (metis "T\<diamond>" "\<rightarrow>E")
    AOT_have \<open>[\<lambda>y \<diamond>E!y]a\<close>
    proof (rule betaC_2_a; "cqt:2[lambda]"?)
      AOT_show \<open>a\<down>\<close> using "cqt:2[const_var]"[axiom_inst].
    next
      AOT_show \<open>\<diamond>E!a\<close> by (fact 1)
    qed
    AOT_hence \<open>O!a\<close>
      by (rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_ordinary, rotated]) "cqt:2[lambda]"
    AOT_hence \<open>\<not>A!a\<close> by (metis "\<equiv>E"(1) oa_contingent_2) 
    AOT_thus \<open>p & \<not>p\<close> for p using abs by (metis "raa-cor:3")
  }
qed

AOT_theorem partition: \<open>\<not>\<exists>x (O!x & A!x)\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>\<exists>x (O!x & A!x)\<close>
  then AOT_obtain a where \<open>O!a & A!a\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>p & \<not>p\<close> for p by (metis "&E"(1) "Conjunction Simplification"(2) "\<equiv>E"(1) "modus-tollens:1" oa_contingent_2 "raa-cor:3")
qed

AOT_define eq_E :: \<open>\<Pi>\<close> ("'(=\<^sub>E')") \<open>(=\<^sub>E) =\<^sub>d\<^sub>f [\<lambda>xy O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)]\<close>

syntax "_AOT_eq_E_infix" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "=\<^sub>E" 50)
translations
  "_AOT_eq_E_infix \<kappa> \<kappa>'" == "CONST AOT_exe (CONST eq_E) (\<kappa>, \<kappa>')"

AOT_theorem eq_E_denotes: \<open>[(=\<^sub>E)]\<down>\<close>
  by (rule "=\<^sub>d\<^sub>fI"(2)[OF eq_E]) "cqt:2[lambda]"+

AOT_theorem eq_E_simple_1: \<open>x =\<^sub>E y \<equiv> (O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y))\<close>
proof -
  (* TODO: rethink the product hacks *)
  AOT_have 0: \<open>\<guillemotleft>(AOT_term_of_var x,AOT_term_of_var y)\<guillemotright>\<down>\<close>
    by (simp add: "&I" "cqt:2[const_var]" prod_denotesI "vdash-properties:1[2]")
  AOT_have 1: \<open>[\<lambda>xy [O!]x & [O!]y & \<box>\<forall>F ([F]x \<equiv> [F]y)]\<down>\<close> by "cqt:2[lambda]"
  show ?thesis apply (rule "=\<^sub>d\<^sub>fI"(2)[OF eq_E]; "cqt:2[lambda]"?)
    using beta_C_meta[THEN "\<rightarrow>E", OF 1, unvarify \<nu>\<^sub>1\<nu>\<^sub>n, of "(AOT_term_of_var x,AOT_term_of_var y)", OF 0]
    by fast
qed

AOT_theorem eq_E_simple_2: \<open>x =\<^sub>E y \<rightarrow> x = y\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>x =\<^sub>E y\<close>
  AOT_hence \<open>O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)\<close> using eq_E_simple_1[THEN "\<equiv>E"(1)] by blast
  AOT_thus \<open>x = y\<close>
    using "\<equiv>\<^sub>d\<^sub>fI"[OF "identity:1"] "\<or>I" by blast
qed

AOT_theorem id_nec3_1: \<open>x =\<^sub>E y \<equiv> \<box>(x =\<^sub>E y)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>x =\<^sub>E y\<close>
  AOT_hence \<open>O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
    using eq_E_simple_1 "\<equiv>E" by blast
  AOT_hence \<open>\<box>O!x & \<box>O!y & \<box>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
    by (metis "S5Basic:6" "&I" "&E"(1) "&E"(2) "\<equiv>E"(4) oa_facts_1 "raa-cor:3" "vdash-properties:10")
  AOT_hence 1: \<open>\<box>(O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y))\<close>
    by (metis "&E"(1) "&E"(2) "\<equiv>E"(2) "KBasic:3" "&I")
  AOT_show \<open>\<box>(x =\<^sub>E y)\<close>
    apply (AOT_subst \<open>\<guillemotleft>x =\<^sub>E y\<guillemotright>\<close> \<open>\<guillemotleft>O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)\<guillemotright>\<close>)
     using eq_E_simple_1 apply presburger
    by (simp add: "1")
next
  AOT_assume \<open>\<box>(x =\<^sub>E y)\<close>
  AOT_thus \<open>x =\<^sub>E y\<close> using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
qed

AOT_theorem id_nec3_2: \<open>\<diamond>(x =\<^sub>E y) \<equiv> x =\<^sub>E y\<close>
  by (meson "RE\<diamond>" "S5Basic:2" id_nec3_1 "\<equiv>E"(1) "\<equiv>E"(5) "Commutativity of \<equiv>")

AOT_theorem id_nec3_3: \<open>\<diamond>(x =\<^sub>E y) \<equiv> \<box>(x =\<^sub>E y)\<close>
  by (meson id_nec3_1 id_nec3_2 "\<equiv>E"(5))

syntax "_AOT_non_eq_E" :: \<open>\<Pi>\<close> ("'(\<noteq>\<^sub>E')")
translations
  (\<Pi>) "(\<noteq>\<^sub>E)" == (\<Pi>) "(=\<^sub>E)\<^sup>-"
syntax "_AOT_non_eq_E_infix" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<noteq>\<^sub>E" 50)
translations
 "_AOT_non_eq_E_infix \<kappa> \<kappa>'" == "CONST AOT_exe (CONST relation_negation (CONST eq_E)) (\<kappa>,\<kappa>')"

AOT_theorem thm_neg_eq_E: \<open>x \<noteq>\<^sub>E y \<equiv> \<not>(x =\<^sub>E y)\<close>
proof -
  (* TODO: rethink the product hacks *)
  AOT_have 0: \<open>\<guillemotleft>(AOT_term_of_var x,AOT_term_of_var y)\<guillemotright>\<down>\<close>
    by (simp add: "&I" "cqt:2[const_var]" prod_denotesI "vdash-properties:1[2]")
  AOT_have \<theta>: \<open>[\<lambda>x\<^sub>1...x\<^sub>2 \<not>(=\<^sub>E)x\<^sub>1...x\<^sub>2]\<down>\<close> by "cqt:2[lambda]" (* TODO_PLM: convoluted proof in PLM; TODO: product hack *)
  AOT_have \<open>x \<noteq>\<^sub>E y \<equiv> [\<lambda>x\<^sub>1...x\<^sub>2 \<not>(=\<^sub>E)x\<^sub>1...x\<^sub>2]xy\<close>
    by (rule "=\<^sub>d\<^sub>fI"(1)[OF df_relation_negation, OF \<theta>])
       (meson "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<not>(=\<^sub>E)xy\<close>
    apply (rule beta_C_meta[THEN "\<rightarrow>E", unvarify \<nu>\<^sub>1\<nu>\<^sub>n])
     apply "cqt:2[lambda]"
    by (fact 0)
  finally show ?thesis.
qed

AOT_theorem id_nec_4_1: \<open>x \<noteq>\<^sub>E y \<equiv> \<box>(x \<noteq>\<^sub>E y)\<close>
proof -
  AOT_have \<open>x \<noteq>\<^sub>E y \<equiv> \<not>(x =\<^sub>E y)\<close> using thm_neg_eq_E.
  also AOT_have \<open>\<dots> \<equiv> \<not>\<diamond>(x =\<^sub>E y)\<close>
    by (meson id_nec3_2 "\<equiv>E"(1) "Commutativity of \<equiv>" "oth-class-taut:4:b")
  also AOT_have \<open>\<dots> \<equiv> \<box>\<not>(x =\<^sub>E y)\<close>
    by (meson "KBasic2:1" "\<equiv>E"(2) "Commutativity of \<equiv>")
  also AOT_have \<open>\<dots> \<equiv> \<box>(x \<noteq>\<^sub>E y)\<close>
    by (AOT_subst_rev "\<guillemotleft>x \<noteq>\<^sub>E y\<guillemotright>" "\<guillemotleft>\<not>(x =\<^sub>E y)\<guillemotright>")
       (auto simp: thm_neg_eq_E "oth-class-taut:3:a")
  finally show ?thesis.
qed

AOT_theorem id_nec_4_2: \<open>\<diamond>(x \<noteq>\<^sub>E y) \<equiv> (x \<noteq>\<^sub>E y)\<close>
  by (meson "RE\<diamond>" "S5Basic:2" id_nec_4_1 "\<equiv>E"(2) "\<equiv>E"(5) "Commutativity of \<equiv>")

AOT_theorem id_nec_4_3: \<open>\<diamond>(x \<noteq>\<^sub>E y) \<equiv> \<box>(x \<noteq>\<^sub>E y)\<close>
  by (meson id_nec_4_1 id_nec_4_2 "\<equiv>E"(5))

AOT_theorem id_act2_1: \<open>x =\<^sub>E y \<equiv> \<^bold>\<A>x =\<^sub>E y\<close>
  by (meson "Act-Basic:5" "Act-Sub:2" "RA[2]" id_nec3_2 "\<equiv>E"(1) "\<equiv>E"(6))
AOT_theorem id_act2_2: \<open>x \<noteq>\<^sub>E y \<equiv> \<^bold>\<A>x \<noteq>\<^sub>E y\<close>
  by (meson "Act-Basic:5" "Act-Sub:2" "RA[2]" id_nec_4_2 "\<equiv>E"(1) "\<equiv>E"(6))

AOT_theorem ord_eq_Eequiv_1: \<open>O!x \<rightarrow> x =\<^sub>E x\<close>
proof (rule "\<rightarrow>I")
  AOT_assume 1: \<open>O!x\<close>
  AOT_show \<open>x =\<^sub>E x\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF eq_E]) apply "cqt:2[lambda]"
    apply (rule betaC_2_a)
      apply "cqt:2[lambda]"
     apply (simp add: "&I" "cqt:2[const_var]" prod_denotesI "vdash-properties:1[2]")
    by (simp add: "1" RN "&I" "oth-class-taut:3:a" "universal-cor")
qed

AOT_theorem ord_eq_Eequiv_2: \<open>x =\<^sub>E y \<rightarrow> y =\<^sub>E x\<close>
proof(rule CP)
  AOT_assume 1: \<open>x =\<^sub>E y\<close>
  AOT_hence 2: \<open>x = y\<close> by (metis eq_E_simple_2 "vdash-properties:10") 
  AOT_have \<open>O!x\<close> using 1 by (meson "&E"(1) eq_E_simple_1 "\<equiv>E"(1))
  AOT_hence \<open>x =\<^sub>E x\<close> using ord_eq_Eequiv_1 "\<rightarrow>E" by blast
  AOT_thus \<open>y =\<^sub>E x\<close> using "=E"[rotated, OF 2] by fast
qed

AOT_theorem ord_eq_Eequiv_3: \<open>(x =\<^sub>E y & y =\<^sub>E z) \<rightarrow> x =\<^sub>E z\<close>
proof (rule CP)
  AOT_assume 1: \<open>x =\<^sub>E y & y =\<^sub>E z\<close>
  AOT_hence \<open>x = y & y = z\<close>
    by (metis "&I" "&E"(1) "&E"(2) eq_E_simple_2 "vdash-properties:6")
  AOT_hence \<open>x = z\<close> by (metis "id-eq:3" "vdash-properties:6")
  moreover AOT_have \<open>x =\<^sub>E x\<close>
    using 1[THEN "&E"(1)] "&E"(1) eq_E_simple_1 "\<equiv>E"(1) ord_eq_Eequiv_1 "\<rightarrow>E" by blast
  ultimately AOT_show \<open>x =\<^sub>E z\<close>
    using "=E" by fast
qed

AOT_theorem ord_eq_E_eq: \<open>(O!x \<or> O!y) \<rightarrow> \<box>(x = y \<equiv> x =\<^sub>E y)\<close>
proof(rule CP)
  AOT_assume \<open>O!x \<or> O!y\<close>
  moreover {
    AOT_assume \<open>O!x\<close>
    AOT_hence \<open>\<box>O!x\<close> by (metis oa_facts_1 "vdash-properties:10")
    moreover {
      AOT_modally_strict {
        AOT_have \<open>O!x \<rightarrow> (x = y \<equiv> x =\<^sub>E y)\<close>
        proof (rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
          AOT_assume \<open>O!x\<close>
          AOT_hence \<open>x =\<^sub>E x\<close> by (metis ord_eq_Eequiv_1 "\<rightarrow>E")
          moreover AOT_assume \<open>x = y\<close>
          ultimately AOT_show \<open>x =\<^sub>E y\<close> using "=E" by fast
        next
          AOT_assume \<open>x =\<^sub>E y\<close>
          AOT_thus \<open>x = y\<close> by (metis eq_E_simple_2 "\<rightarrow>E")
        qed
      }
      AOT_hence \<open>\<box>O!x \<rightarrow> \<box>(x = y \<equiv> x =\<^sub>E y)\<close> by (metis "RM:1")
    }
    ultimately AOT_have \<open>\<box>(x = y \<equiv> x =\<^sub>E y)\<close> using "\<rightarrow>E" by blast
  }
  moreover {
    AOT_assume \<open>O!y\<close>
    AOT_hence \<open>\<box>O!y\<close> by (metis oa_facts_1 "vdash-properties:10")
    moreover {
      AOT_modally_strict {
        AOT_have \<open>O!y \<rightarrow> (x = y \<equiv> x =\<^sub>E y)\<close>
        proof (rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
          AOT_assume \<open>O!y\<close>
          AOT_hence \<open>y =\<^sub>E y\<close> by (metis ord_eq_Eequiv_1 "\<rightarrow>E")
          moreover AOT_assume \<open>x = y\<close>
          ultimately AOT_show \<open>x =\<^sub>E y\<close> using "=E" id_sym by fast
        next
          AOT_assume \<open>x =\<^sub>E y\<close>
          AOT_thus \<open>x = y\<close> by (metis eq_E_simple_2 "\<rightarrow>E")
        qed
      }
      AOT_hence \<open>\<box>O!y \<rightarrow> \<box>(x = y \<equiv> x =\<^sub>E y)\<close> by (metis "RM:1")
    }
    ultimately AOT_have \<open>\<box>(x = y \<equiv> x =\<^sub>E y)\<close> using "\<rightarrow>E" by blast
  }
  ultimately AOT_show \<open>\<box>(x = y \<equiv> x =\<^sub>E y)\<close> by (metis "\<or>E"(3) "raa-cor:1")
qed

AOT_theorem ord_eq_E_eq_2: \<open>O!y \<rightarrow> [\<lambda>x x = y]\<down>\<close>
proof (rule "\<rightarrow>I"; rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E"]; rule "&I")
  AOT_show \<open>[\<lambda>x x =\<^sub>E y]\<down>\<close> by "cqt:2[lambda]"
next
  AOT_assume \<open>O!y\<close>
  AOT_hence 1: \<open>\<box>(x = y \<equiv> x =\<^sub>E y)\<close> for x using ord_eq_E_eq "\<rightarrow>E" "\<or>I" by blast
  AOT_have \<open>\<box>(x =\<^sub>E y \<equiv> x = y)\<close> for x
    by (AOT_subst \<open>\<guillemotleft>x =\<^sub>E y \<equiv> x = y\<guillemotright>\<close> \<open>\<guillemotleft>x = y \<equiv> x =\<^sub>E y\<guillemotright>\<close>)
       (auto simp add: "Commutativity of \<equiv>" 1)
  AOT_hence \<open>\<forall>x \<box>(x =\<^sub>E y \<equiv> x = y)\<close> by (rule GEN)
  AOT_thus \<open>\<box>\<forall>x (x =\<^sub>E y \<equiv> x = y)\<close> by (rule BF[THEN "\<rightarrow>E"])
qed


AOT_theorem ord_eq_E_eq_3: \<open>[\<lambda>xy O!x & O!y & x = y]\<down>\<close>
proof (rule "safe-ext[2]"[axiom_inst, THEN "\<rightarrow>E"]; rule "&I")
  AOT_show \<open>[\<lambda>xy O!x & O!y & x =\<^sub>E y]\<down>\<close> by "cqt:2[lambda]"
next
  AOT_show \<open>\<box>\<forall>x\<forall>y ([O!]x & [O!]y & x =\<^sub>E y \<equiv> [O!]x & [O!]y & x = y)\<close>
  proof (rule RN; rule GEN; rule GEN; rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_modally_strict {
      AOT_show \<open>[O!]x & [O!]y & x = y\<close> if \<open>[O!]x & [O!]y & x =\<^sub>E y\<close> for x y
        by (metis "&I" "&E"(1) "Conjunction Simplification"(2) eq_E_simple_2
                  "modus-tollens:1" "raa-cor:1" that)
    }
  next
    AOT_modally_strict {
      AOT_show \<open>[O!]x & [O!]y & x =\<^sub>E y\<close> if \<open>[O!]x & [O!]y & x = y\<close> for x y
        apply(safe intro!: "&I")
          apply (metis that[THEN "&E"(1), THEN "&E"(1)])
         apply (metis that[THEN "&E"(1), THEN "&E"(2)])
        using "=E"[rotated, OF that[THEN "&E"(2)]]
              ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF that[THEN "&E"(1), THEN "&E"(1)]] by fast
    }
  qed
qed

AOT_theorem ind_nec: \<open>\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
  moreover AOT_have \<open>[\<lambda>x \<box>\<forall>F ([F]x \<equiv> [F]y)]\<down>\<close> by "cqt:2[lambda]"
  ultimately AOT_have \<open>[\<lambda>x \<box>\<forall>F ([F]x \<equiv> [F]y)]x \<equiv> [\<lambda>x \<box>\<forall>F ([F]x \<equiv> [F]y)]y\<close>
    using "\<forall>E" by blast
  moreover AOT_have \<open>[\<lambda>x \<box>\<forall>F ([F]x \<equiv> [F]y)]y\<close>
    apply (rule betaC_2_a)
      apply "cqt:2[lambda]"
     apply (fact "cqt:2[const_var]"[axiom_inst])
    by (simp add: RN GEN "oth-class-taut:3:a")
  ultimately AOT_have \<open>[\<lambda>x \<box>\<forall>F ([F]x \<equiv> [F]y)]x\<close> using "\<equiv>E" by blast
  AOT_thus \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
    using betaC_1_a by blast
qed

AOT_theorem ord_eq_E_1: \<open>(O!x & O!y) \<rightarrow> (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> x =\<^sub>E y)\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
  AOT_hence \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
    using ind_nec[THEN "\<rightarrow>E"] by blast
  moreover AOT_assume \<open>O!x & O!y\<close>
  ultimately AOT_have \<open>O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
    using "&I" by blast
  AOT_thus \<open>x =\<^sub>E y\<close> using eq_E_simple_1[THEN "\<equiv>E"(2)] by blast
qed

AOT_theorem ord_eq_E_2: \<open>(O!x & O!y) \<rightarrow> (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> x = y)\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume \<open>O!x & O!y\<close>
  moreover AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
  ultimately AOT_have \<open>x =\<^sub>E y\<close>
    using ord_eq_E_1 "\<rightarrow>E" by blast
  AOT_thus \<open>x = y\<close> using eq_E_simple_2[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem ord_eq_E2_1: \<open>(O!x & O!y) \<rightarrow> (x \<noteq> y \<equiv> [\<lambda>z z =\<^sub>E x] \<noteq> [\<lambda>z z =\<^sub>E y])\<close>
proof (rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I"; rule "\<equiv>\<^sub>d\<^sub>fI"[OF "=-infix"]; rule "raa-cor:2")
  AOT_assume 0: \<open>O!x & O!y\<close>
  AOT_assume \<open>x \<noteq> y\<close>
  AOT_hence 1: \<open>\<not>(x = y)\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF "=-infix"] by blast
  AOT_assume \<open>[\<lambda>z z =\<^sub>E x] = [\<lambda>z z =\<^sub>E y]\<close>
  moreover AOT_have \<open>[\<lambda>z z =\<^sub>E x]x\<close>
    apply (rule betaC_2_a)
      apply "cqt:2[lambda]"
     apply (fact "cqt:2[const_var]"[axiom_inst])
    using ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF 0[THEN "&E"(1)]].
  ultimately AOT_have \<open>[\<lambda>z z =\<^sub>E y]x\<close> using "rule=E" by fast
  AOT_hence \<open>x =\<^sub>E y\<close> using betaC_1_a by blast
  AOT_hence \<open>x = y\<close> by (metis eq_E_simple_2 "vdash-properties:6")
  AOT_thus \<open>x = y & \<not>(x = y)\<close> using 1 "&I" by blast
next
  AOT_assume \<open>[\<lambda>z z =\<^sub>E x] \<noteq> [\<lambda>z z =\<^sub>E y]\<close>
  AOT_hence 0: \<open>\<not>([\<lambda>z z =\<^sub>E x] = [\<lambda>z z =\<^sub>E y])\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF "=-infix"] by blast
  AOT_have \<open>[\<lambda>z z =\<^sub>E x]\<down>\<close> by "cqt:2[lambda]"
  AOT_hence \<open>[\<lambda>z z =\<^sub>E x] = [\<lambda>z z =\<^sub>E x]\<close>
    by (metis "rule=I:1")
  moreover AOT_assume \<open>x = y\<close>
  ultimately AOT_have \<open>[\<lambda>z z =\<^sub>E x] = [\<lambda>z z =\<^sub>E y]\<close>
    using "=E" by fast
  AOT_thus \<open>[\<lambda>z z =\<^sub>E x] = [\<lambda>z z =\<^sub>E y] & \<not>([\<lambda>z z =\<^sub>E x] = [\<lambda>z z =\<^sub>E y])\<close>
    using 0 "&I" by blast
qed

AOT_theorem ord_eq_E2_2: \<open>(O!x & O!y) \<rightarrow> (x \<noteq> y \<equiv> [\<lambda>z z = x] \<noteq> [\<lambda>z z = y])\<close>
proof (rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I"; rule "\<equiv>\<^sub>d\<^sub>fI"[OF "=-infix"]; rule "raa-cor:2")
  AOT_assume 0: \<open>O!x & O!y\<close>
  AOT_assume \<open>x \<noteq> y\<close>
  AOT_hence 1: \<open>\<not>(x = y)\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF "=-infix"] by blast
  AOT_assume \<open>[\<lambda>z z = x] = [\<lambda>z z = y]\<close>
  moreover AOT_have \<open>[\<lambda>z z = x]x\<close>
    apply (rule betaC_2_a)
    apply (fact ord_eq_E_eq_2[THEN "\<rightarrow>E", OF 0[THEN "&E"(1)]])
     apply (fact "cqt:2[const_var]"[axiom_inst])
    by (simp add: "id-eq:1")
  ultimately AOT_have \<open>[\<lambda>z z = y]x\<close> using "rule=E" by fast
  AOT_hence \<open>x = y\<close> using betaC_1_a by blast
  AOT_thus \<open>x = y & \<not>(x = y)\<close> using 1 "&I" by blast
next
  AOT_assume 0: \<open>O!x & O!y\<close>
  AOT_assume \<open>[\<lambda>z z = x] \<noteq> [\<lambda>z z = y]\<close>
  AOT_hence 1: \<open>\<not>([\<lambda>z z = x] = [\<lambda>z z = y])\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF "=-infix"] by blast
  AOT_have \<open>[\<lambda>z z = x]\<down>\<close> by (fact ord_eq_E_eq_2[THEN "\<rightarrow>E", OF 0[THEN "&E"(1)]])
  AOT_hence \<open>[\<lambda>z z = x] = [\<lambda>z z = x]\<close>
    by (metis "rule=I:1")
  moreover AOT_assume \<open>x = y\<close>
  ultimately AOT_have \<open>[\<lambda>z z = x] = [\<lambda>z z = y]\<close>
    using "=E" by fast
  AOT_thus \<open>[\<lambda>z z = x] = [\<lambda>z z = y] & \<not>([\<lambda>z z = x] = [\<lambda>z z = y])\<close>
    using 1 "&I" by blast
qed

AOT_theorem ordnecfail: \<open>O!x \<rightarrow> \<box>\<not>\<exists>F x[F]\<close>
  by (meson "RM:1" "deduction-theorem" nocoder oa_facts_1 "vdash-properties:10" "vdash-properties:1[2]")

AOT_theorem ab_obey_1: \<open>(A!x & A!y) \<rightarrow> (\<forall>F (x[F] \<equiv> y[F]) \<rightarrow> x = y)\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume 1: \<open>A!x & A!y\<close>
  AOT_assume \<open>\<forall>F (x[F] \<equiv> y[F])\<close>
  AOT_hence \<open>x[F] \<equiv> y[F]\<close> for F using "\<forall>E" by blast
  AOT_hence \<open>\<box>(x[F] \<equiv> y[F])\<close> for F by (metis en_eq_6_1 "\<equiv>E"(1))
  AOT_hence \<open>\<forall>F \<box>(x[F] \<equiv> y[F])\<close> by (rule GEN)
  AOT_hence \<open>\<box>\<forall>F (x[F] \<equiv> y[F])\<close> by (rule BF[THEN "\<rightarrow>E"])
  AOT_thus \<open>x = y\<close>
    using "\<equiv>\<^sub>d\<^sub>fI"[OF "identity:1", OF "\<or>I"(2)] 1 "&I" by blast
qed

(* TODO_PLM: precondition not needed *)
AOT_theorem ab_obey_2: \<open>(A!x & A!y) \<rightarrow> ((\<exists>F (x[F] & \<not>y[F]) \<or> \<exists>F (y[F] & \<not>x[F])) \<rightarrow> x \<noteq> y)\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I"; rule "\<equiv>\<^sub>d\<^sub>fI"[OF "=-infix"]; rule "raa-cor:2")
  AOT_assume 1: \<open>x = y\<close>
  AOT_assume \<open>\<exists>F (x[F] & \<not>y[F]) \<or> \<exists>F (y[F] & \<not>x[F])\<close>
  moreover {
    AOT_assume \<open>\<exists>F (x[F] & \<not>y[F])\<close>
    then AOT_obtain F where \<open>x[F] & \<not>y[F]\<close> using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>y[F]\<close> using calculation[THEN "&E"(1)] 1 "=E" by fast
    ultimately AOT_have \<open>p & \<not>p\<close> for p by (metis "Conjunction Simplification"(2) "modus-tollens:2" "raa-cor:3")
  }
  moreover {
    AOT_assume \<open>\<exists>F (y[F] & \<not>x[F])\<close>
    then AOT_obtain F where \<open>y[F] & \<not>x[F]\<close> using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>\<not>y[F]\<close> using calculation[THEN "&E"(2)] 1 "=E" by fast
    ultimately AOT_have \<open>p & \<not>p\<close> for p by (metis "Conjunction Simplification"(1) "modus-tollens:1" "raa-cor:3")
  }
  ultimately AOT_show \<open>p & \<not>p\<close> for p by (metis "\<or>E"(3) "raa-cor:1")
qed

AOT_theorem encoders_are_abstract: \<open>\<exists>F x[F] \<rightarrow> A!x\<close>
  by (meson "deduction-theorem" "\<equiv>E"(2) "modus-tollens:2" nocoder
            oa_contingent_3 "vdash-properties:1[2]")

AOT_theorem denote_eq_1: \<open>\<forall>H\<exists>x x[H]\<close>
  by (rule GEN; rule "existence:2[1]"[THEN "\<equiv>\<^sub>d\<^sub>fE"]; fact "cqt:2[const_var]"[axiom_inst])

AOT_theorem denote_eq_2: \<open>\<forall>G\<exists>x\<^sub>1...\<exists>x\<^sub>n x\<^sub>1...x\<^sub>n[H]\<close>
  by (rule GEN; rule "existence:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"]; fact "cqt:2[const_var]"[axiom_inst])

AOT_theorem denote_eq_2b: \<open>\<forall>G\<exists>x\<^sub>1\<exists>x\<^sub>2 x\<^sub>1x\<^sub>2[H]\<close>
  by (rule GEN; rule "existence:2[2]"[THEN "\<equiv>\<^sub>d\<^sub>fE"]; fact "cqt:2[const_var]"[axiom_inst])

AOT_theorem denote_eq_2c: \<open>\<forall>G\<exists>x\<^sub>1\<exists>x\<^sub>2\<exists>x\<^sub>3 x\<^sub>1x\<^sub>2x\<^sub>3[H]\<close>
  by (rule GEN; rule "existence:2[3]"[THEN "\<equiv>\<^sub>d\<^sub>fE"]; fact "cqt:2[const_var]"[axiom_inst])

AOT_theorem denote_eq_2d: \<open>\<forall>G\<exists>x\<^sub>1\<exists>x\<^sub>2\<exists>x\<^sub>3\<exists>x\<^sub>4 x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[H]\<close>
  by (rule GEN; rule "existence:2[4]"[THEN "\<equiv>\<^sub>d\<^sub>fE"]; fact "cqt:2[const_var]"[axiom_inst])

AOT_theorem denote_eq_3: \<open>\<exists>x x[\<Pi>] \<equiv> \<exists>H (H = \<Pi>)\<close>
  using "existence:2[1]" "free-thms:1" "\<equiv>E"(2) "\<equiv>E"(5) "Commutativity of \<equiv>" "\<equiv>Df" by blast

AOT_theorem denote_eq_4: \<open>(\<exists>x\<^sub>1...\<exists>x\<^sub>n x\<^sub>1...x\<^sub>n[\<Pi>]) \<equiv> \<exists>H (H = \<Pi>)\<close>
  using "existence:2" "free-thms:1" "\<equiv>E"(6) "\<equiv>Df" by blast

AOT_theorem denote_eq_4b: \<open>(\<exists>x\<^sub>1\<exists>x\<^sub>2 x\<^sub>1x\<^sub>2[\<Pi>]) \<equiv> \<exists>H (H = \<Pi>)\<close>
  using "existence:2[2]" "free-thms:1" "\<equiv>E"(6) "\<equiv>Df" by blast

AOT_theorem denote_eq_4c: \<open>(\<exists>x\<^sub>1\<exists>x\<^sub>2\<exists>x\<^sub>3 x\<^sub>1x\<^sub>2x\<^sub>3[\<Pi>]) \<equiv> \<exists>H (H = \<Pi>)\<close>
  using "existence:2[3]" "free-thms:1" "\<equiv>E"(6) "\<equiv>Df" by blast

AOT_theorem denote_eq_4d: \<open>(\<exists>x\<^sub>1\<exists>x\<^sub>2\<exists>x\<^sub>3\<exists>x\<^sub>4 x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[\<Pi>]) \<equiv> \<exists>H (H = \<Pi>)\<close>
  using "existence:2[4]" "free-thms:1" "\<equiv>E"(6) "\<equiv>Df" by blast

AOT_theorem A_objects_unique: \<open>\<exists>!x (A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
proof (rule "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<phi>{F})\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by blast
  AOT_have \<open>(A!\<beta> & \<forall>F (\<beta>[F] \<equiv> \<phi>{F})) \<rightarrow> \<beta> = a\<close> for \<beta>
  proof (rule "\<rightarrow>I")
    AOT_assume \<beta>_prop: \<open>[A!]\<beta> & \<forall>F (\<beta>[F] \<equiv> \<phi>{F})\<close>
    AOT_hence \<open>\<beta>[F] \<equiv> \<phi>{F}\<close> for F using "\<forall>E" "&E" by blast
    AOT_hence \<open>\<beta>[F] \<equiv> a[F]\<close> for F
      using a_prop[THEN "&E"(2)] "\<forall>E" "\<equiv>E"(2) "\<equiv>E"(5) "Commutativity of \<equiv>" by fast
    AOT_hence \<open>\<forall>F (\<beta>[F] \<equiv> a[F])\<close> by (rule GEN)
    AOT_thus \<open>\<beta> = a\<close>
      using ab_obey_1[THEN "\<rightarrow>E", OF "&I"[OF \<beta>_prop[THEN "&E"(1)], OF a_prop[THEN "&E"(1)]], THEN "\<rightarrow>E"] by blast
  qed
  AOT_hence \<open>\<forall>\<beta> ((A!\<beta> & \<forall>F (\<beta>[F] \<equiv> \<phi>{F})) \<rightarrow> \<beta> = a)\<close> by (rule GEN)
  AOT_thus \<open>\<exists>\<alpha> ([A!]\<alpha> & \<forall>F (\<alpha>[F] \<equiv> \<phi>{F}) & \<forall>\<beta> ([A!]\<beta> & \<forall>F (\<beta>[F] \<equiv> \<phi>{F}) \<rightarrow> \<beta> = \<alpha>)) \<close>
    using "\<exists>I" using a_prop "&I" by fast
qed

AOT_theorem obj_oth_1: \<open>\<exists>!x (A!x & \<forall>F (x[F] \<equiv> [F]y))\<close>
  using A_objects_unique by fast

AOT_theorem obj_oth_2: \<open>\<exists>!x (A!x & \<forall>F (x[F] \<equiv> [F]y & [F]z))\<close>
  using A_objects_unique by fast

AOT_theorem obj_oth_3: \<open>\<exists>!x (A!x & \<forall>F (x[F] \<equiv> [F]y \<or> [F]z))\<close>
  using A_objects_unique by fast

AOT_theorem obj_oth_4: \<open>\<exists>!x (A!x & \<forall>F (x[F] \<equiv> \<box>[F]y))\<close>
  using A_objects_unique by fast

AOT_theorem obj_oth_5: \<open>\<exists>!x (A!x & \<forall>F (x[F] \<equiv> F = G))\<close>
  using A_objects_unique by fast

AOT_theorem obj_oth_6: \<open>\<exists>!x (A!x & \<forall>F (x[F] \<equiv> \<box>\<forall>y([G]y \<rightarrow> [F]y)))\<close>
  using A_objects_unique by fast

AOT_theorem A_descriptions: \<open>\<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<down>\<close>
  by (rule A_Exists_2[THEN "\<equiv>E"(2)]; rule "RA[2]"; rule A_objects_unique)

AOT_act_theorem thm_can_terms2: \<open>y = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F})) \<rightarrow> (A!y & \<forall>F (y[F] \<equiv> \<phi>{F}))\<close>
  using "y-in:2" by blast

AOT_theorem can_ab2: \<open>y = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F})) \<rightarrow>  A!y\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>y = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
  AOT_hence \<open>\<^bold>\<A>(A!y & \<forall>F (y[F] \<equiv> \<phi>{F}))\<close>
    using "actual-desc:2"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<^bold>\<A>A!y\<close> by (metis "Act-Basic:2" "&E"(1) "\<equiv>E"(1))
  AOT_thus \<open>A!y\<close> by (metis "\<equiv>E"(2) oa_facts_8)
qed

AOT_act_theorem desc_encode: \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[G] \<equiv> \<phi>{G}\<close>
proof -
  AOT_have \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<down>\<close>
    by (simp add: A_descriptions)
  AOT_hence \<open>A!\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F})) & \<forall>F (\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[F] \<equiv> \<phi>{F})\<close>
    using "y-in:3"[THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[G] \<equiv> \<phi>{G}\<close>
    using "&E" "\<forall>E" by blast
qed

AOT_theorem desc_nec_encode: \<open>\<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[G] \<equiv> \<^bold>\<A>\<phi>{G}\<close>
proof -
  AOT_have 0: \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<down>\<close>
    by (simp add: A_descriptions)
  AOT_hence \<open>\<^bold>\<A>(A!\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F})) & \<forall>F (\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[F] \<equiv> \<phi>{F}))\<close>
    using "actual-desc:4"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<^bold>\<A>\<forall>F (\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[F] \<equiv> \<phi>{F})\<close>
    using "Act-Basic:2" "&E"(2) "\<equiv>E"(1) by blast
  AOT_hence \<open>\<forall>F \<^bold>\<A>(\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[F] \<equiv> \<phi>{F})\<close>
    using "\<equiv>E"(1) "logic-actual-nec:3" "vdash-properties:1[2]" by blast
  AOT_hence \<open>\<^bold>\<A>(\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[G] \<equiv> \<phi>{G})\<close>
    using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[G] \<equiv> \<^bold>\<A>\<phi>{G}\<close>
    using "Act-Basic:5" "\<equiv>E"(1) by blast
  AOT_thus \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[G] \<equiv> \<^bold>\<A>\<phi>{G}\<close>
    using en_eq_10_1[unvarify x\<^sub>1, OF 0] "\<equiv>E"(6) by blast
qed

AOT_theorem Box_desc_encode_1: \<open>\<box>\<phi>{G} \<rightarrow> \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{G}))[G]\<close>
  by (rule "\<rightarrow>I"; rule desc_nec_encode[THEN "\<equiv>E"(2)])
     (meson "nec-imp-act" "vdash-properties:10")

AOT_theorem Box_desc_encode_2: \<open>\<box>\<phi>{G} \<rightarrow> \<box>(\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{G}))[G] \<equiv> \<phi>{G})\<close>
proof(rule CP)
  AOT_assume \<open>\<box>\<phi>{G}\<close>
  AOT_hence \<open>\<box>\<box>\<phi>{G}\<close> by (metis "S5Basic:6" "\<equiv>E"(1))
  moreover AOT_have \<open>\<box>\<box>\<phi>{G} \<rightarrow> \<box>(\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{G}))[G] \<equiv> \<phi>{G})\<close>
  proof (rule RM; rule "\<rightarrow>I")
    AOT_modally_strict {
      AOT_assume 1: \<open>\<box>\<phi>{G}\<close>
      AOT_hence \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{G}))[G]\<close> using Box_desc_encode_1 "\<rightarrow>E" by blast
      moreover AOT_have \<open>\<phi>{G}\<close> using 1 by (meson "qml:2" "vdash-properties:10" "vdash-properties:1[2]")
      ultimately AOT_show \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{G}))[G] \<equiv> \<phi>{G}\<close>
        using "deduction-theorem" "\<equiv>I" by simp
    }
  qed
  ultimately AOT_show \<open>\<box>(\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{G}))[G] \<equiv> \<phi>{G})\<close> using "\<rightarrow>E" by blast
qed

definition rigid_condition where \<open>rigid_condition \<phi> \<equiv> \<forall>v . [v \<Turnstile> \<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>})]\<close>
syntax rigid_condition :: \<open>id_position \<Rightarrow> AOT_prop\<close> ("RIGID'_CONDITION'(_')")

AOT_theorem rigid_conditionE: assumes \<open>RIGID_CONDITION(\<phi>)\<close>
  shows \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>})\<close>
  using assms[unfolded rigid_condition_def] by auto

AOT_theorem rigid_conditionI:
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>})\<close>
  shows \<open>RIGID_CONDITION(\<phi>)\<close>
  using assms rigid_condition_def by auto

AOT_theorem box_phi_a_1: assumes \<open>RIGID_CONDITION(\<phi>)\<close>
  shows \<open>(A!x  & \<forall>F (x[F] \<equiv> \<phi>{F})) \<rightarrow> \<box>(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
proof (rule "\<rightarrow>I")
  AOT_assume a: \<open>A!x & \<forall>F (x[F] \<equiv> \<phi>{F})\<close>
  AOT_hence b: \<open>\<box>A!x\<close> by (metis "Conjunction Simplification"(1) oa_facts_2 "vdash-properties:10")
  AOT_have \<open>x[F] \<equiv> \<phi>{F}\<close> for F using a[THEN "&E"(2)] "\<forall>E" by blast
  moreover AOT_have \<open>\<box>(x[F] \<rightarrow> \<box>x[F])\<close> for F by (meson pre_en_eq_1_1 RN)
  moreover AOT_have \<open>\<box>(\<phi>{F} \<rightarrow> \<box>\<phi>{F})\<close> for F using RN rigid_conditionE[OF assms] "\<forall>E" by blast
  ultimately AOT_have \<open>\<box>(x[F] \<equiv> \<phi>{F})\<close> for F
    by (metis "&I" sc_eq_box_box_5 "vdash-properties:6")
  AOT_hence \<open>\<forall>F \<box>(x[F] \<equiv> \<phi>{F})\<close> by (rule GEN)
  AOT_hence \<open>\<box>\<forall>F (x[F] \<equiv> \<phi>{F})\<close> by (rule BF[THEN "\<rightarrow>E"])
  AOT_thus \<open>\<box>([A!]x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
    using b "KBasic:3" "\<equiv>S"(1) "\<equiv>E"(2) by blast
qed

AOT_theorem box_phi_a_2: assumes \<open>RIGID_CONDITION(\<phi>)\<close>
  shows \<open>y = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F})) \<rightarrow> (A!y & \<forall>F (y[F] \<equiv> \<phi>{F}))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>y = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
  AOT_hence \<open>\<^bold>\<A>(A!y & \<forall>F (y[F] \<equiv> \<phi>{F}))\<close> using "actual-desc:2"[THEN "\<rightarrow>E"] by fast
  AOT_hence abs: \<open>\<^bold>\<A>A!y\<close> and \<open>\<^bold>\<A>\<forall>F (y[F] \<equiv> \<phi>{F})\<close>
    using "Act-Basic:2" "&E" "\<equiv>E"(1) by blast+
  AOT_hence \<open>\<forall>F \<^bold>\<A>(y[F] \<equiv> \<phi>{F})\<close> by (metis "\<equiv>E"(1) "logic-actual-nec:3" "vdash-properties:1[2]")
  AOT_hence \<open>\<^bold>\<A>(y[F] \<equiv> \<phi>{F})\<close> for F using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>y[F] \<equiv> \<^bold>\<A>\<phi>{F}\<close> for F by (metis "Act-Basic:5" "\<equiv>E"(1)) 
  AOT_hence \<open>y[F] \<equiv> \<phi>{F}\<close> for F
    using sc_eq_fur_2[THEN "\<rightarrow>E", OF rigid_conditionE[OF assms, THEN "\<forall>E"(2)[where \<beta>=F], THEN RN]]
    by (metis en_eq_10_1 "\<equiv>E"(6))
  AOT_hence \<open>\<forall>F (y[F] \<equiv> \<phi>{F})\<close> by (rule GEN)
  AOT_thus \<open>[A!]y & \<forall>F (y[F] \<equiv> \<phi>{F})\<close> using abs "&I" "\<equiv>E"(2) oa_facts_8 by blast
qed

AOT_theorem box_phi_a_3: assumes \<open>RIGID_CONDITION(\<phi>)\<close>
  shows \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))[G] \<equiv> \<phi>{G}\<close>
  using desc_nec_encode 
    sc_eq_fur_2[THEN "\<rightarrow>E", OF rigid_conditionE[OF assms, THEN "\<forall>E"(2)[where \<beta>=G], THEN RN]]
    "\<equiv>E"(5) by blast

AOT_define Null :: \<open>\<tau> \<Rightarrow> \<phi>\<close> ("Null'(_')") 
  df_null_uni_1: \<open>Null(x) \<equiv>\<^sub>d\<^sub>f A!x & \<not>\<exists>F x[F]\<close>

AOT_define Universal :: \<open>\<tau> \<Rightarrow> \<phi>\<close> ("Universal'(_')")
  df_null_uni_2: \<open>Universal(x) \<equiv>\<^sub>d\<^sub>f A!x & \<forall>F x[F]\<close>

AOT_theorem null_uni_uniq_1: \<open>\<exists>!x Null(x)\<close>
proof (rule "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<not>(F = F))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_have a_null: \<open>\<not>a[F]\<close> for F
  proof (rule "raa-cor:2")
    AOT_assume \<open>a[F]\<close>
    AOT_hence \<open>\<not>(F = F)\<close> using a_prop[THEN "&E"(2)] "\<forall>E" "\<equiv>E" by blast
    AOT_hence \<open>F = F & \<not>(F = F)\<close> by (metis "id-eq:1" "raa-cor:3")
    AOT_thus \<open>p & \<not>p\<close> for p  by (metis "raa-cor:1")
  qed
  AOT_have \<open>Null(a) & \<forall>\<beta> (Null(\<beta>) \<rightarrow> \<beta> = a)\<close>
  proof (rule "&I")
    AOT_have \<open>\<not>\<exists>F a[F]\<close> using a_null by (metis "instantiation" "reductio-aa:1")
    AOT_thus \<open>Null(a)\<close>
      using df_null_uni_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] a_prop[THEN "&E"(1)] "&I" by metis
  next
    AOT_show \<open>\<forall>\<beta> (Null(\<beta>) \<rightarrow> \<beta> = a)\<close>
    proof (rule GEN; rule "\<rightarrow>I")
      fix \<beta>
      AOT_assume a: \<open>Null(\<beta>)\<close>
      AOT_hence \<open>\<not>\<exists>F \<beta>[F]\<close>
        using df_null_uni_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
      AOT_hence \<beta>_null: \<open>\<not>\<beta>[F]\<close> for F by (metis "existential:2[const_var]" "reductio-aa:1")
      AOT_have \<open>\<forall>F (\<beta>[F] \<equiv> a[F])\<close>
        apply (rule GEN; rule "\<equiv>I"; rule CP)
        using "raa-cor:3" \<beta>_null a_null by blast+
      moreover AOT_have \<open>A!\<beta>\<close> using a df_null_uni_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
      ultimately AOT_show \<open>\<beta> = a\<close>
        using a_prop[THEN "&E"(1)] ab_obey_1[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I" by blast
    qed
  qed
  AOT_thus \<open>\<exists>\<alpha> (Null(\<alpha>) & \<forall>\<beta> (Null(\<beta>) \<rightarrow> \<beta> = \<alpha>))\<close> using "\<exists>I"(2) by fast
qed

AOT_theorem null_uni_uniq_2: \<open>\<exists>!x Universal(x)\<close>
proof (rule "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> F = F)\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_hence aF: \<open>a[F]\<close> for F using "&E" "\<forall>E" "\<equiv>E" "id-eq:1" by fast
  AOT_hence \<open>Universal(a)\<close>
    using df_null_uni_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" a_prop[THEN "&E"(1)] GEN by blast
  moreover AOT_have \<open>\<forall>\<beta> (Universal(\<beta>) \<rightarrow> \<beta> = a)\<close>
  proof (rule GEN; rule "\<rightarrow>I")
    fix \<beta>
    AOT_assume \<open>Universal(\<beta>)\<close>
    AOT_hence abs_\<beta>: \<open>A!\<beta>\<close> and \<open>\<beta>[F]\<close> for F using df_null_uni_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<forall>E" by blast+
    AOT_hence \<open>\<beta>[F] \<equiv> a[F]\<close> for F using aF by (metis "deduction-theorem" "\<equiv>I")
    AOT_hence \<open>\<forall>F (\<beta>[F] \<equiv> a[F])\<close> by (rule GEN)
    AOT_thus \<open>\<beta> = a\<close>
      using a_prop[THEN "&E"(1)] ab_obey_1[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I" abs_\<beta> by blast
  qed
  ultimately AOT_show \<open>\<exists>\<alpha> (Universal(\<alpha>) & \<forall>\<beta> (Universal(\<beta>) \<rightarrow> \<beta> = \<alpha>))\<close>
    using "&I" "\<exists>I" by fast
qed

AOT_theorem null_uni_uniq_3: \<open>\<^bold>\<iota>x Null(x)\<down>\<close>
  using A_Exists_2 "RA[2]" "\<equiv>E"(2) null_uni_uniq_1 by blast

AOT_theorem null_uni_uniq_4: \<open>\<^bold>\<iota>x Universal(x)\<down>\<close>
  using A_Exists_2 "RA[2]" "\<equiv>E"(2) null_uni_uniq_2 by blast

AOT_define Null_object :: \<open>\<kappa>\<^sub>s\<close> (\<open>a\<^sub>\<emptyset>\<close>)
  df_null_uni_terms_1: \<open>a\<^sub>\<emptyset> =\<^sub>d\<^sub>f \<^bold>\<iota>x Null(x)\<close>

AOT_define Universal_object :: \<open>\<kappa>\<^sub>s\<close> (\<open>a\<^sub>V\<close>)
  df_null_uni_terms_2: \<open>a\<^sub>V =\<^sub>d\<^sub>f \<^bold>\<iota>x Universal(x)\<close>

AOT_theorem null_uni_facts_1: \<open>Null(x) \<rightarrow> \<box>Null(x)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>Null(x)\<close>
  AOT_hence x_abs: \<open>A!x\<close> and x_null: \<open>\<not>\<exists>F x[F]\<close>
    using df_null_uni_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>\<not>x[F]\<close> for F using x_null
    using "existential:2[const_var]" "reductio-aa:1"
    by metis
  AOT_hence \<open>\<box>\<not>x[F]\<close> for F by (metis en_eq_7_1 "\<equiv>E"(1))
  AOT_hence \<open>\<forall>F \<box>\<not>x[F]\<close> by (rule GEN)
  AOT_hence \<open>\<box>\<forall>F \<not>x[F]\<close> by (rule BF[THEN "\<rightarrow>E"])
  moreover AOT_have \<open>\<box>\<forall>F \<not>x[F] \<rightarrow> \<box>\<not>\<exists>F x[F]\<close>
    apply (rule RM)
    by (metis (full_types) "instantiation" "cqt:2[const_var]" "deduction-theorem"
                           "reductio-aa:1" "rule-ui:1" "vdash-properties:1[2]")
  ultimately AOT_have \<open>\<box>\<not>\<exists>F x[F]\<close>
    by (metis "\<rightarrow>E")
  moreover AOT_have \<open>\<box>A!x\<close> using x_abs
    using oa_facts_2 "vdash-properties:10" by blast
  ultimately AOT_have r: \<open>\<box>(A!x & \<not>\<exists>F x[F])\<close>
    by (metis "KBasic:3" "&I" "\<equiv>E"(3) "raa-cor:3")
  AOT_show \<open>\<box>Null(x)\<close>
    by (AOT_subst "\<guillemotleft>Null(x)\<guillemotright>" "\<guillemotleft>A!x & \<not>\<exists>F x[F]\<guillemotright>")
       (auto simp: df_null_uni_1 "\<equiv>Df" r)
qed  

AOT_theorem null_uni_facts_2: \<open>Universal(x) \<rightarrow> \<box>Universal(x)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>Universal(x)\<close>
  AOT_hence x_abs: \<open>A!x\<close> and x_univ: \<open>\<forall>F x[F]\<close>
    using df_null_uni_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>x[F]\<close> for F using x_univ "\<forall>E" by blast
  AOT_hence \<open>\<box>x[F]\<close> for F by (metis en_eq_2_1 "\<equiv>E"(1))
  AOT_hence \<open>\<forall>F \<box>x[F]\<close> by (rule GEN)
  AOT_hence \<open>\<box>\<forall>F x[F]\<close> by (rule BF[THEN "\<rightarrow>E"])
  moreover AOT_have \<open>\<box>A!x\<close> using x_abs
    using oa_facts_2 "vdash-properties:10" by blast
  ultimately AOT_have r: \<open>\<box>(A!x & \<forall>F x[F])\<close>
    by (metis "KBasic:3" "&I" "\<equiv>E"(3) "raa-cor:3")
  AOT_show \<open>\<box>Universal(x)\<close>
    by (AOT_subst "\<guillemotleft>Universal(x)\<guillemotright>" "\<guillemotleft>A!x & \<forall>F x[F]\<guillemotright>")
       (auto simp add: df_null_uni_2 "\<equiv>Df" r)
qed

AOT_theorem null_uni_facts_3: \<open>Null(a\<^sub>\<emptyset>)\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_1])
   apply (simp add: null_uni_uniq_3)
  using "actual-desc:4"[THEN "\<rightarrow>E", OF null_uni_uniq_3]
    sc_eq_fur_2[THEN "\<rightarrow>E", OF null_uni_facts_1[unvarify x, THEN RN, OF null_uni_uniq_3], THEN "\<equiv>E"(1)]
  by blast

AOT_theorem null_uni_facts_4: \<open>Universal(a\<^sub>V)\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_2])
   apply (simp add: null_uni_uniq_4)
  using "actual-desc:4"[THEN "\<rightarrow>E", OF null_uni_uniq_4]
    sc_eq_fur_2[THEN "\<rightarrow>E", OF null_uni_facts_2[unvarify x, THEN RN, OF null_uni_uniq_4], THEN "\<equiv>E"(1)]
  by blast

AOT_theorem null_uni_facts_5: \<open>a\<^sub>\<emptyset> \<noteq> a\<^sub>V\<close>
proof (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_1, OF null_uni_uniq_3];
    rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_2, OF null_uni_uniq_4];
    rule "\<equiv>\<^sub>d\<^sub>fI"[OF "=-infix"];
    rule "raa-cor:2")
  AOT_obtain x where nullx: \<open>Null(x)\<close>
    by (metis "instantiation" df_null_uni_terms_1 "existential:1" null_uni_facts_3
              null_uni_uniq_3 "rule-id-def:2:b[zero]")
  AOT_hence act_null: \<open>\<^bold>\<A>Null(x)\<close> by (metis "nec-imp-act" null_uni_facts_1 "vdash-properties:10")
  AOT_assume \<open>\<^bold>\<iota>x Null(x) = \<^bold>\<iota>x Universal(x)\<close>
  AOT_hence \<open>\<^bold>\<A>\<forall>x(Null(x) \<equiv> Universal(x))\<close>
    using "actual-desc:5"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<forall>x \<^bold>\<A>(Null(x) \<equiv> Universal(x))\<close>
    by (metis "\<equiv>E"(1) "logic-actual-nec:3" "vdash-properties:1[2]")
  AOT_hence \<open>\<^bold>\<A>Null(x) \<equiv> \<^bold>\<A>Universal(x)\<close>
    using "Act-Basic:5" "\<equiv>E"(1) "rule-ui:3" by blast
  AOT_hence \<open>\<^bold>\<A>Universal(x)\<close> using act_null "\<equiv>E" by blast
  AOT_hence \<open>Universal(x)\<close> by (metis RN "\<equiv>E"(1) null_uni_facts_2 sc_eq_fur_2 "vdash-properties:10")
  AOT_hence \<open>\<forall>F x[F]\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF df_null_uni_2] "&E" by metis
  moreover AOT_have \<open>\<not>\<exists>F x[F]\<close> using nullx "\<equiv>\<^sub>d\<^sub>fE"[OF df_null_uni_1] "&E" by metis
  ultimately AOT_show \<open>p & \<not>p\<close> for p by (metis "cqt-further:1" "raa-cor:3" "vdash-properties:10")
qed

AOT_theorem null_uni_facts_6: \<open>a\<^sub>\<emptyset> = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> F \<noteq> F))\<close>
proof (rule ab_obey_1[unvarify x y, THEN "\<rightarrow>E", THEN "\<rightarrow>E"])
  AOT_show \<open>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))\<down>\<close>
    by (simp add: A_descriptions)
next
  AOT_show \<open>a\<^sub>\<emptyset>\<down>\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_1, OF null_uni_uniq_3])
       (simp add: null_uni_uniq_3)
next
  AOT_have \<open>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))\<down>\<close>
    by (simp add: A_descriptions)
  AOT_hence 1: \<open>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F)) = \<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))\<close>
    using "rule=I:1" by blast
  AOT_show \<open>[A!]a\<^sub>\<emptyset> & [A!]\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_1, OF null_uni_uniq_3]; rule "&I")
    apply (meson "\<equiv>\<^sub>d\<^sub>fE" "Conjunction Simplification"(1) df_null_uni_1 df_null_uni_terms_1 null_uni_facts_3 null_uni_uniq_3 "rule-id-def:2:a[zero]" "vdash-properties:10")
    using can_ab2[unvarify y, OF A_descriptions, THEN "\<rightarrow>E", OF 1].
next
  AOT_show \<open>\<forall>F (a\<^sub>\<emptyset>[F] \<equiv> \<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))[F])\<close>
  proof (rule GEN)
    fix F
    AOT_have \<open>\<not>a\<^sub>\<emptyset>[F]\<close>
      by (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_1, OF null_uni_uniq_3])
         (metis (no_types, lifting) "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "\<or>I"(2) "\<or>E"(3)
                df_null_uni_1 df_null_uni_terms_1 "existential:2[const_var]" null_uni_facts_3
                "raa-cor:2" "rule-id-def:2:a[zero]" "russell-axiom[enc,1].\<psi>_denotes_asm")
    moreover AOT_have \<open>\<not>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))[F]\<close>
    proof(rule "raa-cor:2")
      AOT_assume 0: \<open>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))[F]\<close>
      AOT_hence \<open>\<^bold>\<A>(F \<noteq> F)\<close> using desc_nec_encode[THEN "\<equiv>E"(1), OF 0] by blast
      moreover AOT_have \<open>\<not>\<^bold>\<A>(F \<noteq> F)\<close>
        using "\<equiv>\<^sub>d\<^sub>fE" id_act_2 "id-eq:1" "\<equiv>E"(2) "=-infix" "raa-cor:3" by blast
      ultimately AOT_show \<open>\<^bold>\<A>(F \<noteq> F) & \<not>\<^bold>\<A>(F \<noteq> F)\<close> by (rule "&I")
    qed
    ultimately AOT_show \<open>a\<^sub>\<emptyset>[F] \<equiv> \<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))[F]\<close>
      using "deduction-theorem" "\<equiv>I" "raa-cor:4" by blast
  qed
qed

AOT_theorem null_uni_facts_7: \<open>a\<^sub>V = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> F = F))\<close>
proof (rule ab_obey_1[unvarify x y, THEN "\<rightarrow>E", THEN "\<rightarrow>E"])
  AOT_show \<open>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F = F))\<down>\<close>
    by (simp add: A_descriptions)
next
  AOT_show \<open>a\<^sub>V\<down>\<close>
    by (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_2, OF null_uni_uniq_4])
       (simp add: null_uni_uniq_4)
next
  AOT_have \<open>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F = F))\<down>\<close>
    by (simp add: A_descriptions)
  AOT_hence 1: \<open>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F = F)) = \<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F = F))\<close>
    using "rule=I:1" by blast
  AOT_show \<open>[A!]a\<^sub>V & [A!]\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F = F))\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_2, OF null_uni_uniq_4]; rule "&I")
    apply (meson "\<equiv>\<^sub>d\<^sub>fE" "Conjunction Simplification"(1) df_null_uni_2 df_null_uni_terms_2 null_uni_facts_4 null_uni_uniq_4 "rule-id-def:2:a[zero]" "vdash-properties:10")
    using can_ab2[unvarify y, OF A_descriptions, THEN "\<rightarrow>E", OF 1].
next
  AOT_show \<open>\<forall>F (a\<^sub>V[F] \<equiv> \<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F = F))[F])\<close>
  proof (rule GEN)
    fix F
    AOT_have \<open>a\<^sub>V[F]\<close>
      apply (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_2, OF null_uni_uniq_4])
      using "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) df_null_uni_2 df_null_uni_terms_2 null_uni_facts_4 null_uni_uniq_4 "rule-id-def:2:a[zero]" "rule-ui:3" by blast
    moreover AOT_have \<open>\<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F = F))[F]\<close>
      using "RA[2]" desc_nec_encode "id-eq:1" "\<equiv>E"(2) by fastforce
    ultimately AOT_show \<open>a\<^sub>V[F] \<equiv> \<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> F = F))[F]\<close>
      using "deduction-theorem" "\<equiv>I" by simp
  qed
qed

AOT_theorem aclassical_1: \<open>\<forall>R\<exists>x\<exists>y(A!x & A!y & x \<noteq> y & [\<lambda>z [R]zx] = [\<lambda>z [R]zy])\<close>
proof(rule GEN)
  fix R
  AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<exists>y(A!y & F = [\<lambda>z [R]zy] & \<not>y[F]))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_have a_enc: \<open>a[\<lambda>z [R]za]\<close>
  proof (rule "raa-cor:1")
    AOT_assume 0: \<open>\<not>a[\<lambda>z [R]za]\<close>
    AOT_hence \<open>\<not>\<exists>y(A!y & [\<lambda>z [R]za] = [\<lambda>z [R]zy] & \<not>y[\<lambda>z [R]za])\<close>
      by (rule a_prop[THEN "&E"(2), THEN "\<forall>E"(1)[where \<tau>="\<guillemotleft>[\<lambda>z [R]za]\<guillemotright>"],
                THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1), rotated])
         "cqt:2[lambda]"
    AOT_hence \<open>\<forall>y \<not>(A!y & [\<lambda>z [R]za] = [\<lambda>z [R]zy] & \<not>y[\<lambda>z [R]za])\<close>
      using "cqt-further:4" "vdash-properties:10" by blast
    AOT_hence \<open>\<not>(A!a & [\<lambda>z [R]za] = [\<lambda>z [R]za] & \<not>a[\<lambda>z [R]za])\<close> using "\<forall>E" by blast
    AOT_hence \<open>(A!a & [\<lambda>z [R]za] = [\<lambda>z [R]za]) \<rightarrow> a[\<lambda>z [R]za]\<close>
      by (metis "&I" "deduction-theorem" "raa-cor:3")
    moreover AOT_have \<open>[\<lambda>z [R]za] = [\<lambda>z [R]za]\<close>
      by (rule "=I") "cqt:2[lambda]"
    ultimately AOT_have \<open>a[\<lambda>z [R]za]\<close> using a_prop[THEN "&E"(1)] "\<rightarrow>E" "&I" by blast
    AOT_thus \<open>a[\<lambda>z [R]za] & \<not>a[\<lambda>z [R]za]\<close>
      using 0 "&I" by blast
  qed
  AOT_hence \<open>\<exists>y(A!y & [\<lambda>z [R]za] = [\<lambda>z [R]zy] & \<not>y[\<lambda>z [R]za])\<close>
    by (rule a_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(1), rotated]) "cqt:2[lambda]"
  then AOT_obtain b where b_prop: \<open>A!b & [\<lambda>z [R]za] = [\<lambda>z [R]zb] & \<not>b[\<lambda>z [R]za]\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>a \<noteq> b\<close>
    apply (rule "\<equiv>\<^sub>d\<^sub>fI"[OF "=-infix"])
    using a_enc b_prop[THEN "&E"(2)]
    using "\<not>\<not>I" "rule=E" id_sym "\<equiv>E"(4) "oth-class-taut:3:a" "raa-cor:3" "reductio-aa:1" by fast
  AOT_hence \<open>A!a & A!b & a \<noteq> b & [\<lambda>z [R]za] = [\<lambda>z [R]zb]\<close>
    using b_prop "&E" a_prop "&I" by meson
  AOT_hence \<open>\<exists>y (A!a & A!y & a \<noteq> y & [\<lambda>z [R]za] = [\<lambda>z [R]zy])\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>x\<exists>y (A!x & A!y & x \<noteq> y & [\<lambda>z [R]zx] = [\<lambda>z [R]zy])\<close> by (rule "\<exists>I")
qed

AOT_theorem aclassical_2: \<open>\<forall>R\<exists>x\<exists>y(A!x & A!y & x \<noteq> y & [\<lambda>z [R]xz] = [\<lambda>z [R]yz])\<close>
proof(rule GEN)
  fix R
  AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<exists>y(A!y & F = [\<lambda>z [R]yz] & \<not>y[F]))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_have a_enc: \<open>a[\<lambda>z [R]az]\<close>
  proof (rule "raa-cor:1")
    AOT_assume 0: \<open>\<not>a[\<lambda>z [R]az]\<close>
    AOT_hence \<open>\<not>\<exists>y(A!y & [\<lambda>z [R]az] = [\<lambda>z [R]yz] & \<not>y[\<lambda>z [R]az])\<close>
      by (rule a_prop[THEN "&E"(2), THEN "\<forall>E"(1)[where \<tau>="\<guillemotleft>[\<lambda>z [R]az]\<guillemotright>"],
                THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1), rotated])
         "cqt:2[lambda]"
    AOT_hence \<open>\<forall>y \<not>(A!y & [\<lambda>z [R]az] = [\<lambda>z [R]yz] & \<not>y[\<lambda>z [R]az])\<close>
      using "cqt-further:4" "vdash-properties:10" by blast
    AOT_hence \<open>\<not>(A!a & [\<lambda>z [R]az] = [\<lambda>z [R]az] & \<not>a[\<lambda>z [R]az])\<close> using "\<forall>E" by blast
    AOT_hence \<open>(A!a & [\<lambda>z [R]az] = [\<lambda>z [R]az]) \<rightarrow> a[\<lambda>z [R]az]\<close>
      by (metis "&I" "deduction-theorem" "raa-cor:3")
    moreover AOT_have \<open>[\<lambda>z [R]az] = [\<lambda>z [R]az]\<close>
      by (rule "=I") "cqt:2[lambda]"
    ultimately AOT_have \<open>a[\<lambda>z [R]az]\<close> using a_prop[THEN "&E"(1)] "\<rightarrow>E" "&I" by blast
    AOT_thus \<open>a[\<lambda>z [R]az] & \<not>a[\<lambda>z [R]az]\<close>
      using 0 "&I" by blast
  qed
  AOT_hence \<open>\<exists>y(A!y & [\<lambda>z [R]az] = [\<lambda>z [R]yz] & \<not>y[\<lambda>z [R]az])\<close>
    by (rule a_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(1), rotated]) "cqt:2[lambda]"
  then AOT_obtain b where b_prop: \<open>A!b & [\<lambda>z [R]az] = [\<lambda>z [R]bz] & \<not>b[\<lambda>z [R]az]\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>a \<noteq> b\<close>
    apply (rule "\<equiv>\<^sub>d\<^sub>fI"[OF "=-infix"])
    using a_enc b_prop[THEN "&E"(2)]
    using "\<not>\<not>I" "rule=E" id_sym "\<equiv>E"(4) "oth-class-taut:3:a" "raa-cor:3" "reductio-aa:1" by fast
  AOT_hence \<open>A!a & A!b & a \<noteq> b & [\<lambda>z [R]az] = [\<lambda>z [R]bz]\<close>
    using b_prop "&E" a_prop "&I" by meson
  AOT_hence \<open>\<exists>y (A!a & A!y & a \<noteq> y & [\<lambda>z [R]az] = [\<lambda>z [R]yz])\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>x\<exists>y (A!x & A!y & x \<noteq> y & [\<lambda>z [R]xz] = [\<lambda>z [R]yz])\<close> by (rule "\<exists>I")
qed

AOT_theorem aclassical_3: \<open>\<forall>F\<exists>x\<exists>y(A!x & A!y & x \<noteq> y & [\<lambda> [F]x] = [\<lambda> [F]y])\<close>
proof(rule GEN)
  fix R
  AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<exists>y(A!y & F = [\<lambda>z [R]y] & \<not>y[F]))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_have \<open>[\<lambda>z [R]a]\<down>\<close> by "cqt:2[lambda]"
  (* TODO: S should no longer be necessary *)
  then AOT_obtain S where S_def: \<open>S = [\<lambda>z [R]a]\<close>
    by (metis "instantiation" "rule=I:1" "existential:1" id_sym)
  AOT_have a_enc: \<open>a[S]\<close>
  proof (rule "raa-cor:1")
    AOT_assume 0: \<open>\<not>a[S]\<close>
    AOT_hence \<open>\<not>\<exists>y(A!y & S = [\<lambda>z [R]y] & \<not>y[S])\<close>
      by (rule a_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=S],
                THEN "oth-class-taut:4:b"[THEN "\<equiv>E"(1)], THEN "\<equiv>E"(1), rotated]) 
    AOT_hence \<open>\<forall>y \<not>(A!y & S = [\<lambda>z [R]y] & \<not>y[S])\<close>
      using "cqt-further:4" "vdash-properties:10" by blast
    AOT_hence \<open>\<not>(A!a & S = [\<lambda>z [R]a] & \<not>a[S])\<close> using "\<forall>E" by blast
    AOT_hence \<open>(A!a & S = [\<lambda>z [R]a]) \<rightarrow> a[S]\<close>
      by (metis "&I" "deduction-theorem" "raa-cor:3")
    moreover AOT_have \<open>S = [\<lambda>z [R]a]\<close> using S_def .
    ultimately AOT_have \<open>a[S]\<close> using a_prop[THEN "&E"(1)] "\<rightarrow>E" "&I" by blast
    AOT_thus \<open>a[\<lambda>z [R]a] & \<not>a[\<lambda>z [R]a]\<close>  by (metis "0" "raa-cor:3") 
  qed
  AOT_hence \<open>\<exists>y(A!y & S = [\<lambda>z [R]y] & \<not>y[S])\<close>
    by (rule a_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1), rotated])
  then AOT_obtain b where b_prop: \<open>A!b & S = [\<lambda>z [R]b] & \<not>b[S]\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have 1: \<open>a \<noteq> b\<close>
    apply (rule "\<equiv>\<^sub>d\<^sub>fI"[OF "=-infix"])
    using a_enc b_prop[THEN "&E"(2)]
    using "\<not>\<not>I" "rule=E" id_sym "\<equiv>E"(4) "oth-class-taut:3:a" "raa-cor:3" "reductio-aa:1" by fast
  AOT_have a: \<open>[\<lambda> [R]a] = ([R]a)\<close>
    apply (rule "lambda-predicates:3[zero]"[axiom_inst, unvarify p])
    by (meson "log-prop-prop:2")
  AOT_have b: \<open>[\<lambda> [R]b] = ([R]b)\<close>
    apply (rule "lambda-predicates:3[zero]"[axiom_inst, unvarify p])
    by (meson "log-prop-prop:2")
  AOT_have \<open>[\<lambda> [R]a] = [\<lambda> [R]b]\<close>
    apply (rule "rule=E"[rotated, OF a[THEN id_sym]])
    apply (rule "rule=E"[rotated, OF b[THEN id_sym]])
    apply (rule "identity:4"[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I", rotated])
     apply (rule "rule=E"[rotated, OF S_def])
    using b_prop "&E" apply blast
    apply (safe intro!: "&I")
    by (simp add: "log-prop-prop:2")+
  AOT_hence \<open>A!a & A!b & a \<noteq> b & [\<lambda> [R]a] = [\<lambda> [R]b]\<close>
    using 1 a_prop[THEN "&E"(1)] b_prop[THEN "&E"(1), THEN "&E"(1)] "&I" by auto
  AOT_hence \<open>\<exists>y (A!a & A!y & a \<noteq> y & [\<lambda> [R]a] = [\<lambda> [R]y])\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>x\<exists>y (A!x & A!y & x \<noteq> y & [\<lambda> [R]x] = [\<lambda> [R]y])\<close> by (rule "\<exists>I")
qed

AOT_theorem aclassical2: \<open>\<exists>x\<exists>y (A!x & A!y & x \<noteq> y & \<forall>F ([F]x \<equiv> [F]y))\<close>
proof -
  AOT_have \<open>\<exists>x \<exists>y ([A!]x & [A!]y & x \<noteq> y &
               [\<lambda>z [\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]zx] = [\<lambda>z [\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]zy])\<close>
    by (rule aclassical_1[THEN "\<forall>E"(1)[where \<tau>="\<guillemotleft>[\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]\<guillemotright>"]])
       "cqt:2[lambda]"
  then AOT_obtain x where \<open>\<exists>y ([A!]x & [A!]y & x \<noteq> y &
               [\<lambda>z [\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]zx] = [\<lambda>z [\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]zy])\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain y where 0: \<open>([A!]x & [A!]y & x \<noteq> y &
               [\<lambda>z [\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]zx] = [\<lambda>z [\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]zy])\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>[\<lambda>z [\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]zx]x\<close>
    apply (rule betaC_2_a)
      apply "cqt:2[lambda]"
     apply (fact "cqt:2[const_var]"[axiom_inst])
    apply (rule betaC_2_a)
      apply "cqt:2[lambda]"
    apply (simp add: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
    by (simp add: "oth-class-taut:3:a" "universal-cor")
  AOT_hence \<open>[\<lambda>z [\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]zy]x\<close>
    by (rule "rule=E"[rotated, OF 0[THEN "&E"(2)]])
  AOT_hence \<open>[\<lambda>xy \<forall>F ([F]x \<equiv> [F]y)]xy\<close>
    by (rule betaC_1_a)
  AOT_hence \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    using betaC_1_a old.prod.case by fast
  AOT_hence \<open>[A!]x & [A!]y & x \<noteq> y & \<forall>F ([F]x \<equiv> [F]y)\<close> using 0 "&E" "&I" by blast
  AOT_hence \<open>\<exists>y ([A!]x & [A!]y & x \<noteq> y & \<forall>F ([F]x \<equiv> [F]y))\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>x\<exists>y ([A!]x & [A!]y & x \<noteq> y & \<forall>F ([F]x \<equiv> [F]y))\<close> by (rule "\<exists>I"(2))
qed

AOT_theorem kirchner_thm_1: \<open>[\<lambda>x \<phi>{x}]\<down> \<equiv> \<box>\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>[\<lambda>x \<phi>{x}]\<down>\<close>
  AOT_hence \<open>\<box>[\<lambda>x \<phi>{x}]\<down>\<close> by (metis "exist-nec" "vdash-properties:10")
  moreover AOT_have \<open>\<box>[\<lambda>x \<phi>{x}]\<down> \<rightarrow> \<box>\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
  proof (rule "RM:1"; rule "\<rightarrow>I"; rule GEN; rule GEN; rule "\<rightarrow>I")
    AOT_modally_strict {
      fix x y
      AOT_assume 0: \<open>[\<lambda>x \<phi>{x}]\<down>\<close>
      moreover AOT_assume \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
      ultimately AOT_have \<open>[\<lambda>x \<phi>{x}]x \<equiv> [\<lambda>x \<phi>{x}]y\<close>
        using "\<forall>E" by blast
      AOT_thus \<open>(\<phi>{x} \<equiv> \<phi>{y})\<close>
        using beta_C_meta[THEN "\<rightarrow>E", OF 0] "\<equiv>E"(6) by meson
    }
  qed
  ultimately AOT_show \<open>\<box>\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
    using "\<rightarrow>E" by blast
next
  AOT_have \<open>\<box>\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y})) \<rightarrow> \<box>\<forall>y(\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x}) \<equiv> \<phi>{y})\<close>
  proof(rule "RM:1"; rule "\<rightarrow>I"; rule GEN)
    AOT_modally_strict {
      AOT_assume \<open>\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
      AOT_hence indisc: \<open>\<phi>{x} \<equiv> \<phi>{y}\<close> if \<open>\<forall>F([F]x \<equiv> [F]y)\<close> for x y
        using "\<forall>E"(2) "\<rightarrow>E" that by blast
      AOT_show \<open>(\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x}) \<equiv> \<phi>{y})\<close> for y
      proof (rule "raa-cor:1")
        AOT_assume \<open>\<not>(\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x}) \<equiv> \<phi>{y})\<close>
        AOT_hence \<open>(\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x}) & \<not>\<phi>{y}) \<or> (\<not>(\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x})) & \<phi>{y})\<close>
          using "\<equiv>E"(1) "oth-class-taut:4:h" by blast
        moreover {
          AOT_assume 0: \<open>\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x}) & \<not>\<phi>{y}\<close>
          AOT_obtain a where \<open>\<forall>F([F]a \<equiv> [F]y) & \<phi>{a}\<close>
            using "\<exists>E"[rotated, OF 0[THEN "&E"(1)]]  by blast
          AOT_hence \<open>\<phi>{y}\<close> using indisc[THEN "\<equiv>E"(1)] "&E" by blast
          AOT_hence \<open>p & \<not>p\<close> for p using 0[THEN "&E"(2)] "&I" "raa-cor:3" by blast
        }
        moreover {
          AOT_assume 0: \<open>(\<not>(\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x})) & \<phi>{y})\<close>
          AOT_hence \<open>\<forall>x \<not>(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x})\<close>
            using "&E"(1) "cqt-further:4" "\<rightarrow>E" by blast
          AOT_hence \<open>\<not>(\<forall>F([F]y \<equiv> [F]y) & \<phi>{y})\<close> using "\<forall>E" by blast
          AOT_hence \<open>\<not>\<forall>F([F]y \<equiv> [F]y) \<or> \<not>\<phi>{y}\<close>
            using "\<equiv>E"(1) "oth-class-taut:5:c" by blast
          moreover AOT_have \<open>\<forall>F([F]y \<equiv> [F]y)\<close> by (simp add: "oth-class-taut:3:a" "universal-cor")
          ultimately AOT_have \<open>\<not>\<phi>{y}\<close> by (metis "\<not>\<not>I" "\<or>E"(2))
          AOT_hence \<open>p & \<not>p\<close> for p using 0[THEN "&E"(2)] "&I" "raa-cor:3" by blast
        }
        ultimately AOT_show \<open>p & \<not>p\<close> for p using "\<or>E"(3) "raa-cor:1" by blast
      qed
    }
  qed
  moreover AOT_assume \<open>\<box>\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
  ultimately AOT_have \<open>\<box>\<forall>y(\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x}) \<equiv> \<phi>{y})\<close>
    using "\<rightarrow>E" by blast
  AOT_thus \<open>[\<lambda>x \<phi>{x}]\<down>\<close>
    by (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I", rotated]) "cqt:2[lambda]"
qed

AOT_theorem kirchner_thm_2: \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<equiv> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close>
  AOT_hence \<open>\<box>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close> by (metis "exist-nec" "vdash-properties:10")
  moreover AOT_have \<open>\<box>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
  proof (rule "RM:1"; rule "\<rightarrow>I"; rule GEN; rule GEN; rule "\<rightarrow>I")
    AOT_modally_strict {
      fix x\<^sub>1x\<^sub>n y\<^sub>1y\<^sub>n :: \<open>'a AOT_var\<close>
      AOT_assume 0: \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close>
      moreover AOT_assume \<open>\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)\<close>
      ultimately AOT_have \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]x\<^sub>1...x\<^sub>n \<equiv> [\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]y\<^sub>1...y\<^sub>n\<close>
        using "\<forall>E" by blast
      AOT_thus \<open>(\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close>
        using beta_C_meta[THEN "\<rightarrow>E", OF 0] "\<equiv>E"(6) by meson
    }
  qed
  ultimately AOT_show \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
    using "\<rightarrow>E" by blast
next
  AOT_have \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))) \<rightarrow>
            \<box>\<forall>y\<^sub>1...\<forall>y\<^sub>n((\<exists>x\<^sub>1...\<exists>x\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n})) \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close>
  proof(rule "RM:1"; rule "\<rightarrow>I"; rule GEN)
    AOT_modally_strict {
      AOT_assume \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
      AOT_hence indisc: \<open>\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}\<close> if \<open>\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)\<close> for x\<^sub>1x\<^sub>n y\<^sub>1y\<^sub>n
        using "\<forall>E"(2) "\<rightarrow>E" that by blast
      AOT_show \<open>(\<exists>x\<^sub>1...\<exists>x\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n})) \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}\<close> for y\<^sub>1y\<^sub>n
      proof (rule "raa-cor:1")
        AOT_assume \<open>\<not>((\<exists>x\<^sub>1...\<exists>x\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n})) \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close>
        AOT_hence \<open>((\<exists>x\<^sub>1...\<exists>x\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n})) & \<not>\<phi>{y\<^sub>1...y\<^sub>n}) \<or>
                    (\<not>(\<exists>x\<^sub>1...\<exists>x\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n})) & \<phi>{y\<^sub>1...y\<^sub>n})\<close>
          using "\<equiv>E"(1) "oth-class-taut:4:h" by blast
        moreover {
          AOT_assume 0: \<open>(\<exists>x\<^sub>1...\<exists>x\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n})) & \<not>\<phi>{y\<^sub>1...y\<^sub>n}\<close>
          AOT_obtain a\<^sub>1a\<^sub>n where \<open>\<forall>F([F]a\<^sub>1...a\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{a\<^sub>1...a\<^sub>n}\<close>
            using "\<exists>E"[rotated, OF 0[THEN "&E"(1)]]  by blast
          AOT_hence \<open>\<phi>{y\<^sub>1...y\<^sub>n}\<close> using indisc[THEN "\<equiv>E"(1)] "&E" by blast
          AOT_hence \<open>p & \<not>p\<close> for p using 0[THEN "&E"(2)] "&I" "raa-cor:3" by blast
        }
        moreover {
          AOT_assume 0: \<open>(\<not>((\<exists>x\<^sub>1...\<exists>x\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n}))) & \<phi>{y\<^sub>1...y\<^sub>n})\<close>
          AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<not>(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n})\<close>
            using "&E"(1) "cqt-further:4" "\<rightarrow>E" by blast
          AOT_hence \<open>\<not>(\<forall>F([F]y\<^sub>1...y\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{y\<^sub>1...y\<^sub>n})\<close> using "\<forall>E" by blast
          AOT_hence \<open>\<not>\<forall>F([F]y\<^sub>1...y\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<or> \<not>\<phi>{y\<^sub>1...y\<^sub>n}\<close>
            using "\<equiv>E"(1) "oth-class-taut:5:c" by blast
          moreover AOT_have \<open>\<forall>F([F]y\<^sub>1...y\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)\<close>
            by (simp add: "oth-class-taut:3:a" "universal-cor")
          ultimately AOT_have \<open>\<not>\<phi>{y\<^sub>1...y\<^sub>n}\<close> by (metis "\<not>\<not>I" "\<or>E"(2))
          AOT_hence \<open>p & \<not>p\<close> for p using 0[THEN "&E"(2)] "&I" "raa-cor:3" by blast
        }
        ultimately AOT_show \<open>p & \<not>p\<close> for p using "\<or>E"(3) "raa-cor:1" by blast
      qed
    }
  qed
  moreover AOT_assume \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
  ultimately AOT_have \<open>\<box>\<forall>y\<^sub>1...\<forall>y\<^sub>n((\<exists>x\<^sub>1...\<exists>x\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) & \<phi>{x\<^sub>1...x\<^sub>n})) \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close>
    using "\<rightarrow>E" by blast
  AOT_thus \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close>
    by (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I", rotated]) "cqt:2[lambda]"
qed

AOT_theorem kirchner_thm_cor_1: \<open>[\<lambda>x \<phi>{x}]\<down> \<rightarrow> \<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> \<box>(\<phi>{x} \<equiv> \<phi>{y}))\<close>
proof(rule "\<rightarrow>I"; rule GEN; rule GEN; rule "\<rightarrow>I")
  fix x y
  AOT_assume \<open>[\<lambda>x \<phi>{x}]\<down>\<close>
  AOT_hence \<open>\<box>\<forall>x\<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
    by (rule kirchner_thm_1[THEN "\<equiv>E"(1)])
  AOT_hence \<open>\<forall>x\<box>\<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
    using CBF[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<box>\<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
    using "\<forall>E" by blast
  AOT_hence \<open>\<forall>y \<box>(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
    using CBF[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<box>(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
    using "\<forall>E" by blast
  AOT_hence \<open>\<box>\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>(\<phi>{x} \<equiv> \<phi>{y})\<close>
    using "qml:1"[axiom_inst] "vdash-properties:6" by blast
  moreover AOT_assume \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
  ultimately AOT_show \<open>\<box>(\<phi>{x} \<equiv> \<phi>{y})\<close> using "\<rightarrow>E" ind_nec by blast
qed

AOT_theorem kirchner_thm_cor_2:
  \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<rightarrow> \<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> \<box>(\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
proof(rule "\<rightarrow>I"; rule GEN; rule GEN; rule "\<rightarrow>I")
  fix x\<^sub>1x\<^sub>n y\<^sub>1y\<^sub>n
  AOT_assume \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close>
  AOT_hence 0: \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n (\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
    by (rule kirchner_thm_2[THEN "\<equiv>E"(1)])
  AOT_have \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n \<box>(\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
  proof(rule GEN; rule GEN)
    fix x\<^sub>1x\<^sub>n y\<^sub>1y\<^sub>n
    AOT_show \<open>\<box>(\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
      apply (rule "RM:1"[THEN "\<rightarrow>E", rotated, OF 0]; rule "\<rightarrow>I")
      using "\<forall>E" by blast
  qed
  AOT_hence \<open>\<forall>y\<^sub>1...\<forall>y\<^sub>n \<box>(\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
    using "\<forall>E" by blast
  AOT_hence \<open>\<box>(\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
    using "\<forall>E" by blast
  AOT_hence \<open>\<box>(\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
    using "\<forall>E" by blast
  AOT_hence 0: \<open>\<box>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> \<box>(\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close>
    using "qml:1"[axiom_inst] "vdash-properties:6" by blast
  moreover AOT_assume \<open>\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)\<close>
  moreover AOT_have \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<box>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)]\<down>\<close> by "cqt:2[lambda]"
  ultimately AOT_have \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<box>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)]x\<^sub>1...x\<^sub>n \<equiv> [\<lambda>x\<^sub>1...x\<^sub>n \<box>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)]y\<^sub>1...y\<^sub>n\<close>
    using "\<forall>E" by blast
  moreover AOT_have \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<box>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)]y\<^sub>1...y\<^sub>n\<close>
    apply (rule betaC_2_a)
      apply "cqt:2[lambda]"
     apply (fact "cqt:2[const_var]"[axiom_inst])
    by (simp add: RN GEN "oth-class-taut:3:a")
  ultimately AOT_have \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<box>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)]x\<^sub>1...x\<^sub>n\<close> using "\<equiv>E"(2) by blast
  AOT_hence \<open>\<box>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)\<close>
    using betaC_1_a by blast
  AOT_thus \<open>\<box>(\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close> using "\<rightarrow>E" 0 by blast
qed

AOT_define propositional :: \<open>\<Pi> \<Rightarrow> \<phi>\<close> (\<open>Propositional'(_')\<close>)
  prop_prop1: \<open>Propositional([F]) \<equiv>\<^sub>d\<^sub>f \<exists>p(F = [\<lambda>y p])\<close>

AOT_theorem prop_prop2_1: \<open>\<forall>p [\<lambda>y p]\<down>\<close>
  by (rule GEN) "cqt:2[lambda]"

AOT_theorem prop_prop2_2: \<open>[\<lambda>\<nu> \<phi>]\<down>\<close>
  by "cqt:2[lambda]"

AOT_theorem prop_prop2_3: \<open>F = [\<lambda>y p] \<rightarrow> \<box>\<forall>x([F]x \<equiv> p)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume 0: \<open>F = [\<lambda>y p]\<close>
  AOT_show \<open>\<box>\<forall>x([F]x \<equiv> p)\<close>
    by (rule "=E"[rotated, OF 0[symmetric]]; rule RN; rule GEN; rule beta_C_meta[THEN "\<rightarrow>E"])
      "cqt:2[lambda]"
qed

AOT_theorem prop_prop2_4: \<open>Propositional([F]) \<rightarrow> \<box>Propositional([F])\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>Propositional([F])\<close>
  AOT_hence \<open>\<exists>p(F = [\<lambda>y p])\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF prop_prop1] by blast
  then AOT_obtain p where \<open>F = [\<lambda>y p]\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>(F = [\<lambda>y p])\<close> using "id-nec:2" "modus-tollens:1" "raa-cor:3" by blast
  AOT_hence \<open>\<exists>p \<box>(F = [\<lambda>y p])\<close> using "\<exists>I" by fast
  AOT_hence 0: \<open>\<box>\<exists>p (F = [\<lambda>y p])\<close> by (metis sign_S5_thm_1 "vdash-properties:10")
  AOT_show \<open>\<box>Propositional([F])\<close>
    apply (AOT_subst \<open>\<guillemotleft>Propositional([F])\<guillemotright>\<close> \<open>\<guillemotleft>\<exists>p (F = [\<lambda>y p])\<guillemotright>\<close>)
     using prop_prop1 "\<equiv>Df" apply presburger
    by (fact 0)
qed

AOT_define indicriminate :: \<open>\<Pi> \<Rightarrow> \<phi>\<close> ("Indiscriminate'(_')")
  prop_indis: \<open>Indiscriminate([F]) \<equiv>\<^sub>d\<^sub>f F\<down> & \<box>(\<exists>x [F]x \<rightarrow> \<forall>x [F]x)\<close>

AOT_theorem prop_in_thm: \<open>Propositional([\<Pi>]) \<rightarrow> Indiscriminate([\<Pi>])\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>Propositional([\<Pi>])\<close>
  AOT_hence \<open>\<exists>p \<Pi> = [\<lambda>y p]\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF prop_prop1] by blast
  then AOT_obtain p where \<Pi>_def: \<open>\<Pi> = [\<lambda>y p]\<close> using "\<exists>E"[rotated] by blast
  AOT_show \<open>Indiscriminate([\<Pi>])\<close>
  proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF prop_indis]; rule "&I")
    AOT_show \<open>\<Pi>\<down>\<close>
      using \<Pi>_def by (meson "t=t-proper:1" "vdash-properties:6")
  next
    AOT_show \<open>\<box>(\<exists>x [\<Pi>]x \<rightarrow> \<forall>x [\<Pi>]x)\<close>
    proof (rule "=E"[rotated, OF \<Pi>_def[symmetric]]; rule RN; rule "\<rightarrow>I"; rule GEN)
      AOT_modally_strict {
        AOT_assume \<open>\<exists>x [\<lambda>y p]x\<close>
        then AOT_obtain a where \<open>[\<lambda>y p]a\<close> using "\<exists>E"[rotated] by blast
        AOT_hence 0: \<open>p\<close> by (metis betaC_1_a)
        AOT_show \<open>[\<lambda>y p]x\<close> for x
          apply (rule betaC_2_a)
            apply "cqt:2[lambda]"
           apply (fact "cqt:2[const_var]"[axiom_inst])
          by (fact 0)
      }
    qed
  qed
qed

AOT_theorem prop_in_f_1: \<open>Necessary([F]) \<rightarrow> Indiscriminate([F])\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>Necessary([F])\<close>
  AOT_hence 0: \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n [F]x\<^sub>1...x\<^sub>n\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF contingent_properties_1] by blast
  AOT_show \<open>Indiscriminate([F])\<close>
    by (rule "\<equiv>\<^sub>d\<^sub>fI"[OF prop_indis])
       (metis "0" "KBasic:1" "&I" "ex:1:a" "rule-ui:2[const_var]" "vdash-properties:6") 
qed

AOT_theorem prop_in_f_2: \<open>Impossible([F]) \<rightarrow> Indiscriminate([F])\<close>
proof (rule "\<rightarrow>I")
  AOT_modally_strict {
    AOT_have \<open>\<forall>x \<not>[F]x \<rightarrow> (\<exists>x [F]x \<rightarrow> \<forall>x [F]x)\<close>
      by (metis "instantiation" "cqt-orig:3" "Hypothetical Syllogism" "deduction-theorem" "raa-cor:3")
  }
  AOT_hence 0: \<open>\<box>\<forall>x \<not>[F]x \<rightarrow> \<box>(\<exists>x [F]x \<rightarrow> \<forall>x [F]x)\<close>
    by (rule "RM:1")
  AOT_assume \<open>Impossible([F])\<close>
  AOT_hence \<open>\<box>\<forall>x \<not>[F]x\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF contingent_properties_2] "&E" by blast
  AOT_hence 1: \<open>\<box>(\<exists>x [F]x \<rightarrow> \<forall>x [F]x)\<close> using 0 "\<rightarrow>E" by blast
  AOT_show \<open>Indiscriminate([F])\<close>
    by (rule "\<equiv>\<^sub>d\<^sub>fI"[OF prop_indis]; rule "&I")
       (simp add: "ex:1:a" "rule-ui:2[const_var]" 1)+
qed

AOT_theorem prop_in_f_3_a: \<open>\<not>Indiscriminate([E!])\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>Indiscriminate([E!])\<close>
  AOT_hence 0: \<open>\<box>(\<exists>x [E!]x \<rightarrow> \<forall>x [E!]x)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF prop_indis] "&E" by blast
  AOT_hence \<open>\<diamond>\<exists>x [E!]x \<rightarrow> \<diamond>\<forall>x [E!]x\<close>
    using "KBasic:13" "vdash-properties:10" by blast
  moreover AOT_have \<open>\<diamond>\<exists>x [E!]x\<close>
    by (simp add: thm_cont_e_3)
  ultimately AOT_have \<open>\<diamond>\<forall>x [E!]x\<close>
    by (metis "vdash-properties:6")
  AOT_thus \<open>p & \<not>p\<close> for p
    by (metis "\<equiv>\<^sub>d\<^sub>fE" AOT_dia o_objects_exist_5 "reductio-aa:1")
qed

AOT_theorem prop_in_f_3_b: \<open>\<not>Indiscriminate([E!]\<^sup>-)\<close>
proof (rule "=E"[rotated, OF rel_neg_T_2[symmetric]]; rule "raa-cor:2")
  AOT_assume \<open>Indiscriminate([\<lambda>x \<not>[E!]x])\<close>
  AOT_hence 0: \<open>\<box>(\<exists>x [\<lambda>x \<not>[E!]x]x \<rightarrow> \<forall>x [\<lambda>x \<not>[E!]x]x)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF prop_indis] "&E" by blast
  AOT_hence \<open>\<box>\<exists>x [\<lambda>x \<not>[E!]x]x \<rightarrow> \<box>\<forall>x [\<lambda>x \<not>[E!]x]x\<close>
    using "\<rightarrow>E" "qml:1" "vdash-properties:1[2]" by blast
  moreover AOT_have \<open>\<box>\<exists>x [\<lambda>x \<not>[E!]x]x\<close>
    apply (AOT_subst \<open>\<lambda>\<kappa>. \<guillemotleft>[\<lambda>x \<not>[E!]x]\<kappa>\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>\<not>[E!]\<kappa>\<guillemotright>\<close>)
    apply (rule beta_C_meta[THEN "\<rightarrow>E"])
     apply "cqt:2[lambda]"
    by (metis (full_types) "B\<diamond>" RN "T\<diamond>" "cqt-further:2" o_objects_exist_5 "vdash-properties:10")
  ultimately AOT_have 1: \<open>\<box>\<forall>x [\<lambda>x \<not>[E!]x]x\<close>
    by (metis "vdash-properties:6")
  AOT_have \<open>\<box>\<forall>x \<not>[E!]x\<close>
    apply (AOT_subst_rev \<open>\<lambda>\<kappa>. \<guillemotleft>[\<lambda>x \<not>[E!]x]\<kappa>\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>\<not>[E!]\<kappa>\<guillemotright>\<close>)
    apply (rule beta_C_meta[THEN "\<rightarrow>E"])
     apply "cqt:2[lambda]"
    by (fact 1)
  AOT_hence \<open>\<forall>x \<box>\<not>[E!]x\<close> by (metis BFs_2 "vdash-properties:10")
  moreover AOT_obtain a where abs_a: \<open>O!a\<close>
    using "instantiation" o_objects_exist_1 "qml:2" "vdash-properties:1[2]" "vdash-properties:6" by blast
  ultimately AOT_have \<open>\<box>\<not>[E!]a\<close> using "\<forall>E" by blast
  AOT_hence 2: \<open>\<not>\<diamond>[E!]a\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" AOT_dia "reductio-aa:1")
  AOT_have \<open>A!a\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF AOT_abstract])
     apply "cqt:2[lambda]"
    apply (rule betaC_2_a)
      apply "cqt:2[lambda]"
    using "cqt:2[const_var]"[axiom_inst] apply blast
    by (fact 2)
  AOT_thus \<open>p & \<not>p\<close> for p using abs_a
    by (metis "\<equiv>E"(1) oa_contingent_2 "reductio-aa:1")
qed

AOT_theorem prop_in_f_3_c: \<open>\<not>Indiscriminate(O!)\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>Indiscriminate(O!)\<close>
  AOT_hence 0: \<open>\<box>(\<exists>x O!x \<rightarrow> \<forall>x O!x)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF prop_indis] "&E" by blast
  AOT_hence \<open>\<box>\<exists>x O!x \<rightarrow> \<box>\<forall>x O!x\<close>
    using "qml:1"[axiom_inst] "vdash-properties:6" by blast
  moreover AOT_have \<open>\<box>\<exists>x O!x\<close>
    using o_objects_exist_1 by blast
  ultimately AOT_have \<open>\<box>\<forall>x O!x\<close>
    by (metis "vdash-properties:6")
  AOT_thus \<open>p & \<not>p\<close> for p
    by (metis o_objects_exist_3 "qml:2" "raa-cor:3" "vdash-properties:10" "vdash-properties:1[2]")
qed

AOT_theorem prop_in_f_3_d: \<open>\<not>Indiscriminate(A!)\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>Indiscriminate(A!)\<close>
  AOT_hence 0: \<open>\<box>(\<exists>x A!x \<rightarrow> \<forall>x A!x)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF prop_indis] "&E" by blast
  AOT_hence \<open>\<box>\<exists>x A!x \<rightarrow> \<box>\<forall>x A!x\<close>
    using "qml:1"[axiom_inst] "vdash-properties:6" by blast
  moreover AOT_have \<open>\<box>\<exists>x A!x\<close>
    using o_objects_exist_2 by blast
  ultimately AOT_have \<open>\<box>\<forall>x A!x\<close>
    by (metis "vdash-properties:6")
  AOT_thus \<open>p & \<not>p\<close> for p
    by (metis o_objects_exist_4 "qml:2" "raa-cor:3" "vdash-properties:10" "vdash-properties:1[2]")
qed

AOT_theorem prop_in_f_4_a: \<open>\<not>Propositional(E!)\<close>
  using "modus-tollens:1" prop_in_f_3_a prop_in_thm by blast

AOT_theorem prop_in_f_4_b: \<open>\<not>Propositional(E!\<^sup>-)\<close>
  using "modus-tollens:1" prop_in_f_3_b prop_in_thm by blast

AOT_theorem prop_in_f_4_c: \<open>\<not>Propositional(O!)\<close>
  using "modus-tollens:1" prop_in_f_3_c prop_in_thm by blast

AOT_theorem prop_in_f_4_d: \<open>\<not>Propositional(A!)\<close>
  using "modus-tollens:1" prop_in_f_3_d prop_in_thm by blast

AOT_theorem prop_prop_nec_1: \<open>\<diamond>\<exists>p (F = [\<lambda>y p]) \<rightarrow> \<exists>p(F = [\<lambda>y p])\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<diamond>\<exists>p (F = [\<lambda>y p])\<close>
  AOT_hence \<open>\<exists>p \<diamond>(F = [\<lambda>y p])\<close>
    by (metis "BF\<diamond>" "vdash-properties:10")
  then AOT_obtain p where \<open>\<diamond>(F = [\<lambda>y p])\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>F = [\<lambda>y p]\<close> by (metis derived_S5_rules_2 emptyE "id-nec:2" "vdash-properties:6")
  AOT_thus \<open>\<exists>p(F = [\<lambda>y p])\<close> by (rule "\<exists>I")
qed

AOT_theorem prop_prop_nec_2: \<open>\<forall>p (F \<noteq> [\<lambda>y p]) \<rightarrow> \<box>\<forall>p(F \<noteq> [\<lambda>y p])\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>p (F \<noteq> [\<lambda>y p])\<close>
  AOT_hence \<open>(F \<noteq> [\<lambda>y p])\<close> for p
    using "\<forall>E" by blast
  AOT_hence \<open>\<box>(F \<noteq> [\<lambda>y p])\<close> for p
    by (rule id_nec2_2[unvarify \<beta>, THEN "\<rightarrow>E", rotated]) "cqt:2[lambda]"
  AOT_hence \<open>\<forall>p \<box>(F \<noteq> [\<lambda>y p])\<close> by (rule GEN)
  AOT_thus \<open>\<box>\<forall>p (F \<noteq> [\<lambda>y p])\<close> using BF[THEN "\<rightarrow>E"] by fast
qed

AOT_theorem prop_prop_nec_3: \<open>\<exists>p (F = [\<lambda>y p]) \<rightarrow> \<box>\<exists>p(F = [\<lambda>y p])\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>p (F = [\<lambda>y p])\<close>
  then AOT_obtain p where \<open>(F = [\<lambda>y p])\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>(F = [\<lambda>y p])\<close> by (metis "id-nec:2" "vdash-properties:6")
  AOT_hence \<open>\<exists>p\<box>(F = [\<lambda>y p])\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<box>\<exists>p(F = [\<lambda>y p])\<close> by (metis sign_S5_thm_1 "vdash-properties:10")
qed

AOT_theorem prop_prop_nec_4: \<open>\<diamond>\<forall>p (F \<noteq> [\<lambda>y p]) \<rightarrow> \<forall>p(F \<noteq> [\<lambda>y p])\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<diamond>\<forall>p (F \<noteq> [\<lambda>y p])\<close>
  AOT_hence \<open>\<forall>p \<diamond>(F \<noteq> [\<lambda>y p])\<close> by (metis "Buridan\<diamond>" "vdash-properties:10")
  AOT_hence \<open>\<diamond>(F \<noteq> [\<lambda>y p])\<close> for p
    using "\<forall>E" by blast
  AOT_hence \<open>F \<noteq> [\<lambda>y p]\<close> for p
    by (rule id_nec2_3[unvarify \<beta>, THEN "\<rightarrow>E", rotated]) "cqt:2[lambda]"
  AOT_thus \<open>\<forall>p (F \<noteq> [\<lambda>y p])\<close> by (rule GEN)
qed

AOT_theorem enc_prop_nec_1: \<open>\<diamond>\<forall>F (x[F] \<rightarrow> \<exists>p(F = [\<lambda>y p])) \<rightarrow> \<forall>F(x[F] \<rightarrow> \<exists>p (F = [\<lambda>y p]))\<close>
proof(rule "\<rightarrow>I"; rule GEN; rule "\<rightarrow>I")
  fix F
  AOT_assume \<open>\<diamond>\<forall>F (x[F] \<rightarrow> \<exists>p(F = [\<lambda>y p]))\<close>
  AOT_hence \<open>\<forall>F \<diamond>(x[F] \<rightarrow> \<exists>p(F = [\<lambda>y p]))\<close>
    using "Buridan\<diamond>" "vdash-properties:10" by blast
  AOT_hence 0: \<open>\<diamond>(x[F] \<rightarrow> \<exists>p(F = [\<lambda>y p]))\<close> using "\<forall>E" by blast
  AOT_assume \<open>x[F]\<close>
  AOT_hence \<open>\<box>x[F]\<close> by (metis en_eq_2_1 "\<equiv>E"(1))
  AOT_hence \<open>\<diamond>\<exists>p(F = [\<lambda>y p])\<close>
    using 0 by (metis "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>\<exists>p(F = [\<lambda>y p])\<close>
    using prop_prop_nec_1[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem enc_prop_nec_2: \<open>\<forall>F (x[F] \<rightarrow> \<exists>p(F = [\<lambda>y p])) \<rightarrow> \<box>\<forall>F(x[F] \<rightarrow> \<exists>p (F = [\<lambda>y p]))\<close>
  using derived_S5_rules_1[where \<Gamma>="{}", simplified, OF enc_prop_nec_1]
  by blast


(* TODO: not part of PLM *)
AOT_theorem kir_ext_1: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>) \<rightarrow> ((\<phi> \<rightarrow> \<box>\<psi>) \<rightarrow> \<box>(\<phi> \<rightarrow> \<box>\<psi>))\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>\<phi> \<rightarrow> \<box>\<psi>\<close>
  AOT_hence \<open>\<box>(\<box>\<phi> \<rightarrow> \<box>\<psi>)\<close>
    by (metis "B\<diamond>" "KBasic2:1" "KBasic:1" "KBasic:2" "S5Basic:5" "\<equiv>E"(2) "modus-tollens:1" "reductio-aa:1")
  moreover AOT_assume \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>)\<close>
  ultimately AOT_have \<open>\<box>((\<box>\<phi> \<rightarrow> \<box>\<psi>) & (\<phi> \<rightarrow> \<box>\<phi>))\<close>
    by (metis "KBasic:3" "&I" "\<equiv>E"(2))
  moreover AOT_have \<open>\<box>((\<box>\<phi> \<rightarrow> \<box>\<psi>) & (\<phi> \<rightarrow> \<box>\<phi>)) \<rightarrow> \<box>(\<phi> \<rightarrow> \<box>\<psi>)\<close>
    apply (rule RM; rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
    using "Hypothetical Syllogism" by blast
  ultimately AOT_show \<open>\<box>(\<phi> \<rightarrow> \<box>\<psi>)\<close> using "\<rightarrow>E" by blast
qed
AOT_theorem kir_ext_2: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>) \<rightarrow> ((\<phi> \<rightarrow> \<box>\<psi>) \<rightarrow> \<box>(\<phi> \<rightarrow> \<psi>))\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>\<phi> \<rightarrow> \<box>\<psi>\<close>
  AOT_hence \<open>\<box>(\<box>\<phi> \<rightarrow> \<box>\<psi>)\<close>
    by (metis "B\<diamond>" "KBasic2:1" "KBasic:1" "KBasic:2" "S5Basic:5" "\<equiv>E"(2) "modus-tollens:1" "reductio-aa:1")
  moreover AOT_assume \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>)\<close>
  ultimately AOT_have \<open>\<box>((\<box>\<phi> \<rightarrow> \<box>\<psi>) & (\<phi> \<rightarrow> \<box>\<phi>))\<close>
    by (metis "KBasic:3" "&I" "\<equiv>E"(2))
  moreover AOT_have \<open>\<box>((\<box>\<phi> \<rightarrow> \<box>\<psi>) & (\<phi> \<rightarrow> \<box>\<phi>)) \<rightarrow> \<box>(\<phi> \<rightarrow> \<psi>)\<close>
    apply (rule RM; rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
    by (metis "deduction-theorem" "qml:2" "vdash-properties:10" "vdash-properties:1[2]")
  ultimately AOT_show \<open>\<box>(\<phi> \<rightarrow> \<psi>)\<close> using "\<rightarrow>E" by blast
qed
AOT_theorem kir_ext_3: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>) \<rightarrow> ((\<phi> \<rightarrow> \<^bold>\<A>\<psi>) \<rightarrow> \<box>(\<phi> \<rightarrow> \<^bold>\<A>\<psi>))\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>\<phi> \<rightarrow> \<^bold>\<A>\<psi>\<close>
  AOT_hence \<open>\<box>(\<box>\<phi> \<rightarrow> \<^bold>\<A>\<psi>)\<close>
     by (metis "B\<diamond>" "Act-Basic:6" "KBasic2:1" "KBasic:1" "KBasic:2" "\<equiv>E"(1) "\<equiv>E"(2) "modus-tollens:1" "reductio-aa:1")
  moreover AOT_assume \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>)\<close>
  ultimately AOT_have \<open>\<box>((\<box>\<phi> \<rightarrow> \<^bold>\<A>\<psi>) & (\<phi> \<rightarrow> \<box>\<phi>))\<close>
    by (metis "KBasic:3" "&I" "\<equiv>E"(2))
  moreover AOT_have \<open>\<box>((\<box>\<phi> \<rightarrow> \<^bold>\<A>\<psi>) & (\<phi> \<rightarrow> \<box>\<phi>)) \<rightarrow> \<box>(\<phi> \<rightarrow> \<^bold>\<A>\<psi>)\<close>
    apply (rule RM; rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
    using "Hypothetical Syllogism" by blast
  ultimately AOT_show \<open>\<box>(\<phi> \<rightarrow> \<^bold>\<A>\<psi>)\<close> using "\<rightarrow>E" by blast
qed
AOT_theorem kir_ext_4: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>) \<rightarrow> ((\<phi> \<rightarrow> \<^bold>\<A>\<psi>) \<rightarrow> \<^bold>\<A>(\<phi> \<rightarrow> \<psi>))\<close>
proof(safe intro!: "\<rightarrow>I"; rule "raa-cor:1")
  AOT_assume 1: \<open>\<phi> \<rightarrow> \<^bold>\<A>\<psi>\<close>
  AOT_assume 2: \<open>\<box>(\<phi> \<rightarrow> \<box>\<phi>)\<close>
  AOT_assume \<open>\<not>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>)\<close>
  AOT_hence 3: \<open>\<^bold>\<A>\<not>(\<phi> \<rightarrow> \<psi>)\<close>
    by (metis "Act-Basic:1" "\<or>E"(2))
  AOT_have \<open>\<^bold>\<A>(\<phi> & \<not>\<psi>)\<close>
    apply (AOT_subst \<open>\<guillemotleft>\<phi> & \<not>\<psi>\<guillemotright>\<close> \<open>\<guillemotleft>\<not>(\<phi> \<rightarrow> \<psi>)\<guillemotright>\<close>)
    apply (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
    by (fact 3)
  AOT_hence 4: \<open>\<^bold>\<A>\<phi> & \<^bold>\<A>\<not>\<psi>\<close> by (metis "Act-Basic:2" "\<equiv>E"(1))
  AOT_hence \<open>\<phi>\<close> by (metis "2" "&E"(1) "\<equiv>E"(1) sc_eq_fur_2 "vdash-properties:10")
  AOT_hence \<open>\<^bold>\<A>\<psi>\<close> using 1 "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<not>\<^bold>\<A>\<psi>\<close> using 4[THEN "&E"(2)] by (metis "\<not>\<not>I" "Act-Sub:1" "\<equiv>E"(4))
  ultimately AOT_show \<open>\<^bold>\<A>\<psi> & \<not>\<^bold>\<A>\<psi>\<close> by (rule "&I")
qed

(*<*)
end
(*>*)