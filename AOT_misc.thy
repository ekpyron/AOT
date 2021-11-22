theory AOT_misc
  imports AOT_NaturalNumbers
begin

AOT_define ExtensionOf :: \<open>\<tau> \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (\<open>ExtensionOf'(_,_')\<close>)
  "exten-property:1": \<open>ExtensionOf(x,[G]) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> \<forall>z([F]z \<equiv> [G]z))\<close>

AOT_define OrdinaryExtensionOf :: \<open>\<tau> \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (\<open>OrdinaryExtensionOf'(_,_')\<close>)
   \<open>OrdinaryExtensionOf(x,[G]) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> \<forall>z(O!z \<rightarrow> ([F]z \<equiv> [G]z)))\<close>

AOT_define FimpG :: \<open>\<Pi> \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (infixl \<open>\<Rightarrow>\<close> 50)
  "F-imp-G": \<open>[G] \<Rightarrow> [F] \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<box>\<forall>x ([G]x \<rightarrow> [F]x)\<close>

AOT_define concept :: \<open>\<Pi>\<close> (\<open>C!\<close>)
  concepts: \<open>C! =\<^sub>d\<^sub>f A!\<close>

AOT_register_rigid_restricted_type
  Concept: \<open>C!\<kappa>\<close>
proof
  AOT_modally_strict {
    AOT_have \<open>\<exists>x A!x\<close>
      using "o-objects-exist:2" "qml:2"[axiom_inst] "\<rightarrow>E" by blast
    AOT_thus \<open>\<exists>x C!x\<close>
      using "rule-id-df:1[zero]"[OF concepts, OF "oa-exist:2"] "rule=E" id_sym by fast
  }
next
  AOT_modally_strict {
    AOT_show \<open>C!\<kappa> \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
      using "cqt:5:a"[axiom_inst, THEN "\<rightarrow>E", THEN "&E"(2)] "\<rightarrow>I" by blast
  }
next
  AOT_modally_strict {
    AOT_have \<open>\<box>(A!x \<rightarrow> \<box>A!x)\<close> for x
      by (simp add: "oa-facts:2" RN)
    AOT_thus \<open>\<box>(C!x \<rightarrow> \<box>C!x)\<close> for x
      using "rule-id-df:1[zero]"[OF concepts, OF "oa-exist:2"] "rule=E" id_sym by fast
  }
qed

AOT_register_variable_names
  Concept: c

AOT_define conceptOf :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>ConceptOf'(_,_')\<close>)
  "concept-of-G": \<open>ConceptOf(c,G) \<equiv>\<^sub>d\<^sub>f G\<down> & \<forall>F (c[F] \<equiv> [G] \<Rightarrow> [F])\<close>

AOT_theorem ConceptOfOrdinaryProperty: \<open>([H] \<Rightarrow> O!) \<rightarrow> [\<lambda>x ConceptOf(x,H)]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[H] \<Rightarrow> O!\<close>
  AOT_hence \<open>\<box>\<forall>x([H]x \<rightarrow> O!x)\<close>
    using "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence \<open>\<box>\<box>\<forall>x([H]x \<rightarrow> O!x)\<close>
    using "S5Basic:6"[THEN "\<equiv>E"(1)] by blast
  moreover AOT_have \<open>\<box>\<box>\<forall>x([H]x \<rightarrow> O!x) \<rightarrow> \<box>\<forall>F\<forall>G(\<box>(G \<equiv>\<^sub>E F) \<rightarrow> ([H] \<Rightarrow> [F] \<equiv> [H] \<Rightarrow> [G]))\<close>
  proof(rule RM; safe intro!: "\<rightarrow>I" GEN "\<equiv>I")
    AOT_modally_strict {
      fix F G
      AOT_assume 0: \<open>\<box>\<forall>x([H]x \<rightarrow> O!x)\<close>
      AOT_assume \<open>\<box>G \<equiv>\<^sub>E F\<close>
      AOT_hence 1: \<open>\<box>\<forall>u([G]u \<equiv> [F]u)\<close>
        by (AOT_subst_thm eqE[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I",
              OF "cqt:2[const_var]"[axiom_inst],
              OF "cqt:2[const_var]"[axiom_inst], symmetric])
      {
        AOT_assume \<open>[H] \<Rightarrow> [F]\<close>
        AOT_hence \<open>\<box>\<forall>x([H]x \<rightarrow> [F]x)\<close>
          using "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
        moreover AOT_modally_strict {
          AOT_assume \<open>\<forall>x([H]x \<rightarrow> O!x)\<close>
          moreover AOT_assume \<open>\<forall>u([G]u \<equiv> [F]u)\<close>
          moreover AOT_assume \<open>\<forall>x([H]x \<rightarrow> [F]x)\<close>
          ultimately AOT_have \<open>[H]x \<rightarrow> [G]x\<close> for x
            by (auto intro!: "\<rightarrow>I" dest!: "\<forall>E"(2) dest: "\<rightarrow>E" "\<equiv>E")
          AOT_hence \<open>\<forall>x([H]x \<rightarrow> [G]x)\<close>
            by (rule GEN)
        }
        ultimately AOT_have \<open>\<box>\<forall>x([H]x \<rightarrow> [G]x)\<close>
          using "RN[prem]"[where
              \<Gamma>="{\<guillemotleft>\<forall>x([H]x \<rightarrow> O!x)\<guillemotright>, \<guillemotleft>\<forall>u([G]u \<equiv> [F]u)\<guillemotright>,\<guillemotleft>\<forall>x([H]x \<rightarrow> [F]x)\<guillemotright>}"]
          using 0 1 by fast
        AOT_thus \<open>[H] \<Rightarrow> [G]\<close>
          by (AOT_subst_def "F-imp-G")
             (safe intro!: "cqt:2" "&I")
      }
      {
        AOT_assume \<open>[H] \<Rightarrow> [G]\<close>
        AOT_hence \<open>\<box>\<forall>x([H]x \<rightarrow> [G]x)\<close>
          using "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
        moreover AOT_modally_strict {
          AOT_assume \<open>\<forall>x([H]x \<rightarrow> O!x)\<close>
          moreover AOT_assume \<open>\<forall>u([G]u \<equiv> [F]u)\<close>
          moreover AOT_assume \<open>\<forall>x([H]x \<rightarrow> [G]x)\<close>
          ultimately AOT_have \<open>[H]x \<rightarrow> [F]x\<close> for x
            by (auto intro!: "\<rightarrow>I" dest!: "\<forall>E"(2) dest: "\<rightarrow>E" "\<equiv>E")
          AOT_hence \<open>\<forall>x([H]x \<rightarrow> [F]x)\<close>
            by (rule GEN)
        }
        ultimately AOT_have \<open>\<box>\<forall>x([H]x \<rightarrow> [F]x)\<close>
          using "RN[prem]"[where
              \<Gamma>="{\<guillemotleft>\<forall>x([H]x \<rightarrow> O!x)\<guillemotright>, \<guillemotleft>\<forall>u([G]u \<equiv> [F]u)\<guillemotright>,\<guillemotleft>\<forall>x([H]x \<rightarrow> [G]x)\<guillemotright>}"]
          using 0 1 by fast
        AOT_thus \<open>[H] \<Rightarrow> [F]\<close>
          by (AOT_subst_def "F-imp-G")
             (safe intro!: "cqt:2" "&I")
      }
    }
  qed
  ultimately AOT_have \<open>\<box>\<forall>F\<forall>G(\<box>(G \<equiv>\<^sub>E F) \<rightarrow> ([H] \<Rightarrow> [F] \<equiv> [H] \<Rightarrow> [G]))\<close>
    using "\<rightarrow>E" by blast
  AOT_hence 0: \<open>[\<lambda>x \<forall>F(x[F] \<equiv> ([H] \<Rightarrow> [F]))]\<down>\<close>
    using Comprehension_3[THEN "\<rightarrow>E"] by blast
  AOT_show \<open>[\<lambda>x ConceptOf(x,H)]\<down>\<close>
  proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x C!x & [\<lambda>x \<forall>F(x[F] \<equiv> ([H] \<Rightarrow> [F]))]x]\<down>\<close> by "cqt:2"
  next
    AOT_show \<open>\<box>\<forall>x (C!x & [\<lambda>x \<forall>F (x[F] \<equiv> [H] \<Rightarrow> [F])]x \<equiv> ConceptOf(x,H))\<close>
    proof (rule "RN[prem]"[where \<Gamma>=\<open>{\<guillemotleft>[\<lambda>x \<forall>F(x[F] \<equiv> ([H] \<Rightarrow> [F]))]\<down>\<guillemotright>}\<close>, simplified])
      AOT_modally_strict {
        AOT_assume 0: \<open>[\<lambda>x \<forall>F (x[F] \<equiv> [H] \<Rightarrow> [F])]\<down>\<close>
        AOT_show \<open>\<forall>x (C!x & [\<lambda>x \<forall>F (x[F] \<equiv> [H] \<Rightarrow> [F])]x \<equiv> ConceptOf(x,H))\<close>
        proof(safe intro!: GEN "\<equiv>I" "\<rightarrow>I" "&I")
          fix x
          AOT_assume \<open>C!x & [\<lambda>x \<forall>F (x[F] \<equiv> [H] \<Rightarrow> [F])]x\<close>
          AOT_thus \<open>ConceptOf(x,H)\<close>
            by (AOT_subst_def "concept-of-G")
               (auto intro!: "&I" "cqt:2" dest: "&E" "\<beta>\<rightarrow>C")
        next
          fix x
          AOT_assume \<open>ConceptOf(x,H)\<close>
          AOT_hence \<open>C!x & (H\<down> & \<forall>F(x[F] \<equiv> [H] \<Rightarrow> [F]))\<close>
            by (AOT_subst_def (reverse) "concept-of-G")
          AOT_thus \<open>C!x\<close> and \<open>[\<lambda>x \<forall>F(x[F] \<equiv> [H] \<Rightarrow> [F])]x\<close>
            by (auto intro!: "\<beta>\<leftarrow>C" 0 "cqt:2" dest: "&E")
        qed
      }
    next
      AOT_show \<open>\<box>[\<lambda>x \<forall>F(x[F] \<equiv> ([H] \<Rightarrow> [F]))]\<down>\<close>
        using "exist-nec"[THEN "\<rightarrow>E"] 0 by blast
    qed
  qed
qed

AOT_define ThickForm :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>FormOf'(_,_')\<close>)
  "tform-of": \<open>FormOf(x,G) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> [G] \<Rightarrow> [F])\<close>

AOT_theorem FormOfOrdinaryProperty: \<open>([H] \<Rightarrow> O!) \<rightarrow> [\<lambda>x FormOf(x,H)]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>[H] \<Rightarrow> [O!]\<close>
  AOT_show \<open>[\<lambda>x FormOf(x,H)]\<down>\<close>
  proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x ConceptOf(x,H)]\<down>\<close>
      using 0 ConceptOfOrdinaryProperty[THEN "\<rightarrow>E"] by blast
    AOT_show \<open>\<box>\<forall>x (ConceptOf(x,H) \<equiv> FormOf(x,H))\<close>
    proof(safe intro!: RN GEN)
      AOT_modally_strict {
        fix x
        AOT_modally_strict {
          AOT_have \<open>A!x \<equiv> A!x\<close>
            by (simp add: "oth-class-taut:3:a")
          AOT_hence \<open>C!x \<equiv> A!x\<close>
            using "rule-id-df:1[zero]"[OF concepts, OF "oa-exist:2"]
                  "rule=E" id_sym by fast
        }
        AOT_thus \<open>ConceptOf(x,H) \<equiv> FormOf(x,H)\<close>
          by (AOT_subst_def "tform-of";
              AOT_subst_def "concept-of-G";
              AOT_subst \<open>C!x\<close> \<open>A!x\<close>)
             (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" dest: "&E")
      }
    qed
  qed
qed

end
