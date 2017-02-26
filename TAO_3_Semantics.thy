theory TAO_3_Semantics
imports TAO_1_Embedding "~~/src/HOL/Eisbach/Eisbach"
begin

section{* Semantics *}

subsection{* Propositional Formulas *}

text{* Our embedding extends the notion of propositional formulas
       to functions that are propositional in the individual variables
       that are their parameters, i.e. their parameters only occur
       in exemplification and not in encoding subformulas. This weaker
       condition is enough to prove the semantics of propositional
       formulas. *}

named_theorems IsPropositional_intros

definition IsPropositionalInX :: "(\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" where
  "IsPropositionalInX \<equiv> \<lambda> \<Theta> . \<exists> \<chi> . \<Theta> = (\<lambda> x . \<chi>
    (* one place *) (\<lambda> F . \<lparr>F,x\<rparr>)
    (* two place *) (\<lambda> F . \<lparr>F,x,x\<rparr>) (\<lambda> F a . \<lparr>F,x,a\<rparr>) (\<lambda> F a . \<lparr>F,a,x\<rparr>)
    (* three place three x *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
    (* three place two x *) (\<lambda> F a . \<lparr>F,x,x,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,x,x\<rparr>)
    (* three place one x *) (\<lambda> F a b. \<lparr>F,x,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,x,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,x\<rparr>))"

lemma IsPropositionalInX_intro[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<chi>
    (* one place *) (\<lambda> F . \<lparr>F,x\<rparr>)
    (* two place *) (\<lambda> F . \<lparr>F,x,x\<rparr>) (\<lambda> F a . \<lparr>F,x,a\<rparr>) (\<lambda> F a . \<lparr>F,a,x\<rparr>)
    (* three place three x *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
    (* three place two x *) (\<lambda> F a . \<lparr>F,x,x,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,x,x\<rparr>)
    (* three place one x *) (\<lambda> F a b. \<lparr>F,x,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,x,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,x\<rparr>))"
                               unfolding IsPropositionalInX_def by blast

definition IsPropositionalInXY :: "(\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" where
  "IsPropositionalInXY \<equiv> \<lambda> \<Theta> . \<exists> \<chi> . \<Theta> = (\<lambda> x y . \<chi>
    (* only x *)
      (* one place *) (\<lambda> F . \<lparr>F,x\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,x,x\<rparr>) (\<lambda> F a . \<lparr>F,x,a\<rparr>) (\<lambda> F a . \<lparr>F,a,x\<rparr>)
      (* three place three x *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place two x *) (\<lambda> F a . \<lparr>F,x,x,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,x,x\<rparr>)
      (* three place one x *) (\<lambda> F a b. \<lparr>F,x,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,x,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,x\<rparr>)
    (* only y *)
      (* one place *) (\<lambda> F . \<lparr>F,y\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,y,y\<rparr>) (\<lambda> F a . \<lparr>F,y,a\<rparr>) (\<lambda> F a . \<lparr>F,a,y\<rparr>)
      (* three place three y *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>)
      (* three place two y *) (\<lambda> F a . \<lparr>F,y,y,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,y,y\<rparr>)
      (* three place one y *) (\<lambda> F a b. \<lparr>F,y,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,y,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,y\<rparr>)
    (* x and y *)
      (* two place *) (\<lambda> F . \<lparr>F,x,y\<rparr>) (\<lambda> F . \<lparr>F,y,x\<rparr>)
      (* three place (x,y) *) (\<lambda> F a . \<lparr>F,x,y,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,x,y\<rparr>)
      (* three place (y,x) *) (\<lambda> F a . \<lparr>F,y,x,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,y,x\<rparr>)
      (* three place (x,x,y) *) (\<lambda> F . \<lparr>F,x,x,y\<rparr>) (\<lambda> F . \<lparr>F,x,y,x\<rparr>) (\<lambda> F . \<lparr>F,y,x,x\<rparr>)
      (* three place (x,y,y) *) (\<lambda> F . \<lparr>F,x,y,y\<rparr>) (\<lambda> F . \<lparr>F,y,x,y\<rparr>) (\<lambda> F . \<lparr>F,y,y,x\<rparr>)
      (* three place (x,x,x) *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place (y,y,y) *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>))"

lemma IsPropositionalInXY_intro[IsPropositional_intros]: "IsPropositionalInXY (\<lambda> x y . \<chi> 
    (* only x *)
      (* one place *) (\<lambda> F . \<lparr>F,x\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,x,x\<rparr>) (\<lambda> F a . \<lparr>F,x,a\<rparr>) (\<lambda> F a . \<lparr>F,a,x\<rparr>)
      (* three place three x *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place two x *) (\<lambda> F a . \<lparr>F,x,x,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,x,x\<rparr>)
      (* three place one x *) (\<lambda> F a b. \<lparr>F,x,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,x,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,x\<rparr>)
    (* only y *)
      (* one place *) (\<lambda> F . \<lparr>F,y\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,y,y\<rparr>) (\<lambda> F a . \<lparr>F,y,a\<rparr>) (\<lambda> F a . \<lparr>F,a,y\<rparr>)
      (* three place three y *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>)
      (* three place two y *) (\<lambda> F a . \<lparr>F,y,y,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,y,y\<rparr>)
      (* three place one y *) (\<lambda> F a b. \<lparr>F,y,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,y,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,y\<rparr>)
    (* x and y *)
      (* two place *) (\<lambda> F . \<lparr>F,x,y\<rparr>) (\<lambda> F . \<lparr>F,y,x\<rparr>)
      (* three place (x,y) *) (\<lambda> F a . \<lparr>F,x,y,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,x,y\<rparr>)
      (* three place (y,x) *) (\<lambda> F a . \<lparr>F,y,x,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,y,x\<rparr>)
      (* three place (x,x,y) *) (\<lambda> F . \<lparr>F,x,x,y\<rparr>) (\<lambda> F . \<lparr>F,x,y,x\<rparr>) (\<lambda> F . \<lparr>F,y,x,x\<rparr>)
      (* three place (x,y,y) *) (\<lambda> F . \<lparr>F,x,y,y\<rparr>) (\<lambda> F . \<lparr>F,y,x,y\<rparr>) (\<lambda> F . \<lparr>F,y,y,x\<rparr>)
      (* three place (x,x,x) *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place (y,y,y) *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>))"
                               unfolding IsPropositionalInXY_def by metis

definition IsPropositionalInXYZ :: "(\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" where
  "IsPropositionalInXYZ \<equiv> \<lambda> \<Theta> . \<exists> \<chi> . \<Theta> = (\<lambda> x y z . \<chi>
    (* only x *)
      (* one place *) (\<lambda> F . \<lparr>F,x\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,x,x\<rparr>) (\<lambda> F a . \<lparr>F,x,a\<rparr>) (\<lambda> F a . \<lparr>F,a,x\<rparr>)
      (* three place three x *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place two x *) (\<lambda> F a . \<lparr>F,x,x,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,x,x\<rparr>)
      (* three place one x *) (\<lambda> F a b. \<lparr>F,x,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,x,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,x\<rparr>)
    (* only y *)
      (* one place *) (\<lambda> F . \<lparr>F,y\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,y,y\<rparr>) (\<lambda> F a . \<lparr>F,y,a\<rparr>) (\<lambda> F a . \<lparr>F,a,y\<rparr>)
      (* three place three y *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>)
      (* three place two y *) (\<lambda> F a . \<lparr>F,y,y,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,y,y\<rparr>)
      (* three place one y *) (\<lambda> F a b. \<lparr>F,y,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,y,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,y\<rparr>)
    (* only z *)
      (* one place *) (\<lambda> F . \<lparr>F,z\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,z,z\<rparr>) (\<lambda> F a . \<lparr>F,z,a\<rparr>) (\<lambda> F a . \<lparr>F,a,z\<rparr>)
      (* three place three z *) (\<lambda> F . \<lparr>F,z,z,z\<rparr>)
      (* three place two z *) (\<lambda> F a . \<lparr>F,z,z,a\<rparr>) (\<lambda> F a . \<lparr>F,z,a,z\<rparr>) (\<lambda> F a . \<lparr>F,a,z,z\<rparr>)
      (* three place one z *) (\<lambda> F a b. \<lparr>F,z,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,z,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,z\<rparr>)
    (* x and y *)
      (* two place *) (\<lambda> F . \<lparr>F,x,y\<rparr>) (\<lambda> F . \<lparr>F,y,x\<rparr>)
      (* three place (x,y) *) (\<lambda> F a . \<lparr>F,x,y,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,x,y\<rparr>)
      (* three place (y,x) *) (\<lambda> F a . \<lparr>F,y,x,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,y,x\<rparr>)
      (* three place (x,x,y) *) (\<lambda> F . \<lparr>F,x,x,y\<rparr>) (\<lambda> F . \<lparr>F,x,y,x\<rparr>) (\<lambda> F . \<lparr>F,y,x,x\<rparr>)
      (* three place (x,y,y) *) (\<lambda> F . \<lparr>F,x,y,y\<rparr>) (\<lambda> F . \<lparr>F,y,x,y\<rparr>) (\<lambda> F . \<lparr>F,y,y,x\<rparr>)
      (* three place (x,x,x) *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place (y,y,y) *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>)
    (* x and z *)
      (* two place *) (\<lambda> F . \<lparr>F,x,z\<rparr>) (\<lambda> F . \<lparr>F,z,x\<rparr>)
      (* three place (x,z) *) (\<lambda> F a . \<lparr>F,x,z,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,z\<rparr>) (\<lambda> F a . \<lparr>F,a,x,z\<rparr>)
      (* three place (z,x) *) (\<lambda> F a . \<lparr>F,z,x,a\<rparr>) (\<lambda> F a . \<lparr>F,z,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,z,x\<rparr>)
      (* three place (x,x,z) *) (\<lambda> F . \<lparr>F,x,x,z\<rparr>) (\<lambda> F . \<lparr>F,x,z,x\<rparr>) (\<lambda> F . \<lparr>F,z,x,x\<rparr>)
      (* three place (x,z,z) *) (\<lambda> F . \<lparr>F,x,z,z\<rparr>) (\<lambda> F . \<lparr>F,z,x,z\<rparr>) (\<lambda> F . \<lparr>F,z,z,x\<rparr>)
      (* three place (x,x,x) *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place (z,z,z) *) (\<lambda> F . \<lparr>F,z,z,z\<rparr>)
    (* y and z *)
      (* two place *) (\<lambda> F . \<lparr>F,y,z\<rparr>) (\<lambda> F . \<lparr>F,z,y\<rparr>)
      (* three place (y,z) *) (\<lambda> F a . \<lparr>F,y,z,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,z\<rparr>) (\<lambda> F a . \<lparr>F,a,y,z\<rparr>)
      (* three place (z,y) *) (\<lambda> F a . \<lparr>F,z,y,a\<rparr>) (\<lambda> F a . \<lparr>F,z,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,z,y\<rparr>)
      (* three place (y,y,z) *) (\<lambda> F . \<lparr>F,y,y,z\<rparr>) (\<lambda> F . \<lparr>F,y,z,y\<rparr>) (\<lambda> F . \<lparr>F,z,y,y\<rparr>)
      (* three place (y,z,z) *) (\<lambda> F . \<lparr>F,y,z,z\<rparr>) (\<lambda> F . \<lparr>F,z,y,z\<rparr>) (\<lambda> F . \<lparr>F,z,z,y\<rparr>)
      (* three place (y,y,y) *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>)
      (* three place (z,z,z) *) (\<lambda> F . \<lparr>F,z,z,z\<rparr>)
    (* x y z *)
      (* three place (x,...) *) (\<lambda> F . \<lparr>F,x,y,z\<rparr>) (\<lambda> F . \<lparr>F,x,z,y\<rparr>)
      (* three place (y,...) *) (\<lambda> F . \<lparr>F,y,x,z\<rparr>) (\<lambda> F . \<lparr>F,y,z,x\<rparr>)
      (* three place (z,...) *) (\<lambda> F . \<lparr>F,z,x,y\<rparr>) (\<lambda> F . \<lparr>F,z,y,x\<rparr>)
)"

lemma IsPropositionalInXYZ_intro[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<chi>
    (* only x *)
      (* one place *) (\<lambda> F . \<lparr>F,x\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,x,x\<rparr>) (\<lambda> F a . \<lparr>F,x,a\<rparr>) (\<lambda> F a . \<lparr>F,a,x\<rparr>)
      (* three place three x *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place two x *) (\<lambda> F a . \<lparr>F,x,x,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,x,x\<rparr>)
      (* three place one x *) (\<lambda> F a b. \<lparr>F,x,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,x,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,x\<rparr>)
    (* only y *)
      (* one place *) (\<lambda> F . \<lparr>F,y\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,y,y\<rparr>) (\<lambda> F a . \<lparr>F,y,a\<rparr>) (\<lambda> F a . \<lparr>F,a,y\<rparr>)
      (* three place three y *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>)
      (* three place two y *) (\<lambda> F a . \<lparr>F,y,y,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,y,y\<rparr>)
      (* three place one y *) (\<lambda> F a b. \<lparr>F,y,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,y,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,y\<rparr>)
    (* only z *)
      (* one place *) (\<lambda> F . \<lparr>F,z\<rparr>)
      (* two place *) (\<lambda> F . \<lparr>F,z,z\<rparr>) (\<lambda> F a . \<lparr>F,z,a\<rparr>) (\<lambda> F a . \<lparr>F,a,z\<rparr>)
      (* three place three z *) (\<lambda> F . \<lparr>F,z,z,z\<rparr>)
      (* three place two z *) (\<lambda> F a . \<lparr>F,z,z,a\<rparr>) (\<lambda> F a . \<lparr>F,z,a,z\<rparr>) (\<lambda> F a . \<lparr>F,a,z,z\<rparr>)
      (* three place one z *) (\<lambda> F a b. \<lparr>F,z,a,b\<rparr>) (\<lambda> F a b. \<lparr>F,a,z,b\<rparr>) (\<lambda> F a b . \<lparr>F,a,b,z\<rparr>)
    (* x and y *)
      (* two place *) (\<lambda> F . \<lparr>F,x,y\<rparr>) (\<lambda> F . \<lparr>F,y,x\<rparr>)
      (* three place (x,y) *) (\<lambda> F a . \<lparr>F,x,y,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,x,y\<rparr>)
      (* three place (y,x) *) (\<lambda> F a . \<lparr>F,y,x,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,y,x\<rparr>)
      (* three place (x,x,y) *) (\<lambda> F . \<lparr>F,x,x,y\<rparr>) (\<lambda> F . \<lparr>F,x,y,x\<rparr>) (\<lambda> F . \<lparr>F,y,x,x\<rparr>)
      (* three place (x,y,y) *) (\<lambda> F . \<lparr>F,x,y,y\<rparr>) (\<lambda> F . \<lparr>F,y,x,y\<rparr>) (\<lambda> F . \<lparr>F,y,y,x\<rparr>)
      (* three place (x,x,x) *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place (y,y,y) *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>)
    (* x and z *)
      (* two place *) (\<lambda> F . \<lparr>F,x,z\<rparr>) (\<lambda> F . \<lparr>F,z,x\<rparr>)
      (* three place (x,z) *) (\<lambda> F a . \<lparr>F,x,z,a\<rparr>) (\<lambda> F a . \<lparr>F,x,a,z\<rparr>) (\<lambda> F a . \<lparr>F,a,x,z\<rparr>)
      (* three place (z,x) *) (\<lambda> F a . \<lparr>F,z,x,a\<rparr>) (\<lambda> F a . \<lparr>F,z,a,x\<rparr>) (\<lambda> F a . \<lparr>F,a,z,x\<rparr>)
      (* three place (x,x,z) *) (\<lambda> F . \<lparr>F,x,x,z\<rparr>) (\<lambda> F . \<lparr>F,x,z,x\<rparr>) (\<lambda> F . \<lparr>F,z,x,x\<rparr>)
      (* three place (x,z,z) *) (\<lambda> F . \<lparr>F,x,z,z\<rparr>) (\<lambda> F . \<lparr>F,z,x,z\<rparr>) (\<lambda> F . \<lparr>F,z,z,x\<rparr>)
      (* three place (x,x,x) *) (\<lambda> F . \<lparr>F,x,x,x\<rparr>)
      (* three place (z,z,z) *) (\<lambda> F . \<lparr>F,z,z,z\<rparr>)
    (* y and z *)
      (* two place *) (\<lambda> F . \<lparr>F,y,z\<rparr>) (\<lambda> F . \<lparr>F,z,y\<rparr>)
      (* three place (y,z) *) (\<lambda> F a . \<lparr>F,y,z,a\<rparr>) (\<lambda> F a . \<lparr>F,y,a,z\<rparr>) (\<lambda> F a . \<lparr>F,a,y,z\<rparr>)
      (* three place (z,y) *) (\<lambda> F a . \<lparr>F,z,y,a\<rparr>) (\<lambda> F a . \<lparr>F,z,a,y\<rparr>) (\<lambda> F a . \<lparr>F,a,z,y\<rparr>)
      (* three place (y,y,z) *) (\<lambda> F . \<lparr>F,y,y,z\<rparr>) (\<lambda> F . \<lparr>F,y,z,y\<rparr>) (\<lambda> F . \<lparr>F,z,y,y\<rparr>)
      (* three place (y,z,z) *) (\<lambda> F . \<lparr>F,y,z,z\<rparr>) (\<lambda> F . \<lparr>F,z,y,z\<rparr>) (\<lambda> F . \<lparr>F,z,z,y\<rparr>)
      (* three place (y,y,y) *) (\<lambda> F . \<lparr>F,y,y,y\<rparr>)
      (* three place (z,z,z) *) (\<lambda> F . \<lparr>F,z,z,z\<rparr>)
    (* x y z *)
      (* three place (x,...) *) (\<lambda> F . \<lparr>F,x,y,z\<rparr>) (\<lambda> F . \<lparr>F,x,z,y\<rparr>)
      (* three place (y,...) *) (\<lambda> F . \<lparr>F,y,x,z\<rparr>) (\<lambda> F . \<lparr>F,y,z,x\<rparr>)
      (* three place (z,...) *) (\<lambda> F . \<lparr>F,z,x,y\<rparr>) (\<lambda> F . \<lparr>F,z,y,x\<rparr>)
)"
                      unfolding IsPropositionalInXYZ_def by metis (* takes a long time *)

subsection{* Semantics *}

locale Semantics
begin
  named_theorems semantics

  text{* The domains for the terms in the language. *}
  type_synonym R\<^sub>\<kappa> = "\<nu>"
  type_synonym R\<^sub>0 = "j\<Rightarrow>i\<Rightarrow>bool"
  type_synonym R\<^sub>1 = "\<upsilon>\<Rightarrow>R\<^sub>0"
  type_synonym R\<^sub>2 = "\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>R\<^sub>0"
  type_synonym R\<^sub>3 = "\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>R\<^sub>0"
  type_synonym W = i

  text{* Denotations of the terms in the language. *}
  lift_definition d\<^sub>\<kappa> :: "\<kappa>\<Rightarrow>R\<^sub>\<kappa> option" is "\<lambda> x . (if fst x then Some (snd x) else None)" .
  lift_definition d\<^sub>0 :: "\<Pi>\<^sub>0\<Rightarrow>R\<^sub>0 option" is Some .
  lift_definition d\<^sub>1 :: "\<Pi>\<^sub>1\<Rightarrow>R\<^sub>1 option" is Some .
  lift_definition d\<^sub>2 :: "\<Pi>\<^sub>2\<Rightarrow>R\<^sub>2 option" is Some .
  lift_definition d\<^sub>3 :: "\<Pi>\<^sub>3\<Rightarrow>R\<^sub>3 option" is Some .

  text{* Designated actual world. *}
  definition w\<^sub>0 where "w\<^sub>0 \<equiv> dw"

  text{* exemplification extensions *}

  definition ex0 :: "R\<^sub>0\<Rightarrow>W\<Rightarrow>bool"
    where "ex0 \<equiv> \<lambda> F . F dj"
  definition ex1 :: "R\<^sub>1\<Rightarrow>W\<Rightarrow>(R\<^sub>\<kappa> set)"
    where "ex1 \<equiv> \<lambda> F w . { x . F (\<nu>\<upsilon> x) dj w }"
  definition ex2 :: "R\<^sub>2\<Rightarrow>W\<Rightarrow>((R\<^sub>\<kappa>\<times>R\<^sub>\<kappa>) set)"
    where "ex2 \<equiv> \<lambda> F w . { (x,y) . F (\<nu>\<upsilon> x) (\<nu>\<upsilon> y) dj w }"
  definition ex3 :: "R\<^sub>3\<Rightarrow>W\<Rightarrow>((R\<^sub>\<kappa>\<times>R\<^sub>\<kappa>\<times>R\<^sub>\<kappa>) set)"
    where "ex3 \<equiv> \<lambda> F w . { (x,y,z) . F (\<nu>\<upsilon> x) (\<nu>\<upsilon> y) (\<nu>\<upsilon> z) dj w }"

  text{* encoding extensions *}

  definition en :: "R\<^sub>1\<Rightarrow>(R\<^sub>\<kappa> set)"
    where "en \<equiv> \<lambda> F . { x . case x of \<alpha>\<nu> y \<Rightarrow> make\<Pi>\<^sub>1 (\<lambda> x . F x) \<in> y | _ \<Rightarrow> False }"

  text{* semantics for exemplification and encoding *}

  lemma T1_1[semantics]: "(w \<Turnstile> \<lparr>F,x\<rparr>) = (\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> ex1 r w)"
    by (simp add: meta_defs meta_aux ex1_def d\<^sub>1_def d\<^sub>\<kappa>_def denotation_def meta_denotes_def)
  lemma T1_2[semantics]: "(w \<Turnstile> \<lparr>F,x,y\<rparr>) = (\<exists> r o\<^sub>1 o\<^sub>2 . Some r = d\<^sub>2 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                                                    \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> (o\<^sub>1, o\<^sub>2) \<in> ex2 r w)"
    by (simp add: meta_defs meta_aux ex2_def d\<^sub>2_def d\<^sub>\<kappa>_def denotation_def meta_denotes_def)
  lemma T1_3[semantics]: "(w \<Turnstile> \<lparr>F,x,y,z\<rparr>) = (\<exists> r o\<^sub>1 o\<^sub>2 o\<^sub>3 . Some r = d\<^sub>3 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                                \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> Some o\<^sub>3 = d\<^sub>\<kappa> z \<and> (o\<^sub>1, o\<^sub>2, o\<^sub>3) \<in> ex3 r w)"
    by (simp add: meta_defs meta_aux ex3_def d\<^sub>3_def d\<^sub>\<kappa>_def denotation_def meta_denotes_def)

  lemma T2[semantics]: "(w \<Turnstile> \<lbrace>x,F\<rbrace>) = (\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> en r)"
    by (simp add: meta_defs meta_aux en_def d\<^sub>1_def d\<^sub>\<kappa>_def denotation_def meta_denotes_def split: \<nu>.split)

  lemma T3[semantics]: "(w \<Turnstile> \<lparr>F\<rparr>) = (\<exists> r . Some r = d\<^sub>0 F \<and> ex0 r w)"
    by (simp add: meta_defs meta_aux ex0_def d\<^sub>0_def)

  text{* semantics for connectives and quantifiers *}

  lemma T4[semantics]: "(w \<Turnstile> \<^bold>\<not>\<psi>) = (\<not>(w \<Turnstile> \<psi>))"
    by (simp add: meta_defs meta_aux)

  lemma T5[semantics]: "(w \<Turnstile> \<psi> \<^bold>\<rightarrow> \<chi>) = (\<not>(w \<Turnstile> \<psi>) \<or> (w \<Turnstile> \<chi>))"
    by (simp add: meta_defs meta_aux)

  lemma T6[semantics]: "(w \<Turnstile> \<^bold>\<box>\<psi>) = (\<forall> v . (v \<Turnstile> \<psi>))"
    by (simp add: meta_defs meta_aux)

  lemma T7[semantics]: "(w \<Turnstile> \<^bold>\<A>\<psi>) = (dw \<Turnstile> \<psi>)"
    by (simp add: meta_defs meta_aux)

  lemma T8_\<nu>[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>\<nu> x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_0[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>0 x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_1[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>1 x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_2[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>2 x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_3[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>3 x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_\<o>[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>\<o> x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  text{* semantics for descriptions and lambda expressions *}

  lemma D3[semantics]: "d\<^sub>\<kappa> (\<^bold>\<iota>x . \<psi> x) = (if (\<exists>x . (w\<^sub>0 \<Turnstile> \<psi> x) \<and> (\<forall> y . (w\<^sub>0  \<Turnstile> \<psi> y) \<longrightarrow> y = x))
                                         then (Some (THE x . (w\<^sub>0 \<Turnstile> \<psi> x))) else None)"
    by (auto simp: meta_defs meta_aux d\<^sub>\<kappa>_def w\<^sub>0_def)

  lemma D4_1[semantics]: "d\<^sub>1 (\<^bold>\<lambda> x . \<lparr>F, x\<^sup>P\<rparr>) = d\<^sub>1 F"
    by (simp add: meta_defs meta_aux)

  lemma D4_2[semantics]: "d\<^sub>2 (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<lparr>F, x\<^sup>P, y\<^sup>P\<rparr>)) = d\<^sub>2 F"
    by (simp add: meta_defs meta_aux)

  lemma D4_3[semantics]: "d\<^sub>3 (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<lparr>F, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>)) = d\<^sub>3 F"
    by (simp add: meta_defs meta_aux)

  lemma [simp]: "fst (eval\<kappa> (\<upsilon>\<nu> (\<nu>\<upsilon> (snd (eval\<kappa> x)))\<^sup>P))"
    apply transfer by simp
  lemma [simp]: "(\<nu>\<upsilon> (snd (eval\<kappa> (\<upsilon>\<nu> (\<nu>\<upsilon> (snd (eval\<kappa> x)))\<^sup>P)))) = (\<nu>\<upsilon> (snd (eval\<kappa> x)))"
    apply transfer using \<nu>\<upsilon>_\<upsilon>\<nu>_id by auto

  lemma D5_1[semantics]: "IsPropositionalInX \<phi> \<Longrightarrow> (\<And> w o\<^sub>1 r . Some r = d\<^sub>1 (\<^bold>\<lambda> x . (\<phi> (x\<^sup>P))) \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<longrightarrow> (o\<^sub>1 \<in> ex1 r w) = (w \<Turnstile> \<phi> x))"
    unfolding IsPropositionalInX_def
    by (auto simp: ex1_def ex2_def meta_defs meta_aux d\<^sub>2_def d\<^sub>1_def d\<^sub>\<kappa>_def meta_denotes_def denotation_def)

  lemma D5_2[semantics]: "IsPropositionalInXY \<phi> \<Longrightarrow> (\<And> w o\<^sub>1 o\<^sub>2 r . Some r = d\<^sub>2 (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<phi> (x\<^sup>P) (y\<^sup>P))) \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<longrightarrow> ((o\<^sub>1,o\<^sub>2) \<in> ex2 r w) = (w \<Turnstile> \<phi> x y))"
    unfolding IsPropositionalInX_def IsPropositionalInXY_def
    by (auto simp: ex1_def ex2_def meta_defs meta_aux d\<^sub>2_def d\<^sub>1_def d\<^sub>\<kappa>_def meta_denotes_def denotation_def)

  lemma D5_3[semantics]: "IsPropositionalInXYZ \<phi> \<Longrightarrow> (\<And> w o\<^sub>1 o\<^sub>2 o\<^sub>3 r . Some r = d\<^sub>3 (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P))) \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> Some o\<^sub>3 = d\<^sub>\<kappa> z \<longrightarrow> ((o\<^sub>1,o\<^sub>2,o\<^sub>3) \<in> ex3 r w) = (w \<Turnstile> \<phi> x y z))"
    unfolding IsPropositionalInX_def IsPropositionalInXY_def  IsPropositionalInXYZ_def
    by (auto simp: ex1_def ex2_def ex3_def meta_defs meta_aux d\<^sub>3_def d\<^sub>2_def d\<^sub>1_def d\<^sub>\<kappa>_def meta_denotes_def denotation_def)

  lemma D6[semantics]: "(\<And> w r . Some r = d\<^sub>0 (\<^bold>\<lambda>\<^sup>0 \<phi>) \<longrightarrow> ex0 r w = (w \<Turnstile> \<phi>))"
    by (auto simp: ex0_def meta_defs meta_aux d\<^sub>0_def)

  text{* auxiliary lemmata *}

  lemma propex\<^sub>1: "\<exists> r . Some r = d\<^sub>1 F" unfolding d\<^sub>1_def by simp
  lemma d\<^sub>1_inject: "\<And>x y. d\<^sub>1 x = d\<^sub>1 y \<Longrightarrow> x = y" unfolding d\<^sub>1_def by (simp add: eval\<Pi>\<^sub>1_inject)
  lemma d\<^sub>\<kappa>_inject: "\<And>x y o\<^sub>1. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>1 = d\<^sub>\<kappa> y \<Longrightarrow> x = y"
  proof -
    fix x :: \<kappa> and y :: \<kappa> and o\<^sub>1 :: \<nu>
    assume "Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>1 = d\<^sub>\<kappa> y"
    moreover then have "fst (eval\<kappa> x) \<and> fst (eval\<kappa> y) \<and> snd (eval\<kappa> x) = o\<^sub>1 \<and> snd (eval\<kappa> x) = o\<^sub>1"
      unfolding d\<^sub>\<kappa>_def apply transfer apply simp by (metis option.distinct(1) option.inject)
    ultimately show "x = y" unfolding d\<^sub>\<kappa>_def apply transfer by auto
  qed
  lemma d\<^sub>\<kappa>_proper: "d\<^sub>\<kappa> (u\<^sup>P) = Some u" unfolding d\<^sub>\<kappa>_def by (simp add: \<nu>\<kappa>_def meta_aux)
end

subsection{* Validity Syntax *}

(* disable list syntax [] to replace it with truth evaluation *)
(*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
(*<*) no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 

abbreviation validity_in :: "\<o>\<Rightarrow>i\<Rightarrow>bool" ("[_ in _]" [1]) where
  "validity_in \<equiv> \<lambda> \<phi> v . v \<Turnstile> \<phi>"
abbreviation actual_validity :: "\<o>\<Rightarrow>bool" ("[_]" [1]) where
  "actual_validity \<equiv> \<lambda> \<phi> . dw \<Turnstile> \<phi>"
abbreviation necessary_validity :: "\<o>\<Rightarrow>bool" ("\<box>[_]" [1]) where
  "necessary_validity \<equiv> \<lambda> \<phi> . \<forall> v . (v \<Turnstile> \<phi>)"

end
