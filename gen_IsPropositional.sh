#!/bin/sh

for args in X XY XYZ; do

  vars=""
  for((i=0;i<${#args};i++))
  do
	ch="${args:$i:1}"
	vars="${vars} ${ch,,}"
  done
  vars=$(echo "${vars}" | xargs)

  echo "lemma IsPropositionalIn${args}_const[IsPropositional_intros]:"
  echo "  \"IsPropositionalIn${args} (\<lambda> ${vars} . \<Theta>)\""
  echo "  unfolding IsPropositionalIn${args}_def"
  echo "  by (simp add: meta_defs meta_aux)"

  echo "lemma IsPropositionalIn${args}_impl[IsPropositional_intros]:"
  echo "  assumes \"IsPropositionalIn${args} \<phi>\" and \"IsPropositionalIn${args} \<psi>\""
  echo "  shows \"IsPropositionalIn${args} (\<lambda> ${vars} . \<phi> ${vars} \<^bold>\<rightarrow> \<psi> ${vars})\""
  echo "  using assms unfolding IsPropositionalIn${args}_def"
  echo "  by (simp add: meta_defs meta_aux)"

  echo "lemma IsPropositionalIn${args}_not[IsPropositional_intros]:"
  echo "  assumes \"IsPropositionalIn${args} \<phi>\""
  echo "  shows \"IsPropositionalIn${args} (\<lambda> ${vars} . \<^bold>\<not>\<phi> ${vars})\""
  echo "  using assms unfolding IsPropositionalIn${args}_def"
  echo "  by (simp add: meta_defs meta_aux)"

  echo "lemma IsPropositionalIn${args}_box[IsPropositional_intros]:"
  echo "  assumes \"IsPropositionalIn${args} \<phi>\""
  echo "  shows \"IsPropositionalIn${args} (\<lambda> ${vars} . \<^bold>\<box>\<phi> ${vars})\""
  echo "  using assms unfolding IsPropositionalIn${args}_def"
  echo "  by (auto simp: meta_defs meta_aux)"

  echo "lemma IsPropositionalIn${args}_actual[IsPropositional_intros]:"
  echo "  assumes \"IsPropositionalIn${args} \<phi>\""
  echo "  shows \"IsPropositionalIn${args} (\<lambda> ${vars} . \<^bold>\<A>\<phi> ${vars})\""
  echo "  using assms unfolding IsPropositionalIn${args}_def"
  echo "  by (simp add: meta_defs meta_aux)"

  for q in 0 1 2 3 "\<nu>"; do
    echo "lemma IsPropositionalIn${args}_forall\<^sub>${q}[IsPropositional_intros]:"
    echo "  assumes \"\<And> a . IsPropositionalIn${args} (\<phi> a)\""
    echo "  shows \"IsPropositionalIn${args} (\<lambda> ${vars} . \<^bold>\<forall>\<^sub>${q} a . \<phi> a ${vars})\""
	echo "  using assms unfolding IsPropositionalIn${args}_def"
	echo "  by (simp add: meta_defs meta_aux)"
  done

  for var in ${vars}; do
	echo "lemma IsPropositionalIn${args}_ex_${var}[IsPropositional_intros]:"
	echo "  \"IsPropositionalIn${args} (\<lambda> ${vars} . \<lparr>F,${var}\<rparr>)\""
	echo "  unfolding IsPropositionalIn${args}_def"
	echo "  by (simp add: meta_defs meta_aux)"
  done

  for var1 in ${vars} a; do
	for var2 in ${vars} b; do
	  if [ "$var1" != "a" -o "$var2" != "b" ]; then
	    echo "lemma IsPropositionalIn${args}_ex_${var1}${var2}[IsPropositional_intros]:"
	    echo "  \"IsPropositionalIn${args} (\<lambda> ${vars} . \<lparr>F,${var1},${var2}\<rparr>)\""
	    echo "  unfolding IsPropositionalIn${args}_def"
	    echo "  by (simp add: meta_defs meta_aux)"
      fi
    done
  done

  for var1 in ${vars} a; do
	for var2 in ${vars} b; do
	  for var3 in ${vars} c; do
	    if [ "$var1" != "a" -o "$var2" != "b" -o "$var3" != "c" ]; then
	      echo "lemma IsPropositionalIn${args}_ex_${var1}${var2}${var3}[IsPropositional_intros]:"
	      echo "  \"IsPropositionalIn${args} (\<lambda> ${vars} . \<lparr>F,${var1},${var2},${var3}\<rparr>)\""
	      echo "  unfolding IsPropositionalIn${args}_def"
	      echo "  by (simp add: meta_defs meta_aux)"
        fi
      done
    done
  done

done
