theory %invisible Content
  imports Chi_Calculus.Proper_Weak_Transition_System
begin

section \<open>The \<open>\<natural>\<close>-calculus\<close>

subsection \<open>Basics\<close>

paragraph \<open>Key properties\<close>

text \<open>
  \<^item> Inspired by the \<open>\<pi>\<close>-calculus and \<open>\<psi>\<close>-calculi

  \<^item> Embedded into functional host languages

      \<^item> Haskell (for execution)

      \<^item> Isabelle/HOL (for verification)

  \<^item> Uses higher-order abstract syntax\\
    (binding structures represented by host-language functions)

  \<^item> Minimalistic
\<close>

paragraph \<open>Language\<close>

text \<open>
  \<^item> Do nothing:@{term [display] \<open>\<zero>\<close>}

  \<^item> Send value \<open>x\<close> to channel \<open>a\<close>:@{term [display] \<open>a \<triangleleft> x :: process\<close>}

  \<^item> Receive value \<open>x\<close> from channel \<open>a\<close> and continue with \<^term>\<open>P x\<close>:@{term [display]
    \<open>a \<triangleright> x. P x\<close>}

  \<^item> Perform processes \<open>p\<close> and \<open>q\<close> concurrently:@{term [display] \<open>p \<parallel> q\<close>}

  \<^item> Create new channel \<open>a\<close> and continue with \<^term>\<open>P a\<close>:@{term [display] \<open>\<nu> a. P a :: process\<close>}
\<close>

subsection \<open>Operational semantics\<close>

no_notation %invisible proper_transition (infix "\<rightarrow>\<^sub>\<sharp>" 50)
notation %invisible proper_transition ("_ \<rightarrow>_" [51, 51] 50)

paragraph \<open>Communication\<close>

text \<open>
  \<^item> Key rules:

      \<^item> Sending:@{lemma [display]
        \<open>a \<triangleleft> x \<rightarrow>\<lparr>a \<triangleleft> x\<rparr> \<zero>\<close>
        by (blast intro: sending output_without_opening)}

      \<^item> Receiving:@{lemma [display]
        \<open>a \<triangleright> x. P x \<rightarrow>\<lparr>a \<triangleright> x\<rparr> P x\<close>
        by (fastforce intro: receiving simple)}

      \<^item> Communication:@{lemma [display]
        \<open>\<lbrakk>p \<rightarrow>\<lparr>a \<triangleleft> x\<rparr> p'; q \<rightarrow>\<lparr>a \<triangleright> x\<rparr> q'\<rbrakk> \<Longrightarrow> p \<parallel> q \<rightarrow>\<lparr>\<tau>\<rparr> p' \<parallel> q'\<close>
        by (fastforce elim: proper_transition.cases intro: ltr communication simple)}

  \<^item> Asynchronous communication despite synchronous semantics

      \<^item> No continuation after send (no \<open>a \<triangleleft> x. p\<close>, only \<^term>\<open>a \<triangleleft> x :: process\<close>)

      \<^item> Only ``asynchronous continuations'' possible: \<^term>\<open>a \<triangleleft> x \<parallel> p\<close>
\<close>

axiomatization %invisible chan_to_val :: "chan \<Rightarrow> val" ("\<cent>_")
text_raw \<open>\renewcommand{\isasymcent}{}\<close>

paragraph \<open>Local channels\<close>

lemma %invisible pi_calculus_closing:
  assumes "p \<rightarrow>\<lparr>a \<triangleleft> \<nu> b. \<cent>b\<rparr> P b" and "\<And>b. q \<rightarrow>\<lparr>a \<triangleright> \<cent>b\<rparr> Q b"
  shows "p \<parallel> q \<rightarrow>\<lparr>\<tau>\<rparr> \<nu> b. (P b \<parallel> Q b)"
proof -
  from assms(1) obtain U where "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> U b" and "\<And>b. U b \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> \<cent>b\<rbrace> P b"
    by (fast elim: proper_transition.cases)
  moreover from assms(2) have "\<And>b. q \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> \<cent>b\<rbrace> Q b"
    by (fastforce elim: proper_transition.cases)
  ultimately show ?thesis
    by (fastforce intro: ltr communication opening_left scoped_acting simple)
qed

text \<open>
  \<^item> Comparatively simple rules involving scope:

      \<^item> Scope opening:@{lemma [display]
        \<open>(\<And>b. P b \<rightarrow>\<lparr>a \<triangleleft> \<cent>b\<rparr> Q b) \<Longrightarrow> \<nu> b. P b \<rightarrow>\<lparr>a \<triangleleft> \<nu> b. \<cent>b\<rparr> Q b\<close>
        by (blast intro: opening output_with_opening)}

      \<^item> Communication with scope closing:@{lemma [display, source]
        "\<lbrakk>p \<rightarrow>\<lparr>a \<triangleleft> \<nu> b. \<cent>b\<rparr> P b; \<And>b. q \<rightarrow>\<lparr>a \<triangleright> \<cent>b\<rparr> Q b\<rbrakk> \<Longrightarrow>\<^latex>\<open>\\\<close>p \<parallel> q \<rightarrow>\<lparr>\<tau>\<rparr> \<nu> b. (P b \<parallel> Q b)"
        by (fact pi_calculus_closing)}

      \<^item> Acting inside scope:@{lemma [display]
        \<open>(\<And>a. P a \<rightarrow>\<lparr>\<delta>\<rparr> Q a) \<Longrightarrow> \<nu> a. P a \<rightarrow>\<lparr>\<delta>\<rparr> \<nu> a. Q a\<close>
        by (blast elim: proper_transition.cases intro: acting_scope simple)}

  \<^item> The whole story is much more complicated

      \<^item> The \<^bold>\<open>\<open>\<pi>\<close>-calculus\<close> only permits you to publish individual channels

      \<^item> The \<^bold>\<open>\<open>\<natural>\<close>-calculus\<close> permits you to publish multiple channels\\as part of a single value
\<close>

paragraph \<open>Taming the complexity\<close>

text \<open>
  \<^item> The complexity is in two places

      \<^item> Some labels deal with multiple concepts

      \<^item> Some rules deal with multiple concepts

  \<^item> We define the transition system in two steps to simplify matters

      \<^item> The \<^bold>\<open>basic transition system\<close> uses distinct transitions\\for opening scopes

          \<^item> Each label deals with one thing

          \<^item> Each rule deals with one thing

      \<^item> The \<^bold>\<open>proper transition system\<close> bundles scope opening\\
        and sending transitions from the basic transition system
\<close>

no_notation %invisible basic_transition (infix "\<rightarrow>\<^sub>\<flat>" 50)
notation %invisible basic_transition ("_ \<rightarrow>\<^sub>\<flat>_" [51, 51] 50)

no_notation %invisible proper_transition ("_ \<rightarrow>_" [51, 51] 50)
notation %invisible proper_transition ("_ \<rightarrow>\<^sub>\<sharp>_" [51, 51] 50)

paragraph \<open>The basic transition system\<close>

text \<open>
  \<^item> Communication-related rules as shown before

      \<^item> Sending

      \<^item> Receiving

      \<^item> Communication

  \<^item> Scope-related rules:

      \<^item> Opening:@{lemma [display]
        \<open>\<nu> a. P a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close>
        by (rule opening)}

      \<^item> Closing after acting:@{lemma [display, source]
        "\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R a\<rbrakk> \<Longrightarrow>\<^latex>\<open>\\\<close>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. R a"
        by (fact scoped_acting)}

      \<^item> Closing after another opening:@{lemma [display, source]
        "\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> R a b\<rbrakk> \<Longrightarrow>\<^latex>\<open>\\\<close>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. R a b"
        by (fact scoped_opening)}

  \<^item> Trivial congruence rules, for parallel composition only
\<close>

paragraph \<open>The proper transition system\<close>

text \<open>
  \<^item> Simple rules:

      \<^item> Sending:@{lemma [display]
        \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q\<close>
        by (blast intro: output_without_opening)}

      \<^item> Receiving:@{lemma [display]
        \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> q\<close>
        by (auto intro: simple)}

      \<^item> Silent action:@{lemma [display]
        \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q\<close>
        by (auto intro: simple)}

  \<^item> Opening (general idea):

      \<^item> One scope:@{lemma [display, source]
        "\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P b; \<And>b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> f b\<rparr> Q b\<rbrakk> \<Longrightarrow>\<^latex>\<open>\\\<close>p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. f b\<rparr> Q b"
        by (fact output_with_opening)}

      \<^item> Two scopes:@{lemma [display, source]
        "\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P b; \<And>b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> c. f b c\<rparr> Q b c\<rbrakk> \<Longrightarrow>\<^latex>\<open>\\\<close>p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b c. f b c\<rparr> Q b c"
        by (fact output_with_opening)}

      \<^item> etc.
\<close>

paragraph \<open>Residuals\<close>

text \<open>
  \<^item> Binders in labels cover also target processes

      \<^item> Basic transition system:@{term [display] \<open>\<lbrace>\<nu> a\<rbrace> P a\<close>}

      \<^item> Proper transition system:@{text [display] \<open>\<lparr>a \<triangleleft> \<nu> b\<^sub>1 \<dots> b\<^sub>n. f b\<^sub>1 \<dots> b\<^sub>n\<rparr> P b\<^sub>1 \<dots> b\<^sub>n\<close>}

  \<^item> We bundle labels and target processes, leading to \<^bold>\<open>residuals\<close>

    \<^item> Basic transition system:

        \<^item> Acting:@{lemma [display, source]
          "Acting \<alpha> p \<equiv> \<lbrace>\<alpha>\<rbrace> p"
          by (fact reflexive)}

        \<^item> Opening:@{lemma [display, source]
          "Opening P \<equiv> \<lbrace>\<nu> a\<rbrace> P a"
          by (fact reflexive)}

    \<^item> Proper transition system:

        \<^item> More complex

        \<^item> Otherwise similar to basic transition system
\<close>

subsection \<open>Behavioral equivalence\<close>

context %invisible transition_system begin

paragraph \<open>Bisimilarity\<close>

(*
  We prove the forward part of the first statement of the slide specialized to the proper transition
  system and restricted to simple transitions as a sanity check.
*)
lemma %invisible "proper.sim \<X> \<Longrightarrow> (\<forall>p q \<delta> p'. \<X> p q \<and> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> p' \<longrightarrow> (\<exists>q'. q \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q' \<and> \<X> p' q'))"
  by (blast elim: proper_lift_cases intro: simple_lift)

text \<open>
  \<^item> The standard notion of behavioral equivalence is \<^bold>\<open>bisimilarity\<close>

  \<^item> Definition in three steps:

      \<^item> Simulation relations:@{text [display]
        \<open>sim \<X> \<longleftrightarrow>\<^latex>\<open>\\\<close>(\<forall>p q \<xi> p'. \<X> p q \<and> p \<rightarrow>\<lparr>\<xi>\<rparr> p' \<longrightarrow> (\<exists>q'. q \<rightarrow>\<lparr>\<xi>\<rparr> q' \<and> \<X> p' q'))\<close>}

      \<^item> Bisimulation relations:@{lemma [display, source]
        "bisim \<X> \<longleftrightarrow> sim \<X> \<and> sim \<X>\<inverse>\<inverse>"
        by (fact refl)}

      \<^item> Bisimilarity:@{lemma [display]
        \<open>(\<sim>) = (GREATEST \<X>. bisim \<X>)\<close>
        by (fact bisimilarity_is_greatest_bisimulation)}

  \<^item> Standard definition of \<^term>\<open>sim\<close> does not work with scope opening

      \<^item> Assumes one target process

      \<^item> Refers to labels and target processes separately
\<close>

end %invisible

paragraph \<open>Simulation relations in the presence of scope opening\<close>

text \<open>
  \<^item> Definition for the basic transition system:

      \<^item> \<^bold>\<open>Lifting\<close>, which turns relations on processes into relations on residuals:

          \<^item> Acting case:@{lemma [display]
            \<open>\<X> p q \<Longrightarrow> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> p) (\<lbrace>\<alpha>\<rbrace> q)\<close>
            by (blast intro: acting_lift)}

          \<^item> Opening case:@{lemma [display]
            \<open>(\<And>a. \<X> (P a) (Q a)) \<Longrightarrow> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> Q a)\<close>
            by (blast intro: opening_lift)}

      \<^item> Simulation relations:@{lemma [display, source]
        "basic.sim \<X> \<longleftrightarrow>\<^latex>\<open>\\\<close>(\<forall>p q c. \<X> p q \<and> p \<rightarrow>\<^sub>\<flat> c \<longrightarrow> (\<exists>d. q \<rightarrow>\<^sub>\<flat> d \<and> basic_lift \<X> c d))"
        by blast}

  \<^item> Definition for the proper transition system:

      \<^item> Lifting: \<^bold>\<open>analogous\<close>

      \<^item> Simulation relations: \<^bold>\<open>identical\<close>\\
        (apart from the use of a different lifting operation)
\<close>

paragraph \<open>Dealing with different kinds of residuals\<close>

text \<open>
  \<^item> Problem: different lifting operations for different kinds of residuals

  \<^item> Our solution:

      \<^item> Describe abstractly what a lifting operation is,\\
        using an axiomatically defined algebraic structure

      \<^item> Define simulation relations and derived concepts\\
        solely in terms of a lifting operation

  \<^item> Strength of this approach:

      \<^item> Covers not only the two transition systems of the \<open>\<natural>\<close>-calculus\\
        but also transition systems of other process calculi

      \<^item> Covers also transition systems \<^bold>\<open>without\<close> scope opening
\<close>

section \<open>Residuals axiomatically\<close>

subsection \<open>Residuals in general\<close>

context %invisible residual begin

paragraph \<open>Lifting operations\<close>

text \<open>
  \<^item> Intuition behind \<^term>\<open>lift \<X>\<close>:

      \<^item> Labels must be equal

      \<^item> Target processes must be related by \<^term>\<open>\<X>\<close>

  \<^item> Axioms that are in line with this intuition:

      \<^item> Monotonicity:@{lemma [display]
        \<open>\<X> \<le> \<Y> \<Longrightarrow> lift \<X> \<le> lift \<Y>\<close>
        by (fact lift_monotonicity)}

      \<^item> Equality preservation:@{lemma [display]
        \<open>lift (=) = (=)\<close>
        by (fact lift_equality_preservation)}

      \<^item> Composition preservation:@{lemma [display]
        \<open>lift (\<X> OO \<Y>) = lift \<X> OO lift \<Y>\<close>
        by (fact lift_composition_preservation)}

      \<^item> Conversion preservation:@{lemma [display]
        \<open>lift \<X>\<inverse>\<inverse> = (lift \<X>)\<inverse>\<inverse>\<close>
        by (fact lift_conversion_preservation)}
\<close>

paragraph \<open>The name of the game\<close>

text \<open>
  \<^item> Residual structures are \<^bold>\<open>functors\<close> of a specific kind\\
    (because of equality preservation and composition preservation)

      \<^item> \<^bold>\<open>Not\<close> endofunctors on the category of types and \<^bold>\<open>functions\<close>\\
        (functors in the Haskell sense)

      \<^item> \<^bold>\<open>But\<close> endofunctors on the category of types and \<^bold>\<open>relations\<close>

  \<^item> Residual structures are the same as \<^bold>\<open>relators\<close>

  \<^item> Isabelle/HOL automatically generates relator-specific things\\for every data type

      \<^item> The lifting operation

      \<^item> Facts about the lifting operation, including the instances of the axioms
\<close>

end %invisible

subsection \<open>Weak residuals\<close>

no_notation %invisible proper_transition ("_ \<rightarrow>\<^sub>\<sharp>_" [51, 51] 50)
notation %invisible proper_transition ("_ \<rightarrow>_" [51, 51] 50)

no_notation %invisible proper.weak_transition (infix "\<Rightarrow>\<^sub>\<sharp>" 50)
notation %invisible proper.weak_transition ("_ \<Rightarrow>_" [51, 51] 50)

abbreviation %invisible
  silent_transition_closure :: "process \<Rightarrow> process \<Rightarrow> bool"
  (infix "\<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>*" 50)
where
  "(\<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>*) \<equiv> (\<lambda>s t. s \<rightarrow>\<lparr>\<tau>\<rparr> t)\<^sup>*\<^sup>*"

paragraph \<open>Weak bisimilarity\<close>

lemma %invisible silent_weak_transition_def:
  shows "p \<Rightarrow>\<lparr>\<tau>\<rparr> q \<longleftrightarrow> p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
proof
  assume "p \<Rightarrow>\<lparr>\<tau>\<rparr> q"
  then show "p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
  proof (induction p "\<lparr>\<tau>\<rparr> q" arbitrary: q)
    case strong_transition
    then show ?case
      by (rule r_into_rtranclp)
  next
    case silent_transition
    then show ?case
      by (blast elim: proper_silent.cases)
  next
    case (composed_transition p _ q)
    then obtain u where "p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* u" and "u \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
      by (blast elim: proper_silent.cases proper_lift_cases)
    then show ?case
      by (rule rtranclp_trans)
  qed
next
  assume "p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
  then show "p \<Rightarrow>\<lparr>\<tau>\<rparr> q"
  proof induction
    case base
    then show ?case
      by (blast intro: proper_internal_is_silent proper.silent_transition)
  next
    case step
    then show ?case
      by (blast intro:
        proper.strong_transition
        proper_internal_is_silent
        proper.composed_transition)
  qed
qed

lemma %invisible observable_weak_transition_def:
  fixes \<xi> :: proper_action
  assumes "\<xi> \<noteq> \<tau>"
  shows "p \<Rightarrow>\<lparr>\<xi>\<rparr> q \<longleftrightarrow> (\<exists>s t. p \<Rightarrow>\<lparr>\<tau>\<rparr> s \<and> s \<rightarrow>\<lparr>\<xi>\<rparr> t \<and> t \<Rightarrow>\<lparr>\<tau>\<rparr> q)"
proof
  assume "p \<Rightarrow>\<lparr>\<xi>\<rparr> q"
  then show "\<exists>s t. p \<Rightarrow>\<lparr>\<tau>\<rparr> s \<and> s \<rightarrow>\<lparr>\<xi>\<rparr> t \<and> t \<Rightarrow>\<lparr>\<tau>\<rparr> q"
  proof (induction p "\<lparr>\<xi>\<rparr> q" arbitrary: q)
    case strong_transition
    then show ?case
      by (blast intro: proper_internal_is_silent proper.silent_transition)
  next
    case silent_transition
    with \<open>\<xi> \<noteq> \<tau>\<close> show ?case
      by (blast elim: proper_silent.cases)
  next
    case (composed_transition p _ q)
    then consider
      u and s and t where "p \<Rightarrow>\<lparr>\<tau>\<rparr> u" and "u \<Rightarrow>\<lparr>\<tau>\<rparr> s" and "s \<rightarrow>\<lparr>\<xi>\<rparr> t" and "t \<Rightarrow>\<lparr>\<tau>\<rparr> q" |
      s and t and u where "p \<Rightarrow>\<lparr>\<tau>\<rparr> s" and "s \<rightarrow>\<lparr>\<xi>\<rparr> t" and "t \<Rightarrow>\<lparr>\<tau>\<rparr> u" and "u \<Rightarrow> \<lparr>\<tau>\<rparr> q"
      by (blast elim: proper_silent.cases proper_lift_cases)
    then show ?case
      by cases (blast intro: proper_internal_is_silent proper.composed_transition)+
  qed
next
  assume "\<exists>s t. p \<Rightarrow>\<lparr>\<tau>\<rparr> s \<and> s \<rightarrow>\<lparr>\<xi>\<rparr> t \<and> t \<Rightarrow>\<lparr>\<tau>\<rparr> q"
  then show "p \<Rightarrow>\<lparr>\<xi>\<rparr> q"
    by (fastforce intro:
      proper_internal_is_silent
      proper.strong_transition
      proper.composed_transition)
qed

text \<open>
  \<^item> \<^bold>\<open>Weak bisimilarity\<close> treats internal communication as \<^bold>\<open>silent\<close> and ignores it

  \<^item> Elegant definition:

      \<^item> Weak transitions:

          \<^item> Silent:@{lemma [display, source]
            "p \<Rightarrow>\<lparr>\<tau>\<rparr> q \<longleftrightarrow> p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
            by (fact silent_weak_transition_def)}

          \<^item> Observable:@{lemma [display, source]
            "\<xi> \<noteq> \<tau> \<Longrightarrow>\<^latex>\<open>\\\<close>p \<Rightarrow>\<lparr>\<xi>\<rparr> q \<longleftrightarrow> (\<exists>s t. p \<Rightarrow>\<lparr>\<tau>\<rparr> s \<and> s \<rightarrow>\<lparr>\<xi>\<rparr> t \<and> t \<Rightarrow>\<lparr>\<tau>\<rparr> q)"
            by (fact observable_weak_transition_def)}

      \<^item> Weak bisimilarity: bisimilarity of the weak transition system

  \<^item> The standard definition of weak transitions\\
    is not appropriate for our residual-based approach,\\
    because it refers to a \<^bold>\<open>dedicated silent label\<close>
\<close>

no_notation %invisible proper_transition ("_ \<rightarrow>_" [51, 51] 50)
notation %invisible proper_transition ("_ \<rightarrow>\<^sub>\<sharp>_" [51, 51] 50)

no_notation %invisible proper.weak_transition ("_ \<Rightarrow>_" [51, 51] 50)
notation %invisible proper.weak_transition ("_ \<Rightarrow>\<^sub>\<sharp>_" [51, 51] 50)

definition %invisible
  basic_fuse :: "'p basic_residual basic_residual \<Rightarrow> 'p basic_residual \<Rightarrow> bool"
where
  "basic_fuse = basic_silent\<inverse>\<inverse> \<squnion> basic_lift basic_silent\<inverse>\<inverse>"

(* A version of \<^theory_text>\<open>basic.silent_converse_naturality\<close> with a more general type *)
lemma %invisible basic_silent_converse_naturality:
  shows "basic_silent\<inverse>\<inverse> OO \<X> = basic_lift \<X> OO basic_silent\<inverse>\<inverse>"
  by (blast
    elim: basic_silent.cases basic_lift_cases
    intro: basic_internal_is_silent basic_lift_intros)

lemma %invisible basic_absorb_from_fuse:
  shows "basic.absorb \<I> = basic_lift \<I> OO basic_fuse"
  unfolding basic_fuse_def
  by (simp add: basic_silent_converse_naturality basic_residual.rel_compp)

paragraph \<open>Relations that identify silence\<close>

text \<open>
  \<^item> Definitions for the basic transition system:

      \<^item> Silence introduction:@{lemma [display]
        \<open>basic_silent p (\<lbrace>\<tau>\<rbrace> p)\<close>
        by (fact basic_internal_is_silent)}

      \<^item> Silence absorption:

          \<^item> Silent--acting case:@{lemma [display, source]
            "basic_fuse (\<lbrace>\<tau>\<rbrace>\<lbrace>\<alpha>\<rbrace> p) (\<lbrace>\<alpha>\<rbrace> p)"
            by (unfold basic_fuse_def, blast intro: basic_internal_is_silent)}

          \<^item> Silent--opening case:@{lemma [display, source]
            "basic_fuse (\<lbrace>\<tau>\<rbrace>\<lbrace>\<nu> a\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> P a)"
            by (unfold basic_fuse_def, blast intro: basic_internal_is_silent)}

          \<^item> Acting--silent case:@{lemma [display, source]
            "basic_fuse (\<lbrace>\<alpha>\<rbrace>\<lbrace>\<tau>\<rbrace> p) (\<lbrace>\<alpha>\<rbrace> p)"
            by (unfold basic_fuse_def, blast intro: basic_internal_is_silent basic_lift_intros)}

          \<^item> Opening--silent case:@{lemma [display, source]
            "basic_fuse (\<lbrace>\<nu> a\<rbrace>\<lbrace>\<tau>\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> P a)"
            by (unfold basic_fuse_def, blast intro: basic_internal_is_silent basic_lift_intros)}

  \<^item> Definitions for the proper transition system: analogous
\<close>

no_notation %invisible basic_transition ("_ \<rightarrow>\<^sub>\<flat>_" [51, 51] 50)
notation %invisible basic_transition (infix "\<rightarrow>\<^sub>\<flat>" 50)

paragraph \<open>Weak transitions in the presence of scope opening\<close>

text \<open>
  \<^item> Definition for the basic transition system:

      \<^item> Strong transitions:@{lemma [display]
        \<open>p \<rightarrow>\<^sub>\<flat> c \<Longrightarrow> p \<Rightarrow>\<^sub>\<flat> c\<close>
        by (fact basic.strong_transition)}

      \<^item> Empty transitions:@{lemma [display]
        \<open>basic_silent p c \<Longrightarrow> p \<Rightarrow>\<^sub>\<flat> c\<close>
        by (fact basic.silent_transition)}

      \<^item> Compound transitions:@{lemma [display]
        \<open>\<lbrakk>p \<Rightarrow>\<^sub>\<flat> c; basic_lift (\<Rightarrow>\<^sub>\<flat>) c z; basic_fuse z d\<rbrakk> \<Longrightarrow> p \<Rightarrow>\<^sub>\<flat> d\<close>
        by (rule basic.composed_transition, auto simp add: basic_absorb_from_fuse)}

  \<^item> Definition for the proper transition system: identical\\
    (apart from the use of different relations that identify silence)
\<close>

(*
  From now on, we work with seemingly generic operations \<open>lift\<close>, \<open>silent\<close>, and \<open>fuse\<close> that are in
  fact the concrete entities for the basic transition system. The reasons are as follows:

    \<^item> There cannot be a generic \<open>fuse\<close> (because Isabelle does not support higher-kinded types).

    \<^item> As a consequence of the former, there cannot be generic proofs involving \<open>fuse\<close> (we conduct
      the proofs for the basic transition instead, which gives us at least \<^emph>\<open>some\<close> assurance.
*)

notation %invisible basic_lift ("lift")

notation %invisible basic_silent ("silent")

notation %invisible basic_fuse ("fuse")

paragraph \<open>Silence-identifying relations axiomatically\<close>

text \<open>
  \<^item> Intuitions:

      \<^item> Intuition behind \<^term>\<open>silent\<close>: a silent label is added

      \<^item> Intuition behind \<^term>\<open>fuse\<close>:

          \<^item> An outer silent label is removed

          \<^item> An inner silent label is removed

          \<^item> A nested residual with no silent labels is dropped

  \<^item> Axioms that are in line with these intuitions:

      \<^item> Left-neutrality:@{lemma [display]
        \<open>silent OO fuse = (=)\<close>
        by (
          unfold basic_fuse_def,
          blast elim: basic_silent.cases basic_lift_cases intro: basic_internal_is_silent
        )}

      \<^item> Right-neutrality:@{lemma [display]
        \<open>lift silent OO fuse = (=)\<close>
        by (fold basic_absorb_from_fuse, fact basic.right_neutrality)}

      \<^item> Associativity:@{lemma [display]
        \<open>fuse OO fuse = lift fuse OO fuse\<close>
        by (
          unfold basic_fuse_def,
          simp add:
            basic_residual.rel_compp [symmetric]
            basic_silent_converse_naturality [symmetric]
            sup_assoc
            sup_commute
            sup_left_commute
        )}

  \<^item> Residual structures with a notion of silence are \<^bold>\<open>monads\<close>\\
    on the category of types and relations
\<close>

paragraph \<open>Strengths of the monadic approach to silence\<close>

text \<open>
  \<^item> More general than the traditional approach\\
    (for example, multiple silent labels are possible)

  \<^item> Expected properties of weak bisimilarity can be proved generically
    (despite the additional generality)

      \<^item> Weak bisimilarity is the same as ``mixed'' bisimilarity

      \<^item> Strong bisimilarity is included in weak bisimilarity

  \<^item> Enforces an elegant definition of weak transitions

      \<^item> Distinction between silent and observable labels\\
        is pushed into the definitions of concrete \<^term>\<open>silent\<close> and \<^term>\<open>fuse\<close> relations

      \<^item> As a result, generic proofs tend to be simple
\<close>

end %invisible
