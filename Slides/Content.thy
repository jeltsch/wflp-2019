theory %invisible Content
  imports Chi_Calculus.Proper_Transition_System
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

  \<^item> Receive value \<open>x\<close> from channel \<open>a\<close> and continue with \<^term>\<open>P x\<close>:@{term [display, source]
    "a \<triangleright> x. P x"}

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
        \<open>a \<triangleleft> x \<rightarrow>\<lparr>a \<triangleleft> x\<rparr> \<zero>\<close> by (blast intro: sending output_without_opening)}

      \<^item> Receiving:@{lemma [display, source]
        "a \<triangleright> x. P x \<rightarrow>\<lparr>a \<triangleright> x\<rparr> P x" by (fastforce intro: receiving simple)}

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

      \<^item> Opening:@{lemma [display, source]
        "\<nu> a. P a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a"
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

      \<^item> Basic transition system:@{term [display, source] "\<lbrace>\<nu> a\<rbrace> P a"}

      \<^item> Proper transition system:@{text [display] \<open>\<lparr>a \<triangleleft> \<nu> b\<^sub>1 \<dots> b\<^sub>n. f b\<^sub>1 \<dots> b\<^sub>n\<rparr> P b\<^sub>1 \<dots> b\<^sub>n\<close>}

  \<^item> We bundle labels and target processes, leading to \<^bold>\<open>residuals\<close>

    \<^item> Basic transition system:

        \<^item> Acting:@{lemma [display, source] "Acting \<alpha> p \<equiv> \<lbrace>\<alpha>\<rbrace> p" by (fact reflexive)}

        \<^item> Opening:@{lemma [display, source] "Opening P \<equiv> \<lbrace>\<nu> a\<rbrace> P a" by (fact reflexive)}

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

          \<^item> Opening case:@{lemma [display, source]
            "(\<And>a. \<X> (P a) (Q a)) \<Longrightarrow> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> Q a)"
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

      \<^item> Describe abstractly what a lifting operation is\\
        (using an axiomatically defined algebraic structure)

      \<^item> Define simulation relations and derived concepts\\
        solely in terms of a lifting operation

  \<^item> Strength of this approach:

      \<^item> Covers not only the two transition systems of the \<open>\<natural>\<close>-calculus\\
        but also transition systems of other process calculi

      \<^item> Covers also transition systems \<^bold>\<open>without\<close> scope opening
\<close>

end %invisible
