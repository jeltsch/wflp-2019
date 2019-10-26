theory %invisible Content
  imports Chi_Calculus.Proper_Transition_System
begin

section \<open>Introduction\<close>

text \<open>
  This paper has been produced from documented Isabelle source
  code~@{cite "jeltsch:wflp-2019-source"}, which has been checked with Isabelle2018.
\<close>

section \<open>The \<open>\<natural>\<close>-Calculus\<close>

text \<open>
  The \<open>\<natural>\<close>-calculus is a process calculus in the tradition of the
  \<open>\<pi>\<close>-calculus~@{cite "milner:pi-calculus"}. It is not tied to blockchains in any way but is a
  universal language for concurrent and distributed computing.

  Unlike the \<open>\<pi>\<close>-calculus, the \<open>\<natural>\<close>-calculus is not an isolated language but is embedded into
  functional host languages. In our application scenario, we use embeddings into both Haskell, for
  execution, and Isabelle/HOL, for verification. The user is expected to write programs as
  Haskell-embedded process calculus terms, which can then be turned automatically into
  Isabelle-embedded process calculus terms to make them available for verification. In this paper,
  we focus on the Isabelle embedding, leaving the discussion of the Haskell embedding for another
  time. Whenever we use the term ``\<open>\<natural>\<close>-calculus'', we refer to either the calculus in general or its
  embedding into Isabelle/HOL.

  Our embedding technique uses higher-order abstract syntax (HOAS)~@{cite "pfenning:pldi-1988"},
  which means we represent binding of names using functions of the host language. An immediate
  consequence of this is that the host language is dealing with all the issues regarding names, like
  shadowing and \<open>\<alpha>\<close>-equivalence, which simplifies the implementation of the calculus. Furthermore,
  HOAS gives us support for arbitrary data for free, since we can easily represent data by values of
  the host language. This lifts the restriction of the \<open>\<pi>\<close>-calculus that channels are the only kind
  of data. Finally, HOAS allows us to move computation, branching, and recursion to the host
  language level and thus further simplify the implementation of the calculus.

  The \<open>\<natural>\<close>-calculus is similar to \<open>\<psi>\<close>-calculi~@{cite "bengtson:lmcs-7-1"} in that it adds support for
  arbitrary data to the core features of the \<open>\<pi>\<close>-calculus. However, since the \<open>\<natural>\<close>-calculus uses
  HOAS, we can avoid much of the complexity of \<open>\<psi>\<close>-calculi that comes from their need to cope with
  data-related issues themselves.
\<close>

subsection \<open>Language\<close>

text \<open>
  We define a coinductive data type \<^type>\<open>process\<close> whose values are the terms of the \<open>\<natural>\<close>-calculus.
  We call these terms simply \<^emph>\<open>processes\<close>.

  In the following, we list the different kinds of processes. For describing their syntax, we use
  statements of the form \<open>C x\<^sub>1 \<dots> x\<^sub>n \<equiv> e\<close>. The left-hand side of such a statement is an application
  of a data constructor of the \<^type>\<open>process\<close> type to argument variables; it showcases the ordinary
  notation for the respective kind of process. The right-hand side is a term that is equal to the
  left-hand side but uses convenient notation introduced by us using Isabelle's means for defining
  custom syntax. The kinds of processes are as follows:

    \<^item> Do nothing:@{lemma [display, source]
      "Stop \<equiv> \<zero>"
      by (fact reflexive)}

    \<^item> Send value~\<open>x\<close> to channel~\<open>a\<close>:@{lemma [display, source]
      "Send a x \<equiv> a \<triangleleft> x"
      by (fact reflexive)}

    \<^item> Receive value~\<open>x\<close> from channel~\<open>a\<close> and continue with \<^term>\<open>P x\<close>:@{lemma [display, source]
      "Receive a P \<equiv> a \<triangleright> x. P x"
      by (fact reflexive)}

    \<^item> Perform processes \<open>p\<close> and~\<open>q\<close> concurrently:@{lemma [display, source]
      "Parallel p q \<equiv> p \<parallel> q"
      by (fact reflexive)}

    \<^item> Create a new channel~\<open>a\<close> and continue with \<^term>\<open>P a\<close>:@{lemma [display, source]
      "NewChannel P \<equiv> \<nu> a. P a"
      by (fact reflexive)}

  \<^noindent> The binders (\<open>\<triangleleft>\<close>~and~\<open>\<nu>\<close>) bind stronger than the infix operator~(\<open>\<parallel>\<close>), which is not what the
  reader might have expected but is typical for process calculi.

  There are a few interesting points to note regarding processes and their notation:

    \<^item> Our use of HOAS manifests itself in the \<^const>\<open>Receive\<close> and \<^const>\<open>NewChannel\<close> cases. In both
      of them, the respective data constructor takes an argument \<^term>\<open>P\<close> that is a continuation
      which maps a received value or a newly created channel to a remainder process.

    \<^item> Although dependencies on received values and newly created channels are encoded using
      functions, we can still use convenient binder notation for \<^const>\<open>Receive\<close> and
      \<^const>\<open>NewChannel\<close> processes. A term~\<^term>\<open>e\<close> in \<^term>\<open>a \<triangleright> x. e\<close> or \<^term>\<open>\<nu> a. e :: process\<close>
      does not have to be an application of a function~\<^term>\<open>P\<close> to the bound variable. Every term
      that possibly mentions the bound variable is fine. For example, \<^term>\<open>a \<triangleright> x. b \<triangleleft> x\<close> is a valid
      term, which is equal to @{term [source] "Receive a (\<lambda>x. b \<triangleleft> x)"}.

    \<^item> HOAS gives us the opportunity to construct processes that include computation and branching,
      although we do not have special process calculus constructs for these things. For example, the
      process @{term [source] "a \<triangleright> y. (if y \<noteq> x then b \<triangleleft> y else \<zero>)"}, which performs a kind of
      conditional forwarding, carries the inequality test and the branching inside the continuation
      argument of \<^const>\<open>Receive\<close>.

    \<^item> @{const [source] "Send"} does not have a continuation argument. This is to make communication
      effectively asynchronous. The operational semantics defines communication in the usual way,
      making it actually synchronous, but without @{const [source] "Send"} continuations, synchrony
      cannot be observed. This approach is common for asynchronous process calculi and is used, for
      example, in the asynchronous \<open>\<pi>\<close>-calculus~@{cite "boudol:inria-00076939"}. We use asynchronous
      communication, because it is sufficient for our use case and easier to implement in common
      programming languages, like Haskell.

    \<^item> The \<open>\<natural>\<close>-calculus does not have a construct for nondeterministic choice, because execution of
      nondeterministic choice is difficult to implement.

    \<^item> The \<open>\<natural>\<close>-calculus does not have a construct for replication. We do not need such a construct,
      since the \<^type>\<open>process\<close> type is coinductive and thus allows us to form infinite terms. The
      replication of a process~\<open>p\<close> can be defined as the infinite term \<open>p \<parallel> p \<parallel> \<dots>\<close>, that is, the
      single term \<open>p\<^sup>\<infinity>\<close> for which \<open>p\<^sup>\<infinity> = p \<parallel> p\<^sup>\<infinity>\<close>.
\<close>

subsection \<open>Operational Semantics\<close>

text_raw \<open>\label{operational-semantics}\<close>

no_notation %invisible proper_transition (infix "\<rightarrow>\<^sub>\<sharp>" 50)
notation %invisible proper_transition ("_ \<rightarrow>_" [51, 51] 50)

text \<open>
  We define the operational semantics of the \<open>\<natural>\<close>-calculus as a labeled transition system. We write
  \<^term>\<open>p \<rightarrow>\<lparr>\<xi>\<rparr> q\<close> to say that \<^term>\<open>p\<close> can transition to~\<^term>\<open>q\<close> with label~\<^term>\<open>\<xi>\<close>.

  We handle isolated sending and receiving as well as communication in the standard manner. We
  introduce labels \<^term>\<open>a \<triangleleft> x :: basic_action\<close>, \<^term>\<open>a \<triangleright> x :: proper_action\<close>, and
  \<^term>\<open>\<tau> :: proper_action\<close>, which denote sending of a value~\<^term>\<open>x\<close> to a channel~\<^term>\<open>a\<close>,
  receiving of a value~\<^term>\<open>x\<close> from a channel~\<^term>\<open>a\<close>, and internal communication, respectively,
  and call these labels \<^emph>\<open>actions\<close>. Then we introduce the following rules:

    \<^item> Sending:@{lemma [display]
      \<open>a \<triangleleft> x \<rightarrow>\<lparr>a \<triangleleft> x\<rparr> \<zero>\<close>
      by (blast intro: sending output_without_opening)}

    \<^item> Receiving:@{lemma [display]
      \<open>a \<triangleright> x. P x \<rightarrow>\<lparr>a \<triangleright> x\<rparr> P x\<close>
      by (fastforce intro: receiving simple)}

    \<^item> Communication:@{lemma [display]
      \<open>\<lbrakk>p \<rightarrow>\<lparr>a \<triangleleft> x\<rparr> p'; q \<rightarrow>\<lparr>a \<triangleright> x\<rparr> q'\<rbrakk> \<Longrightarrow> p \<parallel> q \<rightarrow>\<lparr>\<tau>\<rparr> p' \<parallel> q'\<close>
      by (fastforce elim: proper_transition.cases intro: ltr communication simple)}

    \<^item> Acting within a subsystem:@{lemma [display]
      \<open>p \<rightarrow>\<lparr>\<xi>\<rparr> p' \<Longrightarrow> p \<parallel> q \<rightarrow>\<lparr>\<xi>\<rparr> p' \<parallel> q\<close>
      by (blast elim: proper_transition.cases intro: acting_left simple)}

  \<^noindent> The last two of these rules have symmetric versions, which we do not show here for the sake of
  simplicity.
\<close>

axiomatization %invisible chan_to_val :: "chan \<Rightarrow> val" ("\<cent>_")
text_raw \<open>\renewcommand{\isasymcent}{}\<close>

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
  Channels created by \<^const>\<open>NewChannel\<close> are initially local. However, such channels can later be
  made visible by sending them to other subsystems. Let us see how this is captured by the
  transition system of the \<open>\<pi>\<close>-calculus. Besides ordinary sending labels
  \<^term>\<open>a \<triangleleft> b :: basic_action\<close>, the \<open>\<pi>\<close>-calculus has labels \<open>a \<triangleleft> \<nu> b. b\<close> that additionally
  bind the variable~\<^term>\<open>b\<close>. The bound variable denotes a channel not yet known to the outside.
  Using it as the value being sent thus conveys the information that a local channel is being
  published by sending it to~\<^term>\<open>a\<close>. When used as part of a transition statement, the scope of the
  binder includes the target process, so that the target process can depend on the published
  channel. Therefore, the general form of a transition statement with local channel publication is
  \<^term>\<open>p \<rightarrow>\<lparr>a \<triangleleft> \<nu> b. \<cent>b\<rparr> Q b\<close>. The \<open>\<pi>\<close>-calculus contains the following rules to deal with local
  channels:

    \<^item> Scope opening:@{lemma [display]
      \<open>(\<And>b. P b \<rightarrow>\<lparr>a \<triangleleft> \<cent>b\<rparr> Q b) \<Longrightarrow> \<nu> b. P b \<rightarrow>\<lparr>a \<triangleleft> \<nu> b. \<cent>b\<rparr> Q b\<close>
      by (blast intro: opening output_with_opening)}

    \<^item> Communication with scope closing:@{lemma [display]
      \<open>\<lbrakk>p \<rightarrow>\<lparr>a \<triangleleft> \<nu> b. \<cent>b\<rparr> P b; \<And>b. q \<rightarrow>\<lparr>a \<triangleright> \<cent>b\<rparr> Q b\<rbrakk> \<Longrightarrow> p \<parallel> q \<rightarrow>\<lparr>\<tau>\<rparr> \<nu> b. (P b \<parallel> Q b)\<close>
      by (fact pi_calculus_closing)}

    \<^item> Acting inside scope:@{lemma [display]
      \<open>(\<And>a. P a \<rightarrow>\<lparr>\<delta>\<rparr> Q a) \<Longrightarrow> \<nu> a. P a \<rightarrow>\<lparr>\<delta>\<rparr> \<nu> a. Q a\<close>
      by (blast elim: proper_transition.cases intro: acting_scope simple)}

  For the \<open>\<natural>\<close>-calculus, these rules are unfortunately not enough. Unlike the \<open>\<pi>\<close>-calculus, the
  \<open>\<natural>\<close>-calculus permits arbitrary data to be sent, which includes values that contain several
  channels, like pairs of channels and lists of channels. As a result, several local channels can be
  published at once. Variants of the above rules that account for this possibility are complex and
  hard to get right. The complexity has two reasons:

    \<^item> Some labels deal with multiple concepts, namely scope opening and sending. In the
      \<open>\<natural>\<close>-calculus, these labels are not always of the relatively simple form \<open>a \<triangleleft> \<nu> b. b\<close> discussed
      above, but generally of the more complex form \<open>\<nu> b\<^sub>1 \<dots> b\<^sub>n. a \<triangleleft> f b\<^sub>1 \<dots> b\<^sub>n\<close>, because arbitrary
      values depending on multiple local channels can be sent.

    \<^item> Some rules deal with multiple concepts, namely the rule about communication with scope
      closing, which deals with precisely these two things, and the rule about acting inside scope,
      which essentially adds scope opening before and scope closing after the given action.
\<close>

no_notation %invisible basic_transition (infix "\<rightarrow>\<^sub>\<flat>" 50)
notation %invisible basic_transition ("_ \<rightarrow>\<^sub>\<flat>_" [51, 51] 50)

no_notation %invisible proper_transition ("_ \<rightarrow>_" [51, 51] 50)
notation %invisible proper_transition ("_ \<rightarrow>\<^sub>\<sharp>_" [51, 51] 50)

text \<open>
  To tame this complexity, we conduct the definition of the transition system in two steps:

    \<^enum> We define a transition system that uses distinct transitions for opening scopes, so that each
      label and each rule deals with a single concept only. We call this transition system the
      \<^emph>\<open>basic transition system\<close> and write a transition in this system \<^term>\<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<xi>\<rbrace> q\<close>.

    \<^enum> We define the transition system that describes the actual semantics of the \<open>\<natural>\<close>-calculus by
      adding a layer on top of the basic transition system that bundles scope opening and sending
      transitions. We call this transition system the \<^emph>\<open>proper transition system\<close> and write a
      transition in this system \<^term>\<open>p \<rightarrow>\<^sub>\<sharp>\<lparr>\<xi>\<rparr> q\<close>.

  The basic transition system has \<^emph>\<open>action labels\<close> \<^term>\<open>a \<triangleleft> x :: basic_action\<close>,
  \<^term>\<open>a \<triangleright> x :: basic_action\<close>, and \<^term>\<open>\<tau> :: basic_action\<close> as well as \<^emph>\<open>opening labels\<close>~\<open>\<nu> a\<close>,
  which bind their variables in any following target process. Its rules for sending, receiving, and
  communication are the ones we have seen at the beginning of \hyperref[operational-semantics]{this
  subsection}. For dealing with local channels, the basic transition system contains the following
  rules:

    \<^item> Scope opening:@{lemma [display]
      \<open>\<nu> a. P a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close>
      by (fact opening)}

    \<^item> Scope closing after acting:@{lemma [display]
      \<open>\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R a\<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. R a\<close>
      by (fact scoped_acting)}

    \<^item> Scope closing after another scope opening:@{lemma [display]
      \<open>\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> R a b\<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. R a b\<close>
      by (fact scoped_opening)}

    \<^item> Scope opening within a subsystem:@{lemma [display]
      \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<Longrightarrow> p \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<parallel> q\<close>
      by (fact opening_left)}

  \<^noindent> The last rule has a symmetric version, which we do not show here for the sake of simplicity.

  The proper transition system has labels \<^term>\<open>a \<triangleright> x :: proper_action\<close>, \<^term>\<open>\<tau> :: proper_action\<close>,
  and \<open>a \<triangleleft> \<nu> b\<^sub>1 \<dots> b\<^sub>n. f b\<^sub>1 \<dots> b\<^sub>n\<close>, which bind their variables also in any following target process.
  Its rules for sending, receiving, and communication just refer to the basic transition system:

    \<^item> Sending:@{lemma [display]
      \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q\<close>
      by (blast intro: output_without_opening)}

    \<^item> Receiving:@{lemma [display]
      \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleright> x\<rparr> q\<close>
      by (auto intro: simple)}

    \<^item> Communication:@{lemma [display]
      \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<tau>\<rparr> q\<close>
      by (auto intro: simple)}

  \<^noindent> For scope opening, we have a series of facts, one for each number of published channels. The
  facts for one and two published channels are as follows:

    \<^item> One channel:@{lemma [display]
      \<open>\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P b; \<And>b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> f b\<rparr> Q b\<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. f b\<rparr> Q b\<close>
      by (fact output_with_opening)}

    \<^item> Two channels:@{lemma [display, source]
      "\<lbrakk>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> P b; \<And>b. P b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> c. f b c\<rparr> Q b c\<rbrakk> \<Longrightarrow>\<^latex>\<open>\\\<close>p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b c. f b c\<rparr> Q b c"
      by (fact output_with_opening)}

  \<^noindent> The facts for more published channels are analogous. All of these facts can be captured by a
  single rule, which we do not show here for the sake of simplicity.

  As it stands, the proper transition system has the issue that a scope can also be opened when the
  respective channel is actually not published. For example, @{lemma\<open>\<nu> b. a \<triangleleft> x \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. x\<rparr> \<zero>\<close> by
  (blast intro: opening sending output_without_opening output_with_opening)} is a possible
  transition. We are currently investigating ways to fix this issue. That said, this issue is of
  little relevance for the rest of this paper, where we discuss the effects of transitions involving
  scope opening in a way that is largely independent of the particularities of a concrete transition
  system.

  A key issue with both the basic and the proper transition system is that, whenever a label
  contains a binder, the scope of this binder includes any following target process. As a result, we
  can treat neither of the two transition relations as a ternary relation, where source processes,
  labels, and target processes are separate entities. As a solution, we treat the combination of a
  label and an associated target process as a single entity, which we call a \<^emph>\<open>residual\<close>. Our
  transition relation then become binary, relating source processes and residuals. This approach has
  been taken in \<open>\<psi>\<close>-calculi, for example.

  We define an inductive data type \<^type>\<open>basic_residual\<close> whose values are the residuals of the basic
  transition system. There are two kinds of such residuals:

    \<^item> Acting:@{lemma [display, source]
      "Acting \<alpha> p \<equiv> \<lbrace>\<alpha>\<rbrace> p"
      by (fact reflexive)}

    \<^item> Opening:@{lemma [display, source]
      "Opening P \<equiv> \<lbrace>\<nu> a\<rbrace> P a"
      by (fact reflexive)}

  \<^noindent> Note that in the \<open>Opening\<close> case we use HOAS and binder notation again.

  We also introduce an analogous data type \<^type>\<open>proper_residual\<close> for the proper transition system.
  The definition of \<^type>\<open>proper_residual\<close> is considerably more complex than the definition of
  \<^type>\<open>basic_residual\<close>, which is why we do not show it here. However, its general approach to
  capturing scope opening is the same.
\<close>

subsection \<open>Behavioral Equivalence\<close>

context %invisible transition_system begin

(*
  We prove the forward part of the first statement of the slide specialized to the proper transition
  system and restricted to simple transitions as a sanity check.
*)
lemma %invisible
  shows "proper.sim \<X> \<Longrightarrow> (\<forall>p q \<delta> p'. \<X> p q \<and> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> p' \<longrightarrow> (\<exists>q'. q \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q' \<and> \<X> p' q'))"
  by (blast elim: proper_lift_cases intro: simple_lift)

text \<open>
  Ultimately, we are interested in proving that different processes behave in the same or at least a
  similar way. The standard notion of behavioral equivalence is \<^emph>\<open>bisimilarity\<close>. A typical approach
  to define bisimilarity is the following one:

    \<^enum> We define the predicate \<^const>\<open>sim\<close> on binary relations between process as
      follows:@{text [display]
      \<open>sim \<X> \<longleftrightarrow>(\<forall>p q \<xi> p'. \<X> p q \<and> p \<rightarrow>\<lparr>\<xi>\<rparr> p' \<longrightarrow> (\<exists>q'. q \<rightarrow>\<lparr>\<xi>\<rparr> q' \<and> \<X> p' q'))\<close>}
      A relation \<^term>\<open>\<X>\<close> for which \<^term>\<open>sim \<X>\<close> holds is called a \<^emph>\<open>simulation relation\<close>.

    \<^enum> We define the predicate \<^const>\<open>bisim\<close> on binary relations between process as
      follows:@{lemma [display, source]
      "bisim \<X> \<longleftrightarrow> sim \<X> \<and> sim \<X>\<inverse>\<inverse>"
      by (fact refl)}
      A relation \<^term>\<open>\<X>\<close> for which \<^term>\<open>bisim \<X>\<close> holds is called a \<^emph>\<open>bisimulation relation\<close>.

    \<^enum> We define bisimilarity as the greatest bisimulation relation:@{lemma [display]
      \<open>(\<sim>) = (GREATEST \<X>. bisim \<X>)\<close>
      by (fact bisimilarity_is_greatest_bisimulation)}

  The above definition of \<^term>\<open>sim\<close> assumes each transition has exactly one target process and it
  refers to labels and target processes separately. This is a problem in the presence of scope
  opening, where labels and target processes have to be considered together and where a single
  transition may have different target processes depending on published channels.
\<close>

end %invisible

text \<open>
  Let us see how we can solve this problem for the basic transition system. We develop a definition
  of the notion of simulation relation that retains the essence of the above definition but is able
  to deal with the peculiarities of opening residuals. First, we define an operation
  \<^const>\<open>basic_lift\<close> that turns a relation between processes into a relation between basic
  residuals. The general idea is that \<^term>\<open>basic_lift \<X>\<close> relates two residuals if and only if their
  labels are the same and their target process are in relation~\<^term>\<open>\<X>\<close>. This idea can be tweaked in
  an obvious way to work with opening residuals. We define \<^const>\<open>basic_lift\<close> inductively using the
  following two rules:

    \<^item> Acting case:@{lemma [display]
      \<open>\<X> p q \<Longrightarrow> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> p) (\<lbrace>\<alpha>\<rbrace> q)\<close>
      by (blast intro: acting_lift)}

    \<^item> Opening case:@{lemma [display]
      \<open>(\<And>a. \<X> (P a) (Q a)) \<Longrightarrow> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> P a) (\<lbrace>\<nu> a\<rbrace> Q a)\<close>
      by (blast intro: opening_lift)}

  \<^noindent> Using \<^const>\<open>basic_lift\<close>, we define the notion of simulation relation for the basic transition
  system as follows:@{lemma [display, source]
  "basic.sim \<X> \<longleftrightarrow> (\<forall>p q c. \<X> p q \<and> p \<rightarrow>\<^sub>\<flat> c \<longrightarrow> (\<exists>d. q \<rightarrow>\<^sub>\<flat> d \<and> basic_lift \<X> c d))"
  by blast}

  For the proper transition system, we can define a lifting operation \<^const>\<open>proper_lift\<close> in an
  analogous way. Afterwards we can define the notion of simulation relation for the proper
  transition system in exactly the same way as for the basic transition system, except that we have
  to replace \<^const>\<open>basic_lift\<close> by \<^const>\<open>proper_lift\<close>.

  This observation suggests a way to build a generic theory of bisimilarity that applies to
  different transition systems, despite these transition systems using different kinds of residuals:
  We describe axiomatically what a lifting operation is and construct all definitions and proofs of
  our theory with reference to an arbitrary lifting operation that fulfills the respective axioms.
  To instantiate this generic theory for a concrete transition system, we just have to define a
  concrete lifting operation suitable for the kind of residuals this transition system uses and
  prove that this lifting operation has the necessary properties.

  Note that this approach not only allows for a common treatment of the basic and the proper
  transition system but also captures transition systems of other process calculi. In particular, it
  also works with transition systems that do not allow scope opening, like CCS~@{cite "milner:ccs"},
  as there is a trivial lifting operation for such systems.
\<close>

section \<open>Residuals Axiomatically\<close>

subsection \<open>Residuals in General\<close>

subsection \<open>Weak Residuals\<close>

subsection \<open>Normal Weak Residuals\<close>

section \<open>Related Work\<close>

section \<open>Summary and Outlook\<close>

end %invisible
