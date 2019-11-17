theory %invisible Content
  imports Chi_Calculus.Proper_Weak_Transition_System
begin

section \<open>Introduction\<close>

text \<open>
  A blockchain is an open, distributed database that stores a growing list, the \<^emph>\<open>ledger\<close>, and
  achieves security by employing advanced cryptographic methods. Blockchains are used in finance for
  implementing cryptocurrencies and smart contracts and have applications in other fields too.

  A blockchain system establishes data consistency using a \<^emph>\<open>consensus protocol\<close>. There are two
  kinds of consensus protocols:

    \<^item> \<^emph>\<open>Proof of work\<close> protocols require participants to solve computational puzzles in order to
      contribute data to the blockchain.

    \<^item> \<^emph>\<open>Proof of stake\<close> protocols make the opportunity to contribute data dependent on the stake
      participants possess, such as money in a cryptocurrency.

  Since the correctness of a blockchain system rests on the correctness of its consensus protocol,
  several projects are underway that apply formal methods to these protocols. One such project is
  carried out by a team of the Formal Methods Group at IOHK. This project, in which the author is
  involved, aims at a formally verified implementation of the Ouroboros family of consensus
  protocols~@{cite "kiayias:crypto-2017" and "david:eurocrypt-2018" and "badertscher:ccs-2018"},
  which form the backbone of the Cardano blockchain.

  All protocols in the Ouroboros family use the proof of stake mechanism and come with rigorous
  security guarantees. In fact, the original Ouroboros protocol, dubbed Ouroboros Classic, was the
  first proof-of-stake protocol to have such guarantees. The Cardano blockchain is the basis of the
  cryptocurrency Ada and the smart contract languages Plutus~@{cite "chakravarty:plutus"} and
  Marlowe~@{cite "lamela:isola-2018"}. Both Plutus and Marlowe are functional languages, but while
  Plutus is Turing-complete, Marlowe is deliberately restricted in its expressivity to make
  implementing common contracts easy.

  In this paper, we report on the first outcome of our formalization effort: the \<^emph>\<open>\<open>\<natural>\<close>-calculus\<close>
  (pronounced ``natural calculus''). The \<open>\<natural>\<close>-calculus is a process calculus that serves as our
  specification and implementation language. We make the following contributions:

    \<^item> In Sect.~\ref{the-natural-calculus}, we present the language and the operational semantics of
      the \<open>\<natural>\<close>-calculus. The latter is unique in that it uses a stack of two labeled transition
      systems to treat phenomena like data transfer and the opening and closing of channel scope in
      a modular fashion

    \<^item> The presence of multiple transition systems calls for a generic treatment of derived
      concurrency concepts such as strong and weak bisimilarity. In
      Sect.~\ref{residuals-axiomatically}, we develop an abstract theory of transition systems to
      achieve such a generic treatment. Our theory captures notions like scope opening and silent
      transitions using axiomatically defined algebraic structures. For these structures, functors
      and monads play a crucial role.

  \<^noindent> We conclude with Sects. \ref{related-work} and~\ref{summary-and-outlook}, where we discuss
  related work and give a summary and an outlook.

  To this end, we have formalized large parts of the \<open>\<natural>\<close>-calculus and our complete theory of
  transition systems in Isabelle/HOL~@{cite "jeltsch:ouroboros-formalization"}. Furthermore, we have
  produced this paper from documented Isabelle source code~@{cite "jeltsch:wflp-2019-source"}, which
  we have checked with Isabelle2018.
\<close>

section \<open>The \<open>\<natural>\<close>-Calculus\<close>

text_raw \<open>\label{the-natural-calculus}\<close>

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
  \<^term>\<open>p \<rightarrow>\<lparr>a \<triangleleft> \<nu> b. \<cent>b\<rparr> Q b\<close>. The following rules are HOAS versions of the \<open>\<pi>\<close>-calculus rules that
  deal with local channels:

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
  the latter binding their variables in any following target process. The rules for sending,
  receiving, and communication are the ones we have seen at the beginning of
  \hyperref[operational-semantics]{this subsection}. For dealing with local channels, the basic
  transition system contains the following rules:

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
  and \<open>a \<triangleleft> \<nu> b\<^sub>1 \<dots> b\<^sub>n. f b\<^sub>1 \<dots> b\<^sub>n\<close>, the latter binding their variables also in any following target
  process. The rules for sending, receiving, and communication just refer to the basic transition
  system:

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
  transition relations then become binary, relating source processes and residuals. This approach
  has been taken in \<open>\<psi>\<close>-calculi, for example.

  We define an inductive data type whose values are the residuals of the basic transition system.
  There are two kinds of such residuals:

    \<^item> Acting:@{lemma [display, source]
      "Acting \<alpha> p \<equiv> \<lbrace>\<alpha>\<rbrace> p"
      by (fact reflexive)}

    \<^item> Opening:@{lemma [display, source]
      "Opening P \<equiv> \<lbrace>\<nu> a\<rbrace> P a"
      by (fact reflexive)}

  \<^noindent> Note that in the \<open>Opening\<close> case we use HOAS and binder notation again.

  Actually we do not just define a single data type for residuals but a type constructor
  \<^type>\<open>basic_residual\<close> that is parametrized  by the type of the target. As a result, terms
  \<^term>\<open>\<lbrace>\<xi>\<rbrace> e\<close> can be formed from terms \<^term>\<open>e\<close> of any type~\<^term>\<open>\<alpha>\<close>, with the resulting type being
  \<open>\<alpha> basic_residual\<close>. This permits us to construct \<^emph>\<open>nested residuals\<close>, residuals with two labels,
  which have type \<^typ>\<open>process basic_residual basic_residual\<close>. Nested residuals will play a role in
  Subsection~\ref{weak-residuals}.

  We also introduce an analogous type constructor \<^type>\<open>proper_residual\<close> for the proper transition
  system. The definition of \<^type>\<open>proper_residual\<close> is considerably more complex than the definition
  of \<^type>\<open>basic_residual\<close>, which is why we do not show it here. However, its general approach to
  capturing scope opening is the same.
\<close>

subsection \<open>Behavioral Equivalence\<close>

text_raw \<open>\label{behavioral-equivalence}\<close>

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
      follows:\<^footnote>\<open>Note that \<open>_\<inverse>\<inverse>\<close> is Isabelle/HOL syntax for conversion of relations that are
      represented by binary boolean functions.\<close>@{lemma [display, source]
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
\<close>

section \<open>Residuals Axiomatically\<close>

text_raw \<open>\label{residuals-axiomatically}\<close>

text \<open>
  As it stands, we have to develop the theory of bisimilarity separately for the basic and the
  proper transition system. This means, we have to essentially duplicate definitions of concepts
  like simulation relation, bisimulation relation, and bisimilarity and also proofs of various
  properties of these concepts. The reason is that these two transition systems use different
  notions of residual and consequently different lifting operations.

  However, we can develop the theory of bisimilarity also generically. We describe axiomatically
  what a lifting operation is and construct all definitions and proofs of our theory with reference
  to a lifting operation parameter that fulfills the respective axioms. Whenever we want our theory
  to support a new notion of residual, we just have to define a concrete lifting operation for it
  and prove that this lifting operation has the necessary properties.

  Note that this approach not only allows for a common treatment of the basic and the proper
  transition system but also captures transition systems of other process calculi. In particular, it
  also works with transition systems that do not allow scope opening, like CCS~@{cite "milner:ccs"},
  as there is a trivial lifting operation for such systems.
\<close>

subsection \<open>Residuals in General\<close>

context %invisible residual begin

text \<open>
  As indicated in Subsection~\ref{behavioral-equivalence}, a lifting operation \<^term>\<open>lift\<close> should
  generally behave such that \<^term>\<open>lift \<X>\<close> relates two residuals if and only if their labels are the
  same and their target process are in relation~\<^term>\<open>\<X>\<close>. The axioms for lifting operations should
  be in line with this behavior and should at the same time be specific enough to allow us to
  develop the theory of bisimilarity solely based on a lifting operation parameter. It turns out
  that the following axioms fulfill these requirements:\<^footnote>\<open>Note that \<open>_ OO _\<close> is Isabelle/HOL syntax
  for composition of relations that are represented by binary boolean functions.\<close>

    \<^item> Equality preservation:@{lemma [display]
      \<open>lift (=) = (=)\<close>
      by (fact lift_equality_preservation)}

    \<^item> Composition preservation:@{lemma [display]
      \<open>lift (\<X> OO \<Y>) = lift \<X> OO lift \<Y>\<close>
      by (fact lift_composition_preservation)}

    \<^item> Conversion preservation:@{lemma [display]
      \<open>lift \<X>\<inverse>\<inverse> = (lift \<X>)\<inverse>\<inverse>\<close>
      by (fact lift_conversion_preservation)}

  The presence of the equality preservation and composition preservation axioms means that lifting
  operations are functors. However, they are not functors in the Haskell sense. Haskell's functors
  are specifically endofunctors on the category of types and functions, but lifting operations are
  endofunctors on the category of types and \<^emph>\<open>relations\<close>.\<^footnote>\<open>The analogy to functors in the Haskell
  sense can be seen from the fact that replacing \<^term>\<open>lift\<close>, \<^term>\<open>(=)\<close>, and \<^term>\<open>(OO)\<close> in the
  equality preservation and composition preservation axioms by Haskell's \<^verbatim>\<open>fmap\<close>, \<^verbatim>\<open>id\<close>, and \<^verbatim>\<open>(.)\<close>
  yields Haskell's functor axioms.\<close>

  With the additional conversion preservation axiom, the axioms for lifting operations are precisely
  the axioms for \<^emph>\<open>relators\<close>~@{cite \<open>Section~5.1\<close> "bird:aop"}. Therefore, we can say that a residual
  structure is just an endorelator on the category of types and relations -- no problem here.
  Luckily, Isabelle/HOL automatically generates relator-specific constructs for every data type,
  namely the lifting operation and various facts about it, including the instances of the axioms. As
  a result, instantiating our theory of bisimilarity to a new notion of residual is extremely
  simple.
\<close>

end %invisible

subsection \<open>Weak Residuals\<close>

text_raw \<open>\label{weak-residuals}\<close>

no_notation %invisible proper_transition ("_ \<rightarrow>\<^sub>\<sharp>_" [51, 51] 50)
notation %invisible proper_transition ("_ \<rightarrow>_" [51, 51] 50)

no_notation %invisible proper.weak_transition (infix "\<Rightarrow>\<^sub>\<sharp>" 50)
notation %invisible proper.weak_transition ("_ \<Rightarrow>_" [51, 51] 50)

abbreviation %invisible
  silent_transition_closure :: "process \<Rightarrow> process \<Rightarrow> bool"
  (infix "\<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>*" 50)
where
  "(\<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>*) \<equiv> (\<lambda>s t. s \<rightarrow>\<lparr>\<tau>\<rparr> t)\<^sup>*\<^sup>*"

lemma %invisible silent_weak_transition_def:
  shows "p \<Rightarrow>\<lparr>\<tau>\<rparr> q \<longleftrightarrow> p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
proof
  assume "p \<Rightarrow>\<lparr>\<tau>\<rparr> q"
  then show "p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
  proof (induction p "\<lparr>\<tau>\<rparr> q" arbitrary: q)
    case strong_transition
    then show ?case
      by (fact r_into_rtranclp)
  next
    case silent_transition
    then show ?case
      by (blast elim: proper_silent.cases)
  next
    case (composed_transition p _ q)
    then obtain u where "p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* u" and "u \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
      by (blast elim: proper_silent.cases proper_lift_cases)
    then show ?case
      by (fact rtranclp_trans)
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
  Our axiomatic treatment of lifting operations allows us to handle ordinary bisimilarity, which is
  also known as \<^emph>\<open>strong bisimilarity\<close>. In practice, however, we are more interested in \<^emph>\<open>weak
  bisimilarity\<close>. Weak bisimilarity cares only about \<^emph>\<open>observable\<close> behavior; it treats internal
  communication as silent and ignores it.

  Normally, weak bisimilarity can be elegantly defined as the bisimilarity of the \<^emph>\<open>weak transition
  relation\<close>~\<open>(\<Rightarrow>)\<close>, which is derived from the original transition relation~\<open>(\<rightarrow>)\<close> using the
  following equivalences:\<^footnote>\<open>The notation \<open>_ \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* _\<close> stands for the reflexive and transitive closure
  of \<open>_ \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* _\<close>.\<close>

    \<^item> Silent:@{lemma [display, source]
      "p \<Rightarrow>\<lparr>\<tau>\<rparr> q \<longleftrightarrow> p \<rightarrow>\<lparr>\<tau>\<rparr>\<^sup>*\<^sup>* q"
      by (fact silent_weak_transition_def)}

    \<^item> Observable:@{lemma [display, source]
      "\<xi> \<noteq> \<tau> \<Longrightarrow> p \<Rightarrow>\<lparr>\<xi>\<rparr> q \<longleftrightarrow> (\<exists>s t. p \<Rightarrow>\<lparr>\<tau>\<rparr> s \<and> s \<rightarrow>\<lparr>\<xi>\<rparr> t \<and> t \<Rightarrow>\<lparr>\<tau>\<rparr> q)"
      by (fact observable_weak_transition_def)}

  Unfortunately, the above definition of~\<open>(\<Rightarrow>)\<close> refers to a dedicated silent label and thus cannot
  be applied to our setting, where we treat residuals as black boxes. To resolve this issue, we
  modify the definition of~\<open>(\<Rightarrow>)\<close> such that it is based on two relations that together identify
  silence. We define these relations differently for different notions of residual but specify their
  general properties by a set of axioms.
\<close>

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

text \<open>
  The first of the relations that identify silence relates each process with the residual that
  extends this process with the silent label. For \<^type>\<open>basic_residual\<close>, we define this relation
  inductively using the following rule:@{lemma [display]
  \<open>basic_silent p (\<lbrace>\<tau>\<rbrace> p)\<close>
  by (fact basic_internal_is_silent)}
  For \<^type>\<open>proper_residual\<close> and other residual type constructors, we can define the corresponding
  relation in an analogous way.

  The second of the relations that identify silence relates each nested residual that contains the
  silent label at least once with the ordinary residual that is obtained by dropping this label. For
  \<^type>\<open>basic_residual\<close>, we define this relation inductively using the following rules:

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

  \<^noindent> For \<^type>\<open>proper_residual\<close> and other residual type constructors, we can define the corresponding
  relation in an analogous way.
\<close>

(*
  From now on, we work with seemingly generic functions \<open>(\<rightarrow>)\<close>, \<open>lift\<close>, \<open>silent\<close>, and \<open>fuse\<close> that
  are in fact the concrete entities for the basic transition system. The reasons are as follows:

    \<^item> There cannot be a generic \<open>fuse\<close> (because Isabelle does not support higher-kinded types).

    \<^item> As a consequence of the former, there cannot be generic proofs involving \<open>fuse\<close> (we conduct
      the proofs for the basic transition instead, which gives us at least \<^emph>\<open>some\<close> assurance.
*)

no_notation %invisible proper_transition ("_ \<rightarrow>_" [51, 51] 50)

no_notation %invisible proper.weak_transition ("_ \<Rightarrow>_" [51, 51] 50)

notation %invisible basic_transition (infix "\<rightarrow>" 50)

notation %invisible basic.weak_transition (infix "\<Rightarrow>" 50)

notation %invisible basic_lift ("lift")

notation %invisible basic_silent ("silent")

notation %invisible basic_fuse ("fuse")

text \<open>
  We define the weak transition relation~\<^term>\<open>(\<Rightarrow>)\<close> of a given transition relation~\<^term>\<open>(\<rightarrow>)\<close>
  generically based on two parameters \<^term>\<open>silent\<close> and \<^term>\<open>fuse\<close>. The definition of~\<^term>\<open>(\<Rightarrow>)\<close> is
  inductive, using the following rules:

    \<^item> Strong transitions:@{lemma [display]
      \<open>p \<rightarrow> c \<Longrightarrow> p \<Rightarrow> c\<close>
      by (fact basic.strong_transition)}

    \<^item> Empty transitions:@{lemma [display]
      \<open>silent p c \<Longrightarrow> p \<Rightarrow> c\<close>
      by (fact basic.silent_transition)}

    \<^item> Compound transitions:@{lemma [display]
      \<open>\<lbrakk>p \<Rightarrow> c; lift (\<Rightarrow>) c z; fuse z d\<rbrakk> \<Longrightarrow> p \<Rightarrow> d\<close>
      by (rule basic.composed_transition, auto simp add: basic_absorb_from_fuse)}

  As indicated above, the behavior of \<^term>\<open>silent\<close> and \<^term>\<open>fuse\<close> should generally be such that
  \<^term>\<open>silent\<close> adds a silent label to a process and \<^term>\<open>fuse\<close> removes a silent label from a nested
  residual. The following axioms are in line with this behavior and are at the same time specific
  enough to allow us to develop the theory of weak bisimilarity solely based on the \<^term>\<open>silent\<close>
  and \<^term>\<open>fuse\<close> parameters:

    \<^item> Silent naturality:@{lemma [display]
      \<open>\<X> OO silent = silent OO lift \<X>\<close>
      by (blast
        elim: basic_silent.cases basic_lift_cases
        intro: basic_internal_is_silent basic_lift_intros)}

    \<^item> Fuse naturality:@{lemma [display]
      \<open>lift (lift \<X>) OO fuse = fuse OO lift \<X>\<close>
      by (simp add:
        basic_fuse_def
        basic_residual.rel_compp [symmetric]
        basic_silent_converse_naturality)}

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

  The above axioms are precisely the axioms for monads.\<^footnote>\<open>The analogy to monads in the Haskell sense
  can be seen from the fact that replacing \<^term>\<open>lift\<close>,\<^term>\<open>silent\<close>, \<^term>\<open>fuse\<close>, \<^term>\<open>(=)\<close>, and
  \<^term>\<open>(OO)\<close> in these axioms by Haskell's \<^verbatim>\<open>fmap\<close>, \<^verbatim>\<open>return\<close>, \<^verbatim>\<open>join\<close>, \<^verbatim>\<open>id\<close>, and \<^verbatim>\<open>(.)\<close> yields the
  naturality properties of \<^verbatim>\<open>return\<close> and \<^verbatim>\<open>join\<close>, which hold automatically because of
  parametricity~@{cite "wadler:fpca-1989"}, as well as Haskell's \<^verbatim>\<open>join\<close>-based monad axioms.\<close>
  Therefore, we can say that a weak residual structure is just a monad in the category of types and
  relations -- a completely unproblematic specification.

  The monadic approach to weak residuals is actually very general. It does not only allow for a
  common treatment of residuals with different scope opening patters but also makes non-standard
  notions of silence possible, for example, by allowing multiple silent labels. Despite this
  generality, typical properties of weak bisimilarity can be proved generically. Concretely, we have
  developed formal proofs of the following statements:

    \<^item> Weak bisimilarity is the same as ``mixed'' bisimilarity, a notion of bisimilarity where
      ordinary transitions are simulated by weak transitions.

    \<^item> Strong bisimilarity is a subrelation of weak bisimilarity.

  Furthermore, the generic definition of the weak transition relation~\<^term>\<open>(\<Rightarrow>)\<close> is simpler than
  the traditional definition shown at the beginning of \hyperref[weak-residuals]{this subsection} in
  that it does not distinguish between silent and observable transitions; this distinction is pushed
  into the definitions of the \<^term>\<open>silent\<close> and \<^term>\<open>fuse\<close> relations of the individual notions of
  weak residual. The simple structure of the definition of~\<^term>\<open>(\<Rightarrow>)\<close> encourages a simple structure
  of generic proofs about weak transitions.
\<close>

subsection \<open>Normal Weak Residuals\<close>

text \<open>
  The monadic approach to weak residuals forces us to implement the two relations \<^term>\<open>silent\<close> and
  \<^term>\<open>fuse\<close> and prove their properties for every notion of residual. This usually takes quite some
  effort, in particular because the definition of the \<^term>\<open>fuse\<close> relation is typically non-trivial,
  which also affects the proofs of its properties. The reward is that we can use non-standard
  notions of silence. However, we rarely need this additional power, because we are usually fine
  with having \<^emph>\<open>normal weak residuals\<close>, weak residuals that use a dedicated label to indicate
  silence. We introduce a more specific algebraic structure for normal weak residuals, which is much
  easier to instantiate than the monad structure of arbitrary weak residuals.

  We identify silence using just a \<^term>\<open>silent\<close> relation that has the following properties:

    \<^item> Naturality:@{lemma [display]
      \<open>\<X> OO silent = silent OO lift \<X>\<close>
      by (blast
        elim: basic_silent.cases basic_lift_cases
        intro: basic_internal_is_silent basic_lift_intros)}

    \<^item> Left-uniqueness and left-totality:@{lemma [display]
      \<open>silent OO silent\<inverse>\<inverse> = (=)\<close>
      by (fact basic.silent_left_uniqueness_and_left_totality)}

    \<^item> Right-uniqueness:@{lemma [display, source]
      "silent\<inverse>\<inverse> OO silent \<le> (=)"
      by (fact basic.silent_right_uniqueness)}

  Note that in fact these axioms ensure that \<^term>\<open>silent\<close> identifies a single label, our silent
  label. This shows that, although we do not have first-class labels explicitly, we can nevertheless
  have first-class representations of those labels that do not involve scope opening.

  From a \<^term>\<open>silent\<close> relation we can derive a relation \<^term>\<open>fuse\<close> as follows:@{lemma [display]
  \<open>fuse = silent\<inverse>\<inverse> \<squnion> lift silent\<inverse>\<inverse>\<close>
  by (simp add: basic_fuse_def)}
  This derivation captures exactly the idea that \<^term>\<open>fuse\<close> removes a silent label from a nested
  residual: since \<^term>\<open>silent\<close> adds a silent label, \<^term>\<open>silent\<inverse>\<inverse>\<close> removes a silent label, and
  consequently \<^term>\<open>lift silent\<inverse>\<inverse>\<close> removes a silent label under another label.

  A \<^term>\<open>silent\<close> relation with the above properties and the \<^term>\<open>fuse\<close> relation derived from it
  together fulfill the monad axioms, which shows that normal weak residuals are in fact weak
  residuals.
\<close>

section \<open>Related Work\<close>

text_raw \<open>\label{related-work}\<close>

text \<open>
  We are not the first ones to formalize a process calculus using HOAS.
  Honsell~et~al.~@{cite "honsell:tcs-253-2"}, for example, define a HOAS-version of the
  $\pi$-calculus in Coq and prove considerable parts of its metatheory. Their formalization does not
  allow the construction of \<^emph>\<open>exotic terms\<close>, that is, processes whose structure depends on data. In
  our formalization, we use exotic terms deliberately for branching. However, we actually want
  process structure to depend on ordinary data only; dependence on channels, especially local
  channels, is something we would like to prevent. The approach of Honsell~et~al. for ruling out
  exotic terms is to declare the type of channels as a parameter. Unfortunately, we cannot adopt
  this approach for our formalization, since the classical nature of Isabelle/HOL makes exotic terms
  possible even if the channel type is abstract.

  Röckl and Hirschkoff~@{cite "roeckel:jfp-13-2"} develop a HOAS-based implementation of the
  language of the $\pi$-calculus in Isabelle/HOL and show that it is adequate with respect to an
  ordinary, first-order implementation. They prove several syntactic properties but do not deal with
  transitions and bisimilarity at all. Their definition of processes includes exotic terms, but they
  define a separate wellformedness predicate that identifies those processes that are not exotic.

  Neither of the two works described uses an abstract theory of transition systems like we do.
  However, there is also no real demand for that, as these developments only deal with one or even
  no transition system.

  We use HOAS, because we can avoid the difficulties of name handling this way. Another approach is
  to keep names explicit but use nominal logic~@{cite "pitts:ic-186-2"} to make name handling
  easier. Bengtson follows this approach in his dissertation~@{cite "bengtson:phd-thesis"}. He
  formalizes several process calculi, namely CCS, the $\pi$-calculus, and $\psi$-calculi, in
  Isabelle/HOL, making use of its support for nominal logic.
\<close>

section \<open>Summary and Outlook\<close>

text_raw \<open>\label{summary-and-outlook}\<close>

text \<open>
  We have presented the language and the operational semantics of the \<open>\<natural>\<close>-calculus, a
  general-purpose process calculus embedded into functional host languages using HOAS. Since the
  operational semantics of the \<open>\<natural>\<close>-calculus is defined using two transition systems, we have
  developed an abstract theory of transition systems to treat concepts like bisimilarity
  generically. We have formalized large parts of the \<open>\<natural>\<close>-calculus and our complete theory of
  transition systems in Isabelle/HOL~@{cite "jeltsch:ouroboros-formalization"}.

  As it stands, the \<open>\<natural>\<close>-calculus allows process structure to depend on channels, which is something
  we would like to avoid. Thus an important task for the future is the development of techniques
  that allows us to prevent channel-dependent behavior while continuing to use HOAS for expressing
  binding of names.

  We plan to very soon start using our process calculus for developing a formally verified
  implementation of the Ouroboros family of consensus protocols. Our hope is to gain valuable
  feedback about our process calculus work this way, which can potentially lead to improvements of
  the calculus and its implementation.
\<close>

end %invisible
