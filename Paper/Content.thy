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
  We call these terms simply ``processes''.

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

subsection \<open>Behavioral Equivalence\<close>

section \<open>Residuals Axiomatically\<close>

subsection \<open>Residuals in General\<close>

subsection \<open>Weak Residuals\<close>

subsection \<open>Normal Weak Residuals\<close>

section \<open>Wrapping Up\<close>

end %invisible
