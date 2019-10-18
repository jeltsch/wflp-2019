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

subsection \<open>Operational Semantics\<close>

subsection \<open>Behavioral Equivalence\<close>

section \<open>Residuals Axiomatically\<close>

subsection \<open>Residuals in General\<close>

subsection \<open>Weak Residuals\<close>

subsection \<open>Normal Weak Residuals\<close>

section \<open>Wrapping Up\<close>

end %invisible
