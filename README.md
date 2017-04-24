# Contextual Equivalence for Probabilistic Programs with Continuous Random Variables and Scoring: The Coq Proofs

---

## Intro

These proofs accompany the paper at
<https://link.springer.com/chapter/10.1007%2F978-3-662-54434-1_14>

A prettier, coqdoc version of the sources is viewable at
<https://cobbal.github.io/ppl-ctx-equiv-coq/toc.html>


## Axioms

Since a complete formalization of measure theory is beyond the scope of this
project, many facts about measures and integration have been axiomatized. These
axioms are contained and documented
in
[integration.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.integration.html)

## Differences from paper

While the Coq formalism largely follows the same structure as the paper, there
are some notable differences between the two:

 - The language uses De Bruijn indices for variables.
 - Many operations (e.g. EVAL) are defined only for well-typed terms.
   Substitution is provided by
   the [autosubst](https://www.ps.uni-saarland.de/autosubst/) library over
   mostly type-erased terms.
   See
   [syntax.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.syntax.html)
   for details.
 - The language does not yet have primitive operations besides addition. The
   proofs for the other operations would be the same as for addition, but the
   syntactic overhead made it low priority.
 - Entropy is fixed to be the Hilbert cube [0, 1]^ω
 - Simple contexts don't yet include `let x = e in []`.

## Organization

Files listed in dependency order:

 - [ennr.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.ennr.html)
   <br> Extended non-negative reals [0, ∞].
 - [utils.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.utils.html)
   <br> Common helper tactics and lemmas.
 - [entropy.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.entropy.html) <br>
   Definition of entropy as countable product of unit intervals.
 - [integration.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.integration.html) <br>
   Axiomatization and lemmas about integration.
 - [syntax.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.syntax.html) <br>
   Definition of language syntax and evaluation.
 - [determinism.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.determinism.html) <br>
   Proof that evaluation is a partial function.
 - [relations.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.relations.html) <br>
 Definition of logical relation for contextual equivalence and proof of
 fundamental property.
 - [chain.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.chain.html)
 <br> Definition of type-aligned lists, which we use to define contexts
 - [ctxequiv.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.ctxequiv.html) <br>
 Definition of contexts, contextual equivalence, and proof that the logical
 relation is sound with respect to contextual equivalence.
 - [properties_of_relations.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.properties_of_relations.html) <br>
 Symmetry, transitivity, and reflexivity of main and auxilary logical relations.
 - [applications.v](https://cobbal.github.io/ppl-ctx-equiv-coq/OpSemProofs.applications.html) <br>
 Applications of logical relation to show equivalences. Includes β_v, simple
 contexts, commutivity, and a few others.
