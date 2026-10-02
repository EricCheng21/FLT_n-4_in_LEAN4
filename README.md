# Reflections and Workflow on an Automated Proof Strategy for Lean 4 under FLT.Four

This project is motivated by a gap I encountered while learning Lean 4: the gap between a human mathematical proof and a machine-checkable formal proof.

In ordinary mathematical writing, many steps are compressed. A human proof often says things like "by the classification of primitive Pythagorean triples", "the factors must be squares", or "this contradicts minimality". These phrases are mathematically meaningful to a reader, but they hide many precise conditions: coprimality assumptions, positivity assumptions, parity assumptions, sign issues, and the exact form of the object being constructed.

In Lean 4, none of these hidden details can remain implicit. Every hypothesis has to be available in the right form, every object has to have the right type, and every transformation has to be justified by a theorem, a definition, or a tactic. This makes the process of translating a human proof into Lean substantially more difficult than simply "typing up" the proof.

I was also influenced by discussions and lectures about the limitations of AI models in formal proof generation. Generative AI can be useful for suggesting Lean syntax, finding relevant lemmas, and explaining error messages. However, it can also fall into loops or hallucinate nonexistent lemmas when the proof state is not broken into sufficiently precise subgoals（lecture 4.24 the topic of automated conjecture resolution）. One reason for this is that human proofs rely on implicit mathematical context, while Lean requires explicit proof objects.

The strategy explored in this project is therefore a blueprint-based workflow:

1. Start with a human proof blueprint.
2. Break the proof into small mathematical fragments.
3. Treat each fragment as a node in the proof graph.
4. Formalize each node as a separate Lean lemma or clearly marked proof block.
5. Use Lean's kernel as the final verifier.
6. Refactor the final proof so that the Lean code follows the human blueprint.

## Scope of the Project

Mathlib already contains a complete formalization of Fermat's Last Theorem for exponent 4 in `Mathlib.NumberTheory.FLT.Four`. In this project, I do not claim to give a new mathematical proof of Fermat's theorem. The preliminary parts of my Lean file use mathlib's existing infrastructure, such as `Fermat42`, `Fermat42.Minimal`, `PythagoreanTriple`, and the classification of primitive Pythagorean triples.

The main focus of my project is the infinite descent step.  I extracted this
part into a separate Lean file, `InfiniteDescent.lean`, so that the core proof
strategy can be read independently from the surrounding wrapper material in
`FermatFour.lean`.  Instead of directly invoking mathlib's final theorem
`Fermat42.not_minimal`, I reconstruct the argument in a teaching-oriented way. I
created a handwritten blueprint of the descent proof and then organized the Lean
proof around that blueprint. Each major mathematical move is labelled as a
"Blueprint" step in the code.

The earlier parts of the file are retained to provide context and to show the surrounding workflow under `FLT.Four`. They also helped me practice reading and writing Lean 4 proofs. However, the main contribution of the project is the reconstructed infinite descent argument in Part 4.

The infinite descent argument is also explained in `DescentBlueprint.md`.  This
file gives the human-readable proof strategy step by step and explains how each
step corresponds to the Lean proof in `InfiniteDescent.lean`.

## The Descent Argument

The descent argument follows the classical structure:

- Assume a normalized minimal solution of `a ^ 4 + b ^ 4 = c ^ 2`.
- View `(a ^ 2, b ^ 2, c)` as a primitive Pythagorean triple.
- Classify this triple to obtain parameters `m` and `n`.
- Use `a ^ 2 = m ^ 2 - n ^ 2` to construct a second Pythagorean triple `(a, n, m)`.
- Classify the second triple to obtain parameters `r` and `s`.
- Use coprimality and square-factor arguments to show that certain factors are squares.
- Construct a new Fermat42 solution `(j, k, i)`.
- Prove that the new square side is smaller than the original one.
- Contradict the assumed minimality.

## Formalization Workflow

The main contribution of this project is not a new proof of Fermat's Last Theorem for exponent 4, which is already formalized in mathlib. Instead, the project explores a workflow for translating a classical infinite descent proof into Lean 4.

The key idea is to begin with a human proof blueprint and then identify the intermediate mathematical statements that are often omitted in ordinary mathematical exposition. Rather than formalizing the descent argument as one large theorem, the proof is decomposed into a collection of smaller lemmas, each corresponding to a single mathematical transformation.

This decomposition serves two purposes. First, it makes the proof easier to formalize and debug in Lean. Second, it allows the final theorem to follow the same conceptual structure as the original human proof. The Lean file is therefore organized around a sequence of "Blueprint" steps that mirror the descent argument and are reassembled into the final contradiction.

An important observation from the project is that the main difficulty in formalization is often not proving individual facts, but discovering the intermediate statements needed to connect a human argument to a machine-checkable proof. In this sense, the project can be viewed as an exercise in proof decomposition and proof engineering.
