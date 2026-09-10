**Can consciousness be formalized as meta-reflective choice? I built the first Lean skeleton**

I've been exploring a deliberately minimal computational hypothesis:

> Consciousness may be a substrate-independent process involving represented possibilities, deliberate choice among those possibilities, and reflection upon the system's own representations and choices.

I implemented an initial version in Lean 4 with **zero `sorry` and zero axioms**.

The current formalization establishes several things:

* A choice point requires multiple distinct possible continuations.
* Choice does not require randomness or nondeterminism.
* Self-representation does not imply choice.
* Choice does not imply self-representation.
* These properties are formally independent under the current definitions.
* A non-embodied computational system can satisfy the current candidate criterion.
* The choice-point property is invariant under suitable state-space isomorphisms.

Interestingly, the formalization also caught a problem in my own theory: my first definition of "deliberation" was too weak and could be attached to essentially any choice function. Rather than hiding this, I'm treating it as a useful negative result.

I don't claim this proves phenomenal consciousness. The interesting question is whether the formal architecture can be strengthened into a precise, minimal computational theory without smuggling consciousness into the definitions.

The next step is to formalize **partial self-representation and causal meta-reflection**, rather than requiring a system to possess a complete model of itself.

I'd be very interested in criticism, especially from people working on consciousness, philosophy of mind, theoretical CS, AI, or formal methods.
