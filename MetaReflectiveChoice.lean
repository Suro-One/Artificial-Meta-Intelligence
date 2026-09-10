/-
  MetaReflectiveChoice.lean

  A first Lean 4 formalization of a proposed computational criterion
  for consciousness: "substrate-independent, meta-reflective
  computational choice."

  Status: first pass, covering Layers A-G of the master specification
  plus explicit counterexamples and independence/realizability
  theorems. Zero `sorry`, zero `axiom`, zero Mathlib dependency (core
  Lean 4 only), tested against Lean 4.14.0.

  READ THE FINAL COMMENT BLOCK ("LAYER I") BEFORE READING ANY THEOREM
  BELOW AS A CLAIM ABOUT PHENOMENAL CONSCIOUSNESS. It is not one.
  Every theorem here is a statement about a formally specified
  computational structure, checkable by the Lean kernel. None of
  them asserts anything about subjective experience.
-/

namespace MetaReflectiveChoice

universe u v

/- ================================================================
   LAYER A — Basic computation: possibility (Sec. 6)
   ================================================================ -/

/-- The possibilities reachable from a state, as a predicate on
    states rather than `Set`/`Finset`, so this file needs no
    Mathlib. `poss s s'` reads "`s'` is a possible continuation of
    `s`". -/
def Poss (S : Type u) := S → S → Prop

/-- `s` is a genuine *choice point* iff at least two distinct
    continuations are represented as possible from it. Deliberately
    weak: it says nothing about *how* a continuation gets picked,
    only that more than one was on the table. -/
def HasAlternative {S : Type u} (poss : Poss S) (s : S) : Prop :=
  ∃ s₁ s₂ : S, poss s s₁ ∧ poss s s₂ ∧ s₁ ≠ s₂

/-- The converse direction, stated as its own lemma because it is
    exactly the formal shape of several of Sec. 18's counterexamples
    (lookup table, thermostat, deterministic single-branch program):
    if `poss` ever offers only one option, there is no choice point
    there, full stop. -/
theorem not_hasAlternative_of_unique {S : Type u} (poss : Poss S) (s : S)
    (huniq : ∀ s₁ s₂, poss s s₁ → poss s s₂ → s₁ = s₂) :
    ¬ HasAlternative poss s := by
  rintro ⟨s₁, s₂, h1, h2, hne⟩
  exact hne (huniq s₁ s₂ h1 h2)

/-- Theorem 2 (Sec. 23): a genuine choice point unpacks into two
    distinct, both-possible continuations. -/
theorem theorem2_choicepoint_needs_two {S : Type u} (poss : Poss S) (s : S)
    (h : HasAlternative poss s) :
    ∃ s₁ s₂ : S, s₁ ≠ s₂ ∧ poss s s₁ ∧ poss s s₂ := by
  obtain ⟨s₁, s₂, h1, h2, hne⟩ := h
  exact ⟨s₁, s₂, hne, h1, h2⟩

/- ================================================================
   LAYER B — Choice (Sec. 7)
   ================================================================ -/

/-- A choice function, packaged with the "the chosen state really
    is one of the options" obligation baked in, so it can never be
    satisfied vacuously. -/
structure ChoiceFn (S : Type u) where
  poss       : Poss S
  choose     : S → S
  choose_mem : ∀ s, poss s (choose s)

def ChoiceFn.HasChoicePoint {S : Type u} (c : ChoiceFn S) (s : S) : Prop :=
  HasAlternative c.poss s

/-- Determinism, made explicit instead of assumed. Every Lean
    function trivially satisfies this — which is exactly the
    content of Theorem 6 / Sec. 29 below: nothing about `choose`
    smuggles in randomness. -/
def Deterministic {S : Type u} (f : S → S) : Prop :=
  ∀ s₁ s₂, s₁ = s₂ → f s₁ = f s₂

theorem choiceFn_deterministic {S : Type u} (c : ChoiceFn S) :
    Deterministic c.choose :=
  fun _ _ h => congrArg c.choose h

/- ================================================================
   LAYER C — Deliberation (Sec. 8)
   ================================================================ -/

/-- `evaluates s s'` stands for "the internal process at `s` has
    weighed `s'` as a candidate continuation." Requiring the actual
    choice to be among the evaluated options is meant to rule out a
    choice bolted onto no internal process at all. See
    `deliberation_gap` below for why this, by itself, does NOT yet
    achieve that — an important honest finding, not a bug I've
    hidden. -/
structure DeliberativeChoice (S : Type u) extends ChoiceFn S where
  evaluates        : S → S → Prop
  choose_evaluated : ∀ s, evaluates s (choose s)

def DeliberativeChoice.Deliberates {S : Type u} (d : DeliberativeChoice S) (s : S) : Prop :=
  d.HasChoicePoint s

/-- **Honest gap, not a feature.** Every `ChoiceFn` — including a
    literal lookup table or an RNG-driven selector — extends to a
    `DeliberativeChoice` by defining `evaluates s s' := s' = choose
    s`. So `DeliberativeChoice`, as formalized above, adds no
    discriminating power over plain `ChoiceFn`: `Deliberates` and
    `HasChoicePoint` end up equivalent for the induced structure.
    This means Layer C, in its current form, has NOT yet captured
    what Sec. 7-8 actually asked for (ruling out "a mindless
    arbitrary function" dressed up as deliberation). Flagged
    explicitly rather than patched over — see the discussion
    preceding this file for what a real fix needs. -/
theorem deliberation_gap {S : Type u} (c : ChoiceFn S) :
    ∃ d : DeliberativeChoice S, d.toChoiceFn = c ∧
      ∀ s, d.Deliberates s ↔ c.HasChoicePoint s := by
  refine ⟨{ toChoiceFn := c
          , evaluates := fun s s' => s' = c.choose s
          , choose_evaluated := fun _ => rfl }, rfl, fun s => Iff.rfl⟩

/- ================================================================
   LAYER D/E — Self-representation & meta-reflection (Sec. 9-10)

   From here the ambient state type is

       MState Base Repr := { base : Base, model : Repr }

   `Base` carries whatever the system represents about the world,
   `Repr` is the representation space, `model` is the state's own
   current self-representation. This is a modelling choice (not
   forced by the master prompt) but it is the minimal structure that
   makes "does the self-model matter causally?" a well-posed
   question instead of a stipulation.
   ================================================================ -/

structure MState (Base : Type u) (Repr : Type v) where
  base  : Base
  model : Repr
  deriving DecidableEq

/-- `encodes r s` : representation `r` is *about* state `s`, i.e. is
    semantically correct as a self-description of `s`. Supplied as
    data (an "aboutness"/semantic relation, Sec. 31), never derived,
    and never assumed to hold universally — that is what keeps
    `SelfRepresents` below non-trivial, per Sec. 9's warning. -/
def Encodes (Base : Type u) (Repr : Type v) := Repr → MState Base Repr → Prop

/-- A state genuinely self-represents iff its own self-model slot
    actually encodes that very state — not merely iff a self-model
    slot exists (every `MState` has one; that alone would trivialize
    the predicate). -/
def SelfRepresents {Base : Type u} {Repr : Type v}
    (encodes : Encodes Base Repr) (s : MState Base Repr) : Prop :=
  encodes s.model s

/-- The self-model *causally influences* the transition: swapping
    out only the self-model component (holding the world/base
    component fixed) changes where the system goes next. Formal
    stand-in for Sec. 10's requirement that reflection be able to
    affect subsequent computation, not merely sit there as an inert
    log entry. -/
def Influences {Base : Type u} {Repr : Type v}
    (transition : MState Base Repr → MState Base Repr) (s : MState Base Repr) : Prop :=
  ∃ r : Repr, r ≠ s.model ∧ transition ⟨s.base, r⟩ ≠ transition s

/-- Meta-reflection (Sec. 10) = accurate self-representation *and*
    causal efficacy of that representation. Either half alone is
    cheap (Theorems 3/4 below show exactly this); the conjunction is
    not. -/
def MetaReflective {Base : Type u} {Repr : Type v}
    (encodes : Encodes Base Repr)
    (transition : MState Base Repr → MState Base Repr) (s : MState Base Repr) : Prop :=
  SelfRepresents encodes s ∧ Influences transition s

/- ================================================================
   LAYER F — Meta-choice / reflection depth (Sec. 11, Sec. 26)

   `DeliberativeChoice` is parametric in the underlying state type,
   so "choosing among choice-mechanisms" is literally
   `DeliberativeChoice (DeliberativeChoice S)`: a deliberative
   process whose *states* are themselves deliberative-choice
   structures. Reflection depth is then just how many times this is
   nested — a constructive, total answer to Sec. 26's question
   ("is arbitrary finite reflection depth computationally
   expressible?"). Yes: by this recursive type family, for every
   `n : Nat`, no axiom required.
   ================================================================ -/

def NthOrderChoice (S : Type u) : Nat → Type u
  | 0     => S
  | n + 1 => DeliberativeChoice (NthOrderChoice S n)

example (S : Type u) : NthOrderChoice S 0 = S := rfl
example (S : Type u) : NthOrderChoice S 1 = DeliberativeChoice S := rfl
example (S : Type u) :
    NthOrderChoice S 2 = DeliberativeChoice (DeliberativeChoice S) := rfl

/- ================================================================
   LAYER G — Candidate consciousness predicate (Sec. 21)

   Conjoins the independently-defined layers rather than defining
   consciousness as "makes conscious choices" (Sec. 24 — avoid
   circularity). The only structural link is that the system's
   dynamics *is* what its own deliberative mechanism outputs, so
   "does it choose" and "does it reflect" are both about one and the
   same transition function.
   ================================================================ -/

structure ConsciousCandidate (Base : Type u) (Repr : Type v) where
  deliberation : DeliberativeChoice (MState Base Repr)
  encodes      : Encodes Base Repr

def ConsciousCandidate.transition {Base : Type u} {Repr : Type v}
    (c : ConsciousCandidate Base Repr) : MState Base Repr → MState Base Repr :=
  c.deliberation.choose

def ConsciousCandidate.SatisfiesChoicePoint {Base : Type u} {Repr : Type v}
    (c : ConsciousCandidate Base Repr) (s : MState Base Repr) : Prop :=
  c.deliberation.HasChoicePoint s

def ConsciousCandidate.SatisfiesMetaReflection {Base : Type u} {Repr : Type v}
    (c : ConsciousCandidate Base Repr) (s : MState Base Repr) : Prop :=
  MetaReflective c.encodes c.transition s

/-- Layer G's candidate predicate at a state: a genuine,
    deliberation-grounded choice point, together with accurate and
    causally efficacious self-representation. -/
def ConsciousCandidate.IsCandidateAt {Base : Type u} {Repr : Type v}
    (c : ConsciousCandidate Base Repr) (s : MState Base Repr) : Prop :=
  c.SatisfiesChoicePoint s ∧ c.SatisfiesMetaReflection s

-- Theorem 1 (Sec. 23): a choice-point-satisfying candidate has at
-- least one available continuation.
theorem theorem1_choice_gives_continuation {Base : Type u} {Repr : Type v}
    (c : ConsciousCandidate Base Repr) (s : MState Base Repr)
    (h : c.SatisfiesChoicePoint s) :
    ∃ s', c.deliberation.poss s s' := by
  obtain ⟨s₁, _, h1, _, _⟩ := h
  exact ⟨s₁, h1⟩

/- ================================================================
   Two concrete instances, standing in for Sec. 18's counterexample
   menagerie, plus Theorems 3-7 (Sec. 23).
   ================================================================ -/

/-- COUNTEREXAMPLE (Sec. 18: thermostat / lookup table /
    self-referential program). A single fixed point: the only
    "possible continuation" of any state is itself. Trivially
    self-representing (we hand it an `encodes` that always holds)
    but structurally incapable of a choice point. -/
def selfReferentialSingleton : ConsciousCandidate Unit Unit where
  deliberation :=
    { poss             := fun s s' => s' = s
      choose           := fun s => s
      choose_mem       := fun _ => rfl
      evaluates        := fun s s' => s' = s
      choose_evaluated := fun _ => rfl }
  encodes := fun _ _ => True

-- Theorem 3 (Sec. 23): self-representation does not imply choice.
theorem theorem3_selfRepr_not_implies_choice :
    ∃ (c : ConsciousCandidate Unit Unit) (s : MState Unit Unit),
      SelfRepresents c.encodes s ∧ ¬ c.SatisfiesChoicePoint s := by
  refine ⟨selfReferentialSingleton, ⟨(), ()⟩, trivial, ?_⟩
  exact not_hasAlternative_of_unique _ _ (fun _ _ h1 h2 => h1.trans h2.symm)

/-- COUNTEREXAMPLE (Sec. 18: chess engine / RNG / optimization
    algorithm / branching deterministic machine). A genuine binary
    choice point at every state (flip the `Bool` component), but the
    `encodes` relation is identically `False`: nothing this system
    ever does counts as self-representation. -/
def noSelfModelSystem : ConsciousCandidate Bool Unit where
  deliberation :=
    { poss := fun _ s' => s' = (⟨true, ()⟩ : MState Bool Unit) ∨
                            s' = (⟨false, ()⟩ : MState Bool Unit)
      choose           := fun _ => ⟨true, ()⟩
      choose_mem       := fun _ => Or.inl rfl
      evaluates        := fun _ s' => s' = (⟨true, ()⟩ : MState Bool Unit) ∨
                                        s' = (⟨false, ()⟩ : MState Bool Unit)
      choose_evaluated := fun _ => Or.inl rfl }
  encodes := fun _ _ => False

theorem noSelfModelSystem_choicePoint (s : MState Bool Unit) :
    noSelfModelSystem.SatisfiesChoicePoint s :=
  ⟨⟨true, ()⟩, ⟨false, ()⟩, Or.inl rfl, Or.inr rfl, by decide⟩

-- Theorem 4 (Sec. 23): choice does not imply self-representation.
theorem theorem4_choice_not_implies_selfRepr :
    ∃ (c : ConsciousCandidate Bool Unit) (s : MState Bool Unit),
      c.SatisfiesChoicePoint s ∧ ¬ SelfRepresents c.encodes s :=
  ⟨noSelfModelSystem, ⟨true, ()⟩, noSelfModelSystem_choicePoint _, id⟩

-- Theorem 5 (Sec. 23): consequently, choice and self-representation
-- are logically independent unless further axioms are added — no
-- such axiom appears anywhere in this file.
theorem theorem5_independence :
    (∃ (c : ConsciousCandidate Unit Unit) (s : MState Unit Unit),
        SelfRepresents c.encodes s ∧ ¬ c.SatisfiesChoicePoint s) ∧
    (∃ (c : ConsciousCandidate Bool Unit) (s : MState Bool Unit),
        c.SatisfiesChoicePoint s ∧ ¬ SelfRepresents c.encodes s) :=
  ⟨theorem3_selfRepr_not_implies_choice, theorem4_choice_not_implies_selfRepr⟩

-- Theorem 6 (Sec. 23, Sec. 29 "Deterministic Choice Theorem"): a
-- deterministic choice function can sit at a genuine choice point.
-- Determinism is free (`choiceFn_deterministic`); this records that
-- it coexists with real multiplicity of alternatives, not just with
-- degenerate single-option systems.
theorem theorem6_deterministic_choice_at_choicepoint :
    ∃ (S : Type) (c : ChoiceFn S) (s : S),
      Deterministic c.choose ∧ c.HasChoicePoint s :=
  ⟨MState Bool Unit, noSelfModelSystem.deliberation.toChoiceFn, ⟨true, ()⟩,
    choiceFn_deterministic _, noSelfModelSystem_choicePoint _⟩

/-- Working instance for Theorem 7: `Base := Unit`, i.e. no external
    "world" state at all — deliberately disembodied (Sec. 15, Sec.
    30 "Imported Representation": the self-model here is supplied
    extrinsically as a bare `Bool`, never internally *generated* by
    any `generate` function, since this file defines none). The
    transition genuinely flips the self-model, so it is not just
    present but causally load-bearing. -/
def minimalReflectiveSystem : ConsciousCandidate Unit Bool where
  deliberation :=
    { poss := fun _ s' => s' = (⟨(), true⟩ : MState Unit Bool) ∨
                            s' = (⟨(), false⟩ : MState Unit Bool)
      choose           := fun s => ⟨(), !s.model⟩
      choose_mem       := fun s => by cases s.model <;> simp
      evaluates        := fun _ s' => s' = (⟨(), true⟩ : MState Unit Bool) ∨
                                        s' = (⟨(), false⟩ : MState Unit Bool)
      choose_evaluated := fun s => by cases s.model <;> simp }
  encodes := fun r s => r = s.model

theorem minimalReflectiveSystem_isCandidate :
    minimalReflectiveSystem.IsCandidateAt (⟨(), true⟩ : MState Unit Bool) := by
  refine ⟨⟨⟨(), true⟩, ⟨(), false⟩, Or.inl rfl, Or.inr rfl, by decide⟩, rfl, ?_⟩
  exact ⟨false, by decide, by decide⟩

-- Theorem 7 (Sec. 23): the definition does not logically require an
-- embodied state. `minimalReflectiveSystem` has `Base := Unit` — no
-- sensory/environmental component whatsoever — and still satisfies
-- the full Layer G predicate, choice point and meta-reflection
-- together, at a witness state.
theorem theorem7_no_embodiment_required :
    ∃ (Repr : Type) (c : ConsciousCandidate Unit Repr) (s : MState Unit Repr),
      c.IsCandidateAt s :=
  ⟨Bool, minimalReflectiveSystem, ⟨(), true⟩, minimalReflectiveSystem_isCandidate⟩

/- ================================================================
   BONUS — a genuine (partial) Substrate Invariance theorem
   (Sec. 28). Proved for the choice-point layer: "has genuine
   alternatives" transports across an isomorphism-respecting
   relabeling of the state space. Extending this through
   `SelfRepresents`/`Influences` needs a compatibility condition on
   `encodes` across the isomorphism too — left for the next pass,
   flagged rather than assumed.
   ================================================================ -/

structure Iso (S : Type u) (S' : Type v) where
  toFun     : S → S'
  invFun    : S' → S
  left_inv  : ∀ s, invFun (toFun s) = s
  right_inv : ∀ s', toFun (invFun s') = s'

theorem substrate_invariance {S : Type u} {S' : Type v}
    (e : Iso S S') (poss : Poss S) (poss' : Poss S')
    (hconj : ∀ s s', poss s s' ↔ poss' (e.toFun s) (e.toFun s'))
    (s : S) :
    HasAlternative poss s ↔ HasAlternative poss' (e.toFun s) := by
  constructor
  · rintro ⟨s₁, s₂, h1, h2, hne⟩
    refine ⟨e.toFun s₁, e.toFun s₂, (hconj s s₁).mp h1, (hconj s s₂).mp h2, ?_⟩
    intro h
    apply hne
    have := congrArg e.invFun h
    rwa [e.left_inv, e.left_inv] at this
  · rintro ⟨t₁, t₂, h1, h2, hne⟩
    refine ⟨e.invFun t₁, e.invFun t₂, ?_, ?_, ?_⟩
    · exact (hconj s (e.invFun t₁)).mpr (by rw [e.right_inv]; exact h1)
    · exact (hconj s (e.invFun t₂)).mpr (by rw [e.right_inv]; exact h2)
    · intro h
      apply hne
      have := congrArg e.toFun h
      rwa [e.right_inv, e.right_inv] at this

end MetaReflectiveChoice

/-
  ================================================================
  LEDGER (Sec. 22): what kind of claim each part of this file is.

  DEFINITIONS   : Poss, HasAlternative, ChoiceFn, Deterministic,
                  DeliberativeChoice, MState, Encodes,
                  SelfRepresents, Influences, MetaReflective,
                  NthOrderChoice, ConsciousCandidate, IsCandidateAt,
                  Iso.
  THEOREMS      : everything named `theoremN_...`, plus
                  `not_hasAlternative_of_unique`,
                  `choiceFn_deterministic`, `deliberation_gap`,
                  `substrate_invariance`, and the two `_isCandidate`
                  / `_choicePoint` witnesses. All proved, no
                  `sorry`.
  AXIOMS        : none. Zero in this file.
  CONJECTURES   : none stated as Lean terms; see the discussion
                  preceding this file for open problems (chiefly:
                  `deliberation_gap` shows Layer C needs independent
                  constraints on `evaluates` to do real philosophical
                  work; substrate invariance is proved only for the
                  choice-point layer, not for self-representation).
  PHILOSOPHICAL
  INTERPRETATION: none of the above, on its own or in conjunction,
                  is a claim that any instance — including
                  `minimalReflectiveSystem`, which does satisfy
                  every formal condition in this file — has
                  subjective experience. `IsCandidateAt` is a
                  candidate SYNTACTIC/computational criterion only.
                  Whether, or under what further premise,
                  `IsCandidateAt c s` bears on phenomenal
                  consciousness is a philosophical question this
                  file does not — and structurally cannot — answer.
                  Any future file that wants to assert a bridge
                  principle should do so as an explicit, clearly
                  labelled `axiom`, never smuggled into a theorem
                  statement or definition name.
  ================================================================
-/
