import Complexity.Composition

/-!
# Pulling deterministic polynomial-time decisions back along a Karp reduction

The pinned library composes output-producing transducers. Its public
composition lemma assumes both stages halt with the Boolean decision `true`.
A decision machine must be allowed to reject. We keep the library's actual
composition machine and bound its rejecting branch, reusing its input cleanup,
stack compiler and polynomial single-tape simulation.
-/

namespace Mobius.Pullback

open Complexity

set_option backward.isDefEq.respectTransparency false

private theorem accepts_iff_decision {M : Machine} {input : Word} {fuel : Nat}
    {decision : Bool} {out : Tape}
    (run : runInput M fuel input = some (decision, out)) :
    Accepts M input ↔ decision = true := by
  constructor
  · rintro ⟨t, tape, accepted⟩
    exact congrArg Prod.fst (run_deterministic M (initial M input) run accepted)
  · rintro rfl
    exact ⟨fuel, out, run⟩

open TapeToStacks StackProgram in
private theorem run_decision_composition (first second : Machine)
    (firstFuel secondFuel : Nat) (input : Word) (decision : Bool) (middle out : Tape)
    (hfirst : runInput first firstFuel input = some (true, middle))
    (hsecond : runInput second secondFuel middle.output = some (decision, out)) :
    ∃ time registers, time ≤ 72 * (input.length + firstFuel + secondFuel + 1) ∧
      StackMachine.runInput (compositionMachine first second) time input =
        some (decision, registers) := by
  cases decision with
  | true =>
    obtain ⟨time, ht, hr⟩ := run_compositionMachine first second firstFuel secondFuel
      input middle out hfirst hsecond
    exact ⟨time, _, ht, hr⟩
  | false =>
    obtain ⟨t, ht, he⟩ := exec_normalized first firstFuel input middle hfirst
    obtain ⟨s, hs, hc⟩ := simulate_core second secondFuel middle.output false out hsecond []
    have rejected := exec_seq_failure (core second) extractor hc
    have next := exec_seq initializer (seq (core second) extractor)
      (exec_initializer middle.output) rejected
    have combined := compile_exec (Encoding.sum (normalEncoding first) (normalEncoding second))
      (exec_seq (normalized first) (normalized second) he next)
    have hm := runInput_output_length_le first firstFuel input (true, middle) hfirst
    simp only at hm
    refine ⟨t + (5 * middle.output.length + 4 + s), resultRegs [] out, ?_, ?_⟩
    · omega
    · simpa only [StackMachine.runInput, StackMachine.initial, compositionMachine,
        compositionProgram, compile, seq, registers_initial] using combined

/-- For the binary-word, counted Turing-machine definitions of the dependency,
a polynomial Karp reduction to a language in P gives a language in P. -/
theorem inP_of_reduction {A B : Language} (reduction : PolyRed A B) (decidableB : InP B) :
    InP A := by
  obtain ⟨f, ⟨first, c, k, reduceRun⟩, correct⟩ := reduction
  obtain ⟨second, ⟨d, l, decideRun⟩, spec⟩ := decidableB
  let S := TapeToStacks.compositionMachine first second
  let bound := compositionBound c k d l
  have runs (input : Word) : ∃ time decision registers, time ≤ bound input.length ∧
      StackMachine.runInput S time input = some (decision, registers) ∧
      (A input ↔ decision = true) := by
    obtain ⟨t, middle, ht, firstOK, middleOK⟩ := reduceRun input
    obtain ⟨s, decision, out, hs, secondOK⟩ := decideRun middle.output
    obtain ⟨time, registers, timeBound, run⟩ :=
      run_decision_composition first second t s input decision middle out firstOK secondOK
    have lengthBound := runInput_output_length_le first t input (true, middle) firstOK
    simp only at lengthBound
    have intermediate : middle.output.length ≤ input.length + 2 * powerBound c k input.length := by omega
    have seconds := Nat.le_trans hs (powerBound_mono d l intermediate)
    refine ⟨time, decision, registers, ?_, run, ?_⟩
    · unfold bound compositionBound
      omega
    · exact (correct input).trans (middleOK ▸ (spec middle.output).trans (accepts_iff_decision secondOK))
  refine ⟨StackCompile.compile S, ?_, ?_⟩
  · apply StackCompile.polynomialTimeMachine_of_stack S bound (polynomialBound_compositionBound c k d l)
    intro input
    obtain ⟨time, b, regs, ht, hr, _⟩ := runs input
    exact ⟨time, b, regs, ht, hr⟩
  · intro input
    obtain ⟨time, b, regs, _, hr, ha⟩ := runs input
    obtain ⟨_, _, _, ht, _⟩ := StackCompile.simulate S time input (b, regs) hr
    exact ha.trans (accepts_iff_decision ht).symm

end Mobius.Pullback
