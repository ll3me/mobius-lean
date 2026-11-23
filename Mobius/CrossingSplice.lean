import Mobius.CrossingRun

/-! A physical run can be decomposed into excursions on the two sides of a
single boundary. Their durations may vary. The incoming state and the side
determine the entire interface: a crossing writes its departing cell, and
its head lands on the adjacent boundary cell. -/
namespace Mobius.CrossingRun
open Complexity

private inductive Exit (M : Machine)
  | stop (b : Bool)
  | hand (c : Absolute M)

/-- A maximal one-sided portion of a halting run. A hand-off is the
    first move in the portion whose destination is on the other side. -/
private inductive Part (M : Machine) (cut : Int) (s : Bool) : Absolute M → Exit M → Prop
  | stop {c b} (here : leftOf cut c.head = s) (code : instruction M c = .halt b) :
      Part M cut s c (.stop b)
  | cross {c w d q} (here : leftOf cut c.head = s) (code : instruction M c = .step w d q)
      (away : leftOf cut (c.head+delta d) ≠ s) : Part M cut s c (.hand (advance c w d q))
  | more {c w d q out} (here : leftOf cut c.head = s) (code : instruction M c = .step w d q)
      (rest : Part M cut s (advance c w d q) out) : Part M cut s c out

private inductive Phases (M : Machine) (cut : Int) :
    Bool → Absolute M → Bool → List (State M) → Prop
  | last {s c b} (part : Part M cut s c (.stop b)) : Phases M cut s c b []
  | next {s c c' b q qs} (part : Part M cut s c (.hand c')) (incoming : c'.state = q)
      (tail : Phases M cut (!s) c' b qs) : Phases M cut s c b (q::qs)

private theorem add_inside {M : Machine} {cut : Int} {s : Bool} {c : Absolute M}
    {w d q b qs} (here : leftOf cut c.head = s) (code : instruction M c = .step w d q)
    (tail : Phases M cut s (advance c w d q) b qs) : Phases M cut s c b qs := by
  cases tail with
  | last part => exact .last (.more here code part)
  | next part state rest => exact .next (.more here code part) state rest

private theorem split_trace (M : Machine) (cut : Int) (fuel : Nat) (c : Absolute M)
    {b es} (h : trace M fuel c = some (b,es)) :
    Phases M cut (leftOf cut c.head) c b (sequence cut es) := by
  induction fuel generalizing c es with
  | zero => contradiction
  | succ fuel ih =>
    rw [trace] at h
    cases code : instruction M c with
    | halt v =>
      rw [code] at h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact .last (.stop rfl code)
    | step w d q =>
      rw [code] at h
      cases ht : trace M fuel (advance c w d q) with
      | none => simp [ht] at h
      | some p =>
        obtain ⟨v,t⟩ := p
        simp only [ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        have rest := ih (advance c w d q) ht
        change Phases M cut (leftOf cut (c.head+delta d)) _ _ _ at rest
        rw [sequence_record]
        by_cases stay : leftOf cut c.head = leftOf cut (c.head+delta d)
        · rw [ite_eq_left stay]
          exact add_inside rfl code (stay ▸ rest)
        · rw [ite_eq_right stay]
          have other : leftOf cut (c.head+delta d) = !(leftOf cut c.head) := by
            cases a : leftOf cut c.head <;> cases z : leftOf cut (c.head+delta d) <;> simp_all
          exact .next (.cross rfl code (Ne.symm stay)) rfl (other ▸ rest)

private def mix (cut : Int) (s : Bool) (a frozen : Absolute M) : Absolute M :=
  ⟨a.state,a.head,fun i => if leftOf cut i=s then a.cells i else frozen.cells i⟩

private theorem mix_instruction {a : Absolute M} (frozen : Absolute M) (cut : Int) {s : Bool}
    (here : leftOf cut a.head = s) : instruction M (mix cut s a frozen) = instruction M a := by
  simp [instruction,mix,here]

private theorem mix_advance {a : Absolute M} (frozen : Absolute M) (cut : Int) {s : Bool}
    (here : leftOf cut a.head = s) (w : Symbol) (d : Move) (q : State M) :
    advance (mix cut s a frozen) w d q = mix cut s (advance a w d q) frozen := by
  unfold advance mix
  congr 1
  funext i
  by_cases h : i=a.head <;> simp [h,here] <;> split <;> simp_all

private def mixExit (cut : Int) (s : Bool) (frozen : Absolute M) : Exit M → Exit M
  | .stop b => .stop b
  | .hand a => .hand (mix cut s a frozen)

private theorem transfer_part {c : Absolute M} {cut s out}
    (part : Part M cut s c out) (frozen : Absolute M) :
    Part M cut s (mix cut s c frozen) (mixExit cut s frozen out) := by
  induction part with
  | stop here code => exact .stop here ((mix_instruction frozen cut here).trans code)
  | @cross c w d q here code away =>
    change Part M cut s _ (.hand (mix cut s (advance c w d q) frozen))
    rw [← mix_advance frozen cut here]
    exact .cross here ((mix_instruction frozen cut here).trans code) away
  | @more c w d q out here code tail ih =>
    apply Part.more (c := mix cut s c frozen) here ((mix_instruction frozen cut here).trans code)
    rw [mix_advance frozen cut here]
    exact ih

private theorem far_cell {c : Absolute M} {cut s} (here : leftOf cut c.head=s) {i : Int}
    (far : leftOf cut i ≠ s) (w : Symbol) (d : Move) (q : State M) :
    (advance c w d q).cells i = c.cells i := by
  have ne : i ≠ c.head := fun eq => far (eq ▸ here)
  simp [advance,ne]

private def exitFacts (cut : Int) (s : Bool) (c : Absolute M) : Exit M → Prop
  | .stop _ => True
  | .hand z => z.head = (if s then cut else cut-1) ∧ ∀ i, leftOf cut i ≠ s → z.cells i = c.cells i

private theorem exit_facts {c : Absolute M} {cut s out} (part : Part M cut s c out) :
    exitFacts cut s c out := by
  induction part with
  | stop => trivial
  | cross here code away =>
    exact ⟨crossing_head _ _ _ _ here away,fun i far => far_cell here far _ _ _⟩
  | more here code tail ih =>
    rename_i out
    cases out with
    | stop => trivial
    | hand z => exact ⟨ih.1, fun i far => (ih.2 i far).trans (far_cell here far _ _ _)⟩

private theorem handover {a b a' b' : Absolute M} {cut s}
    (left : Part M cut s a (.hand a')) (right : Part M cut s b (.hand b'))
    (q : a'.state = b'.state) : mix cut s a' b = mix cut (!s) b' a' := by
  have la := exit_facts left
  have rb := exit_facts right
  change a'.head = _ ∧ _ at la
  change b'.head = _ ∧ _ at rb
  have pos : a'.head = b'.head := la.1.trans rb.1.symm
  unfold mix
  congr 1
  funext i
  by_cases h : leftOf cut i = s
  · cases s <;> simp_all
  · have cells := rb.2 i h
    cases s <;> cases side : leftOf cut i <;> simp_all

private def Halts (M : Machine) (c : Absolute M) (b : Bool) : Prop :=
  ∃ fuel es, trace M fuel c = some (b,es)

private theorem halts_step {c : Absolute M} {w d q b} (code : instruction M c = .step w d q)
    (next : Halts M (advance c w d q) b) : Halts M c b := by
  obtain ⟨fuel,es,run⟩ := next
  exact ⟨fuel+1,record c.head d q es,by simp [trace,code,run]⟩

private def continues (M : Machine) (b : Bool) : Exit M → Prop
  | .stop decision => decision = b
  | .hand c => Halts M c b

private theorem finish_part {c : Absolute M} {cut s out} (part : Part M cut s c out)
    (b : Bool) (rest : continues M b out) : Halts M c b := by
  induction part with
  | stop here code =>
    change _ = b at rest
    exact ⟨1,[],by simp [trace,code,rest]⟩
  | cross here code away => exact halts_step code rest
  | more here code tail ih => exact halts_step code (ih rest)

private theorem sew (M : Machine) (cut : Int) (xs : List (State M)) (s : Bool)
    (a b : Absolute M) (decision : Bool)
    (left : Phases M cut s a decision xs) (right : Phases M cut s b decision xs) :
    Halts M (mix cut s a b) decision := by
  induction xs generalizing s a b with
  | nil =>
    cases left with
    | last part => exact finish_part (transfer_part part b) decision rfl
  | cons q qs ih =>
    cases left with
    | @next _ _ a' _ _ _ lp qa ls =>
      cases right with
      | @next _ _ b' _ _ _ rp qb rs =>
        have swap := handover lp rp (qa.trans qb.symm)
        have later := ih (!s) b' a' rs ls
        apply finish_part (transfer_part lp b) decision
        change Halts M (mix cut s a' b) decision
        exact swap ▸ later

private theorem start_mix (M : Machine) (l₁ l₂ r₁ r₂ : Word) (len : l₁.length=l₂.length) :
    mix (l₁.length : Int) true (start M (l₁++r₁)) (start M (l₂++r₂)) = start M (l₁++r₂) := by
  unfold mix start embed initial
  congr 1
  funext i
  cases i with
  | negSucc j => simp [Tape.ofInput,observe]
  | ofNat j =>
    simp only [Int.sub_zero,observe,Tape.ofInput,List.map_append,leftOf,decide_eq_true_eq]
    by_cases h : j < l₁.length
    · have on : Int.ofNat j < (l₁.length : Int) := Int.ofNat_lt.mpr h
      rw [ite_eq_left on]
      have in₁ : j < (l₁.map Symbol.bit).length := by simpa using h
      simp only [List.getD,List.getElem?_append_left in₁]
    · have off : ¬ Int.ofNat j < (l₁.length : Int) := fun t => h (Int.ofNat_lt.mp t)
      rw [ite_eq_right off]
      have out₁ : (l₁.map Symbol.bit).length ≤ j := by simp; omega
      have out₂ : (l₂.map Symbol.bit).length ≤ j := by simp; omega
      simp only [List.getD,List.getElem?_append_right out₁,List.getElem?_append_right out₂,
        List.length_map,len]

/-- The unrestricted finite-control machine may rewrite either half and
    revisit the cut any number of times. The accepting mixed run has its
    own finite running time; the two donor clocks need not agree. -/
theorem splice_accept {M : Machine} {l₁ l₂ r₁ r₂ : Word} {f₁ f₂ : Nat}
    {t₁ t₂ : List (Event M)} (sz : l₁.length = l₂.length) (hpos : 0 < l₁.length)
    (run₁ : inputTrace M f₁ (l₁++r₁) = some (true,t₁))
    (run₂ : inputTrace M f₂ (l₂++r₂) = some (true,t₂))
    (same : sequence (l₁.length : Int) t₁ = sequence (l₁.length : Int) t₂) :
    Accepts M (l₁++r₂) := by
  let cut : Int := l₁.length
  have side (w : Word) : leftOf cut (start M w).head = true := by
    change decide (0 < (l₁.length : Int)) = true
    simp [hpos]
  have left := split_trace M cut f₁ (start M _) run₁
  have right := split_trace M cut f₂ (start M _) run₂
  rw [side,same] at left
  rw [side] at right
  have mixed := sew M cut _ true _ _ true left right
  rw [start_mix M _ _ _ _ sz] at mixed
  obtain ⟨fuel,es,run⟩ := mixed
  exact accepts_of_trace run

end Mobius.CrossingRun
