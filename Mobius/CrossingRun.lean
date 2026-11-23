import Complexity.BoundedExecution
import Complexity.Classes

/-! Absolute coordinates for a write-before-move two-way one-tape machine.
A moving transition contributes its crossed boundary and its incoming control
state. Staying put and halting contribute no crossing events. Halting, like
every other instruction, still consumes one transition of the original clock. -/
namespace Mobius.CrossingRun
open Complexity

abbrev State (M : Machine) := Fin (M.states + 1)
abbrev Event (M : Machine) := Int × State M

structure Absolute (M : Machine) where
  state : State M
  head : Int
  cells : Int → Symbol

def delta : Move → Int
  | .left => -1
  | .stay => 0
  | .right => 1

def observe (t : Tape) : Int → Symbol
  | .ofNat i => t.right.getD i .blank
  | .negSucc i => t.left.getD i .blank

theorem observe_move (t : Tape) (d : Move) (i : Int) :
    observe (t.move d) i = observe t (i + delta d) := by
  cases d with
  | stay => simp [delta,Tape.move]
  | left =>
    cases i with
    | ofNat i =>
      cases i with
      | zero => exact Tape.move_left_right_getD_zero t
      | succ i =>
        rw [show Int.ofNat (i+1) + delta Move.left = Int.ofNat i by simp [delta]; omega]
        exact Tape.move_left_right_getD_succ t i
    | negSucc i =>
      rw [show Int.negSucc i + delta Move.left = Int.negSucc (i+1) by simp [delta]; omega]
      exact Tape.move_left_left_getD t i
  | right =>
    cases i with
    | ofNat i =>
      rw [show Int.ofNat i + delta Move.right = Int.ofNat (i+1) by simp [delta]]
      exact Tape.move_right_right_getD t i
    | negSucc i =>
      cases i with
      | zero => exact Tape.move_right_left_getD_zero t
      | succ i =>
        rw [show Int.negSucc (i+1) + delta Move.right = Int.negSucc i by simp [delta]; omega]
        exact Tape.move_right_left_getD_succ t i

theorem observe_write (t : Tape) (w : Symbol) (i : Int) :
    observe (t.write w) i = if i = 0 then w else observe t i := by
  cases i with
  | ofNat i =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [ite_eq_right (show Int.ofNat (i+1) ≠ 0 by intro h; cases h)]
      exact Tape.write_right_getD_succ t w i
  | negSucc i => exact Tape.write_left_getD t w i

def embed (M : Machine) (c : Config M) (pos : Int) : Absolute M :=
  ⟨c.state,pos,fun i => observe c.tape (i-pos)⟩

def advance (c : Absolute M) (w : Symbol) (d : Move) (q : State M) : Absolute M :=
  ⟨q,c.head+delta d,fun i => if i=c.head then w else c.cells i⟩

def instruction (M : Machine) (c : Absolute M) := M.code c.state (c.cells c.head)

theorem instruction_embed (M : Machine) (c : Config M) (pos : Int) :
    instruction M (embed M c pos) = M.code c.state c.tape.read := by
  simp only [instruction, embed, Int.sub_self]
  rw [Tape.read_eq_getD]
  rfl

theorem advance_embed (M : Machine) (c : Config M) (pos : Int) (w : Symbol) (d : Move) (q : State M) :
    advance (embed M c pos) w d q = embed M ⟨q,(c.tape.write w).move d⟩ (pos+delta d) := by
  unfold advance embed
  congr 1
  funext i
  rw [observe_move,show i - (pos + delta d) + delta d = i-pos by omega,observe_write]
  by_cases h : i=pos <;> simp_all [Int.sub_eq_zero]

/-- The right-hand cell is the integer naming a boundary. -/
def record (pos : Int) (d : Move) (q : State M) (es : List (Event M)) : List (Event M) :=
  match d with
  | .left => (pos,q)::es
  | .right => (pos+1,q)::es
  | .stay => es

def trace (M : Machine) : Nat → Absolute M → Option (Bool × List (Event M))
  | 0, _ => none
  | fuel+1, c =>
    match instruction M c with
    | .halt b => some (b,[])
    | .step w d q => (trace M fuel (advance c w d q)).map (fun (b,t) => (b,record c.head d q t))

def start (M : Machine) (w : Word) := embed M (initial M w) 0

def inputTrace (M : Machine) (fuel : Nat) (w : Word) := trace M fuel (start M w)

theorem trace_agrees (M : Machine) (fuel : Nat) (c : Config M) (pos : Int) :
    (trace M fuel (embed M c pos)).map Prod.fst = (run M fuel c).map Prod.fst := by
  induction fuel generalizing c pos with
  | zero => rfl
  | succ fuel ih =>
    rw [trace,run,instruction_embed]
    cases h : M.code c.state c.tape.read with
    | halt b => rfl
    | step w d q =>
      simp only [advance_embed,Option.map_map]
      exact ih _ _

theorem trace_length {M : Machine} {fuel : Nat} {c : Absolute M} {b : Bool} {es : List (Event M)}
    (h : trace M fuel c = some (b,es)) : es.length ≤ fuel := by
  induction fuel generalizing c es with
  | zero => contradiction
  | succ fuel ih =>
    rw [trace] at h
    cases hi : instruction M c with
    | halt s =>
      rw [hi] at h
      have nil := congrArg (fun p : Bool × List (Event M) => p.2) (Option.some.inj h)
      simp_all
    | step w d q =>
      rw [hi] at h
      cases ht : trace M fuel (advance c w d q) with
      | none => simp [ht] at h
      | some p =>
        obtain ⟨s,t⟩ := p
        simp only [ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        have len := ih ht
        cases d <;> simp [record] <;> omega

theorem trace_of_runInput {M : Machine} {fuel : Nat} {w : Word} {b : Bool} {out : Tape}
    (run : runInput M fuel w = some (b,out)) :
    ∃ es, inputTrace M fuel w = some (b,es) ∧ es.length ≤ fuel := by
  have h := trace_agrees M fuel (initial M w) 0
  change (inputTrace M fuel w).map Prod.fst = (runInput M fuel w).map Prod.fst at h
  rw [run] at h
  cases ht : inputTrace M fuel w with
  | none => simp [ht] at h
  | some v =>
    obtain ⟨s,es⟩ := v
    simp only [ht,Option.map_some,Option.some.injEq] at h
    subst s
    exact ⟨es,rfl,trace_length ht⟩

theorem accepts_of_trace {M : Machine} {fuel : Nat} {w : Word} {es : List (Event M)}
    (h : inputTrace M fuel w = some (true,es)) : Accepts M w := by
  have agree := trace_agrees M fuel (initial M w) 0
  change (inputTrace M fuel w).map Prod.fst = (runInput M fuel w).map Prod.fst at agree
  rw [h] at agree
  cases out : runInput M fuel w with
  | none => simp [out] at agree
  | some p =>
    obtain ⟨b,t⟩ := p
    simp only [out,Option.map_some,Option.some.injEq] at agree
    subst b
    exact ⟨fuel,t,out⟩

def sequence (cut : Int) : List (Event M) → List (State M)
  | [] => []
  | (pos,q) :: es => if pos=cut then q :: sequence cut es else sequence cut es

/-- True is the left side of the boundary. -/
def leftOf (cut pos : Int) : Bool := decide (pos < cut)

private theorem crossing_cases (pos cut : Int) (d : Move) :
    (leftOf cut pos ≠ leftOf cut (pos+delta d)) ↔
      (d = .left ∧ pos = cut) ∨ (d = .right ∧ pos+1 = cut) := by
  have different (p q : Prop) [Decidable p] [Decidable q] :
      decide p ≠ decide q ↔ (p ∧ ¬q) ∨ (¬p ∧ q) := by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]
  unfold leftOf
  rw [different]
  cases d <;> simp [delta] <;> omega

theorem sequence_record (pos cut : Int) (d : Move) (q : State M) (es : List (Event M)) :
    sequence cut (record pos d q es) =
      if leftOf cut pos = leftOf cut (pos+delta d) then sequence cut es else q::sequence cut es := by
  have h := crossing_cases pos cut d
  cases d with
  | stay => simp [record,delta]
  | left =>
    simp only [record,sequence]
    by_cases eq : pos=cut <;> simp_all
  | right =>
    simp only [record,sequence]
    by_cases eq : pos+1=cut <;> simp_all

theorem crossing_head (pos cut : Int) (d : Move) (s : Bool)
    (before : leftOf cut pos=s) (after : leftOf cut (pos+delta d) ≠ s) :
    pos+delta d = if s then cut else cut-1 := by
  have h := (crossing_cases pos cut d).1 (by intro e; exact after (e ▸ before))
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,e⟩
  · simp [leftOf] at before
    simp [before,delta]; omega
  · have left : leftOf cut pos=true := by simp [leftOf]; omega
    rw [left] at before
    subst s
    simpa [delta] using e

end Mobius.CrossingRun
