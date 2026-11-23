import Mobius.OptimalCertificate

/-!
The least fraction of failed square constraints for a four-bit signed crossing.
The 15-square certificate has one representative per nonzero direction.
Independent translations of the first and second proof indices partition all
3840 anchored rectangles into 256 parity certificates. Quotienting away a
single direction attains the lower bound.
-/
namespace Mobius.SignObstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def translate (shift : Cell) (r : Rectangle) : Rectangle :=
  (shift.1 ^^^ r.1, shift.2 ^^^ r.2.1, r.2.2)

def shiftedPhase (phase : B → B → Bool) (shift : Cell) (x y : B) : Bool :=
  phase (shift.1 ^^^ x) (shift.2 ^^^ y)

theorem oddAt_translate (p : B → B → Bool) (s : Cell) (r : Rectangle) :
    oddAt p (translate s r) ↔ oddAt (shiftedPhase p s) r := by
  obtain ⟨x,y,d⟩ := r
  simp [oddAt, translate, shiftedPhase, total, corners, BitVec.xor_assoc]

theorem representative_exists (d : B) (hd : d ≠ 0) :
    ∃ r ∈ certificate, r.2.2 = d := by
  revert d hd; decide

theorem representative_unique : ∀ r ∈ certificate, ∀ q ∈ certificate,
    r.2.2 = q.2.2 → r = q := by decide

/-- Every anchored square comes from a translated certificate. -/
theorem translate_surjects (r : Rectangle) (valid : r.2.2 ≠ 0) :
    ∃ s : Cell, ∃ q ∈ certificate, translate s q = r := by
  obtain ⟨q,hq,hdir⟩ := representative_exists r.2.2 valid
  refine ⟨(r.1 ^^^ q.1, r.2.1 ^^^ q.2.1),q,hq,?_⟩
  obtain ⟨x,y,d⟩ := r; obtain ⟨a,b,e⟩ := q
  simp_all [translate, BitVec.xor_assoc]

/-- Every anchored square occurs only once in this partition, even though
the same unanchored four cells admit four choices of anchor. -/
theorem translate_unique (s t : Cell) {r q : Rectangle}
    (hr : r ∈ certificate) (hq : q ∈ certificate)
    (he : translate s r = translate t q) : s = t ∧ r = q := by
  have projected := congrArg (fun z : Rectangle => z.2.2) he
  have eqdir : r.2.2 = q.2.2 := projected
  have er := representative_unique r hr q hq eqdir
  subst q
  obtain ⟨u,v⟩ := s; obtain ⟨a,b⟩ := t
  simp [translate] at he
  exact ⟨Prod.ext he.1 he.2,rfl⟩

def badIn (phase : B → B → Bool) (s : Cell) : List Rectangle :=
  certificate.filter (fun r => !(total (fun q : Cell => phase q.1 q.2) (corners (translate s r))))

theorem badAtEveryShift (p : B → B → Bool) (s : Cell) : 1 ≤ (badIn p s).length := by
  apply Nat.zero_lt_of_ne_zero
  intro empty
  apply fifteen_inconsistent
  refine ⟨shiftedPhase p s, ?_⟩
  intro r hr
  apply (oddAt_translate p s r).1
  cases eqn : total (fun q : Cell => p q.1 q.2) (corners (translate s r)) with
  | true => exact eqn
  | false =>
    have mem : r ∈ badIn p s := List.mem_filter.mpr ⟨hr,by simp [eqn]⟩
    have pos := List.length_pos_of_mem mem
    omega

def alphabet : List B := List.ofFn (fun i : Fin 16 => BitVec.ofNat 4 i.val)
def shifts : List Cell := alphabet.flatMap fun x => alphabet.map fun y => (x,y)

theorem shifts_complete (s : Cell) : s ∈ shifts := by obtain ⟨x,y⟩ := s; revert x y; decide
theorem shifts_nodup : shifts.Nodup := by decide

def failures (p : B → B → Bool) := (shifts.map (fun s => (badIn p s).length)).sum

theorem failures_lower (p : B → B → Bool) : 256 ≤ failures p := by
  have count (xs : List Cell) : xs.length ≤ (xs.map (fun s => (badIn p s).length)).sum := by
    induction xs with
    | nil => simp
    | cons s xs ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have := badAtEveryShift p s
      omega
  exact count shifts

/-- Omit direction 8 by reading only the low three bits. -/
def repairPhase (x y : B) : Bool := Mobius.EightSquare.phase (x.setWidth 3) (y.setWidth 3)

theorem repair_signature (x y d : B) (hd : d ≠ 0) :
    total (fun q : Cell => repairPhase q.1 q.2) (corners (x,y,d)) = decide (d ≠ 8) := by
  revert x y d hd
  decide

theorem repair_count_each (s : Cell) : (badIn repairPhase s).length = 1 := by
  have eqn : badIn repairPhase s = certificate.filter (fun r => decide (r.2.2 = 8)) := by
    unfold badIn
    apply List.filter_congr
    intro r hr
    have nz : ∀ q ∈ certificate, q.2.2 ≠ 0 := by decide
    rw [show translate s r = (s.1 ^^^ r.1, s.2 ^^^ r.2.1, r.2.2) by rfl,
      repair_signature _ _ _ (nz r hr)]
    simp
  rw [eqn]; decide

theorem repair_optimal : failures repairPhase = 256 := by
  unfold failures
  simp only [repair_count_each]
  decide

end Mobius.SignObstruction
