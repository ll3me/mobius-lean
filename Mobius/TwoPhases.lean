import Mobius.Defect

/-!
# Two independent phase tables on a four-bit crossing

The row and column phases have distinct domains of variables, marked by a
Boolean tag. A finite odd dependency in the off-diagonal equations rejects
all pairs of sign tables. The Python search only supplied rectangle indices;
the proof checks their parity internally for arbitrary tables.
-/

namespace Mobius.TwoPhases

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Mobius.SignObstruction (B Cell Rectangle total total_append total_perm total_paired)

abbrev TaggedCell := Bool × Cell

def corners (r : Rectangle) : List TaggedCell :=
  let (x,y,d) := r
  [(false,x,y), (false,x ^^^ d,y ^^^ d), (true,x,y ^^^ d), (true,x ^^^ d,y)]

def SignedCancellation {n : Nat} (row col : BitVec n → BitVec n → Bool) : Prop :=
  ∀ x y d, d ≠ 0 →
    (row x y ^^ (row (x ^^^ d) (y ^^^ d) ^^
      (col x (y ^^^ d) ^^ col (x ^^^ d) y))) = true

def certificate : List Rectangle :=
  [(0,5,2), (0,5,5), (0,8,8), (0,8,15), (2,3,6),
   (2,3,7), (2,7,4), (2,14,10), (2,14,13), (4,5,1),
   (4,8,11), (4,8,12), (5,0,3), (6,14,9), (6,14,14)]

def allCells := certificate.flatMap corners

/-- Every tagged cell in this certificate occurs exactly twice. -/
def halfCells := allCells.eraseDups

theorem paired_cells : allCells.Perm (halfCells.flatMap fun c => [c,c]) := by decide

theorem certificate_size :
    certificate.length = 15 ∧ allCells.eraseDups.length = 30 := by decide

private theorem parity_sum (f : TaggedCell → Bool) (rs : List Rectangle)
    (odd : ∀ r ∈ rs, total f (corners r) = true) :
    total f (rs.flatMap corners) = total (fun _ => true) rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons, total_append, odd r (by simp), ih (fun u hu => odd u (by simp [hu]))]
    rfl

theorem no_four_bit_phases (row col : B → B → Bool) : ¬SignedCancellation row col := by
  intro compatible
  let val : TaggedCell → Bool := fun (color,x,y) => if color then col x y else row x y
  have nz : ∀ r ∈ certificate, r.2.2 ≠ 0 := by decide
  have odd := parity_sum val certificate (by
    intro r hr
    obtain ⟨x,y,d⟩ := r
    simpa [corners, val, total] using compatible x y d (nz _ hr))
  have even := (total_perm val paired_cells).trans (total_paired val halfCells)
  have parity : total (fun _ => true) certificate = true := by decide
  change total val allCells = _ at odd
  rw [parity, even] at odd
  contradiction

theorem no_wider_phases (n : Nat) (width : 4 ≤ n) (row col : BitVec n → BitVec n → Bool) :
    ¬SignedCancellation row col := by
  intro good
  apply no_four_bit_phases (fun x y => row (x.setWidth n) (y.setWidth n))
    (fun x y => col (x.setWidth n) (y.setWidth n))
  intro x y d hd
  have nz : d.setWidth n ≠ 0 := by
    intro zero
    have lower := congrArg (BitVec.setWidth 4) zero
    apply hd
    simpa [BitVec.setWidth_setWidth_of_le _ width] using lower
  simpa using good (x.setWidth n) (y.setWidth n) (d.setWidth n) nz

def sign (phase : Bool) : Int := if phase then -1 else 1

private theorem parity_of_zero (a b c d : Bool)
    (h : sign a * sign b + sign c * sign d = 0) : a ^^ (b ^^ (c ^^ d)) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [sign]

/-- The obstruction in the integer form of the proposed rank-one factors. -/
theorem no_integer_cancellation (n : Nat) (width : 4 ≤ n)
    (row col : BitVec n → BitVec n → Bool) :
    ¬ (∀ x y d, d ≠ 0 →
      sign (row x y) * sign (row (x ^^^ d) (y ^^^ d)) +
      sign (col x (y ^^^ d)) * sign (col (x ^^^ d) y) = 0) := by
  intro cancel
  exact no_wider_phases n width row col
    (fun x y d nz => parity_of_zero _ _ _ _ (cancel x y d nz))

theorem yes_three_bits :
    ∃ row col : BitVec 3 → BitVec 3 → Bool, SignedCancellation row col := by
  refine ⟨Mobius.EightSquare.phase, Mobius.EightSquare.phase, ?_⟩
  unfold SignedCancellation
  decide



def Fits (row col : B → B → Bool) (r : Rectangle) : Prop :=
  let (x,y,d) := r
  (row x y ^^ (row (x ^^^ d) (y ^^^ d) ^^
    (col x (y ^^^ d) ^^ col (x ^^^ d) y))) = true

/-- Omitting even one nonzero direction leaves a satisfiable system: pull
back a width-three solution along the linear quotient by that direction. -/
theorem every_direction_needed (rs : List Rectangle)
    (nz : ∀ r ∈ rs, r.2.2 ≠ 0)
    (infeasible : ¬∃ row col, ∀ r ∈ rs, Fits row col r) (h : B) (hh : h ≠ 0) :
    h ∈ rs.map (fun r => r.2.2) := by
  apply Classical.byContradiction
  intro missing
  apply infeasible
  obtain ⟨row,col,odd⟩ := yes_three_bits
  refine ⟨fun x y => row (Mobius.SignObstruction.quotient h x) (Mobius.SignObstruction.quotient h y),
          fun x y => col (Mobius.SignObstruction.quotient h x) (Mobius.SignObstruction.quotient h y), ?_⟩
  intro r hr
  obtain ⟨x,y,d⟩ := r
  have dh : d ≠ h := by
    intro e
    apply missing
    exact List.mem_map.mpr ⟨(x,y,d), hr, e⟩
  have nd := Mobius.SignObstruction.quotient_nonzero h d hh (nz _ hr) dh
  simpa [Fits, Mobius.SignObstruction.quotient_linear] using odd (Mobius.SignObstruction.quotient h x) (Mobius.SignObstruction.quotient h y) (Mobius.SignObstruction.quotient h d) nd



open Mobius.SignObstruction (translate shiftedPhase shifts repairPhase)

def score (row col : B → B → Bool) (r : Rectangle) : Bool :=
  total (fun (tag,x,y) => if tag then col x y else row x y) (corners r)

theorem fifteen_inconsistent : ¬ ∃ row col, ∀ r ∈ certificate, score row col r = true := by
  rintro ⟨row,col,h⟩
  let val : TaggedCell → Bool := fun (tag,x,y) => if tag then col x y else row x y
  have one := parity_sum val certificate h
  have even := (total_perm val paired_cells).trans (total_paired val halfCells)
  have parity : total (fun _ => true) certificate = true := by decide
  change total val allCells = _ at one
  rw [parity, even] at one
  contradiction

theorem score_translate (row col : B → B → Bool) (s : Cell) (r : Rectangle) :
    score row col (translate s r) = score (shiftedPhase row s) (shiftedPhase col s) r := by
  obtain ⟨x,y,d⟩ := r
  simp [score, translate, shiftedPhase, total, corners, BitVec.xor_assoc]

/-- The 256 translated certificates partition all 3840 anchored rectangles. -/
theorem unique_anchoring (z : Rectangle) (hz : z.2.2 ≠ 0) :
    ∃ s : Cell, ∃ r ∈ certificate, translate s r = z ∧
      ∀ t q, q ∈ certificate → translate t q = z → t = s ∧ q = r := by
  have covers : ∀ d : B, d ≠ 0 → ∃ r ∈ certificate, r.2.2 = d := by decide
  have uniq : ∀ r ∈ certificate, ∀ q ∈ certificate, r.2.2 = q.2.2 → r=q := by decide
  obtain ⟨r,hr,hd⟩ := covers z.2.2 hz
  let s : Cell := (z.1 ^^^ r.1, z.2.1 ^^^ r.2.1)
  have back : translate s r = z := by
    obtain ⟨x,y,d⟩ := z
    obtain ⟨a,b,e⟩ := r
    simp_all [translate, s, BitVec.xor_assoc]
  refine ⟨s, r, hr, back, ?_⟩
  intro t q hq heq
  have same := heq.trans back.symm
  have proj := congrArg (fun r : Rectangle => r.2.2) same
  have eqr := uniq q hq r hr proj
  subst q
  obtain ⟨u,v⟩ := t
  obtain ⟨a,b,e⟩ := r
  simp [translate] at same
  exact ⟨Prod.ext same.1 same.2, rfl⟩

def badIn (row col : B → B → Bool) (s : Cell) :=
  certificate.filter (fun r => !score row col (translate s r))

private theorem bad_each (row col : B → B → Bool) (s : Cell) :
    1 ≤ (badIn row col s).length := by
  apply Nat.zero_lt_of_ne_zero
  intro empty
  apply fifteen_inconsistent
  refine ⟨shiftedPhase row s,shiftedPhase col s,?_⟩
  intro r hr
  rw [← score_translate]
  cases h : score row col (translate s r) with
  | true => rfl
  | false =>
    have mem : r ∈ badIn row col s := List.mem_filter.mpr ⟨hr,by simp [h]⟩
    have := List.length_pos_of_mem mem
    omega

def failures (row col : B → B → Bool) := (shifts.map (fun s => (badIn row col s).length)).sum

theorem failures_lower (row col : B → B → Bool) : 256 ≤ failures row col := by
  have count (xs : List Cell) : xs.length ≤ (xs.map (fun s => (badIn row col s).length)).sum := by
    induction xs with
    | nil => simp
    | cons s xs ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have := bad_each row col s
      omega
  exact count shifts

private theorem equal_phase_score (p : B → B → Bool) (r : Rectangle) :
    score p p r = total (fun c : Cell => p c.1 c.2) (Mobius.SignObstruction.corners r) := by
  obtain ⟨x,y,d⟩ := r
  simp [score, corners, Mobius.SignObstruction.corners,total,Bool.xor_left_comm,Bool.xor_comm]

private theorem repair_each (s : Cell) : (badIn repairPhase repairPhase s).length = 1 := by
  have eqn : badIn repairPhase repairPhase s = certificate.filter (fun r => decide (r.2.2 = 8)) := by
    unfold badIn
    apply List.filter_congr
    intro r hr
    have nz : ∀ r ∈ certificate, r.2.2 ≠ 0 := by decide
    rw [equal_phase_score, show translate s r = (s.1 ^^^ r.1,s.2 ^^^ r.2.1,r.2.2) by rfl,
        Mobius.SignObstruction.repair_signature _ _ _ (nz r hr)]
    simp
  rw [eqn]; decide

theorem repair_optimal : failures repairPhase repairPhase = 256 := by
  unfold failures
  simp only [repair_each]
  decide

/-- Exact count in the anchored measure; 256 out of 3840 equals 1/15. -/
theorem optimum_failure_fraction :
    (∀ row col, 256 ≤ failures row col) ∧
    (∃ row col, failures row col = 256) ∧ shifts.length * certificate.length = 3840 :=
  ⟨failures_lower, ⟨repairPhase,repairPhase,repair_optimal⟩, by decide⟩

end Mobius.TwoPhases
