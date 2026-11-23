import Mobius.FourBitPortCut

/-! The 78-face instance has no descending single-cell move from any
full-board minimizer. Its nearest sparse optimum differs in two tagged bits. -/
namespace Mobius.PortCutEdits
open Mobius.SignObstruction (B Rectangle total shifts)
open Mobius.TwoPhases (TaggedCell corners score failures)
open Mobius.OneInThree (Phase)
open Mobius.FourBitPortCut (faces cost costOn nearRow nearCol)

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

abbrev Board := TaggedCell → Bool

def pack (r c : Phase) : Board := fun p => if p.1 then c p.2.1 p.2.2 else r p.2.1 p.2.2
def row (a : Board) : Phase := fun x y => a (false,x,y)
def col (a : Board) : Phase := fun x y => a (true,x,y)
def sparse (a : Board) := cost (row a) (col a)
def full (a : Board) := failures (row a) (col a)

def flip (a : Board) (p : TaggedCell) : Board := fun t => a t ^^ decide (t=p)
def setCell (a : Board) (p : TaggedCell) (b : Bool) : Board := fun t => if t=p then b else a t

theorem pack_projections (a : Board) : pack (row a) (col a) = a := by
  funext p
  rcases p with ⟨t,x,y⟩
  cases t <;> rfl

private theorem score_total (a : Board) (q : Rectangle) : score (row a) (col a) q = total a (corners q) := by
  change total (pack (row a) (col a)) _ = _
  rw [pack_projections]

private theorem total_xor (a b : Board) (cs : List TaggedCell) :
    total (fun p => a p ^^ b p) cs = (total a cs ^^ total b cs) := by
  induction cs with
  | nil => rfl
  | cons x xs ih =>
    simp only [total,ih]
    generalize a x = i; generalize b x = j
    generalize total a xs = k; generalize total b xs = l
    cases i <;> cases j <;> cases k <;> cases l <;> rfl

/-- This bit is precisely the parity change incurred by editing the cell. -/
def hit (p : TaggedCell) (q : Rectangle) : Bool := total (fun t => decide (t=p)) (corners q)

theorem score_flip (a : Board) (p : TaggedCell) (q : Rectangle) :
    score (row (flip a p)) (col (flip a p)) q = (score (row a) (col a) q ^^ hit p q) := by
  rw [score_total,score_total]
  exact total_xor a (fun t => decide (t=p)) (corners q)

def incident (p : TaggedCell) := faces.filter (hit p)

private theorem nonzero : ∀ q ∈ faces, q.2.2 ≠ 0 := by decide

/-- At a fixed tagged address there is at most one selected square in
each direction. Every address has degree zero or at least two. -/
theorem incident_profile : ∀ p : TaggedCell,
    ((incident p).map (fun q => q.2.2)).Nodup ∧ (incident p).length ≠ 1 := by
  intro ⟨t,x,y⟩
  revert t x y
  decide +kernel

private theorem bad_incident (a : Board) (p : TaggedCell) (ha : full a = 256) :
    (incident p).countP (fun q => !(score (row a) (col a) q)) ≤ 1 := by
  obtain ⟨d,pat,_⟩ := Mobius.Rigidity.optimal_direction (row a) (col a) ha
  have same : (incident p).countP (fun q => !(score (row a) (col a) q)) =
      (incident p).countP (fun q => q.2.2 == d) := by
    apply List.countP_congr
    intro q hq
    obtain ⟨x,y,e⟩ := q
    have hm := (List.mem_filter.mp hq).1
    rw [pat.2 x y e (nonzero _ hm)]
    by_cases he : e=d <;> simp [he]
  have hn := List.nodup_iff_count.mp (incident_profile p).1 d
  rw [List.count_eq_countP,List.countP_map] at hn
  exact same ▸ hn

private def bad (a : Board) (q : Rectangle) := !(score (row a) (col a) q)

/-- The loss change is degree minus twice the number of incident old failures. -/
theorem flip_balance (a : Board) (p : TaggedCell) :
    sparse (flip a p) + 2 * (incident p).countP (bad a) = sparse a + (incident p).length := by
  have count (qs : List Rectangle) :
      qs.countP (bad (flip a p)) + 2*(qs.filter (hit p)).countP (bad a) =
      qs.countP (bad a) + (qs.filter (hit p)).length := by
    induction qs with
    | nil => rfl
    | cons q qs ih =>
      have relation : bad (flip a p) q = (bad a q ^^ hit p q) := by
        unfold bad
        rw [score_flip]
        cases score (row a) (col a) q <;> cases hit p q <;> rfl
      cases hh : hit p q <;> cases hb : bad a q <;>
        simp [relation,hh,hb] <;> omega
  exact count faces

/-- No flip can improve the sparse score of any global minimizer. -/
theorem one_flip_bound (a : Board) (p : TaggedCell) (ha : full a = 256) :
    sparse a ≤ sparse (flip a p) := by
  have eqn := flip_balance a p
  have hn := (incident_profile p).2
  have b : (incident p).countP (bad a) ≤ 1 := bad_incident a p ha
  have le := List.countP_le_length (p:=bad a) (l:=incident p)
  omega

private theorem set_eq_or_flip (a : Board) (p : TaggedCell) (b : Bool) :
    setCell a p b = a ∨ setCell a p b = flip a p := by
  by_cases h : b=a p
  · left; subst b; funext t; by_cases ht : t=p <;> simp [setCell,ht]
  · right; funext t
    by_cases ht : t=p
    · subst t
      cases b <;> cases ha : a p <;> simp_all [setCell,flip]
    · simp [setCell,flip,ht]

theorem one_replacement_bound (a : Board) (p : TaggedCell) (b : Bool) (ha : full a = 256) :
    sparse a ≤ sparse (setCell a p b) := by
  rcases set_eq_or_flip a p b with h|h
  · rw [h]; exact Nat.le_refl _
  · rw [h]; exact one_flip_bound a p ha

def cells : List TaggedCell := [false,true].flatMap fun t => shifts.map fun pos => (t,pos)

private theorem all_cells (p : TaggedCell) : p ∈ cells := by
  rcases p with ⟨t,x,y⟩
  have h := Mobius.SignObstruction.shifts_complete (x,y)
  cases t <;> simp [cells,h]

def disagreements (a b : Board) := cells.filter fun p => decide (a p ≠ b p)
def hamming (a b : Board) := (disagreements a b).length

private theorem mem_disagreements (a b : Board) (p : TaggedCell) :
    p ∈ disagreements a b ↔ a p ≠ b p := by simp [disagreements,all_cells p]

private theorem near_eq_or_edit (a b : Board) (hl : hamming a b < 2) :
    b=a ∨ ∃ p, b=setCell a p (b p) := by
  cases hd : disagreements a b with
  | nil =>
    left; funext t
    have ht := mem_disagreements a b t
    rw [hd] at ht
    exact Eq.symm (Classical.byContradiction (fun h => List.not_mem_nil (ht.mpr h)))
  | cons p ps =>
    have h' : ps.length=0 := by
      unfold hamming at hl; rw [hd,List.length_cons] at hl; omega
    have hempty := List.length_eq_zero_iff.mp h'
    right; refine ⟨p,?_⟩; funext t
    by_cases he : t=p
    · simp [setCell,he]
    · have ht := mem_disagreements a b t
      rw [hd,hempty] at ht
      have same : a t=b t := Classical.byContradiction (fun h => he (by simpa using ht.mpr h))
      simp [setCell,he,same]

theorem distance_lower (a b : Board) (ha : full a = 256) (hb : sparse b = 2) :
    2 ≤ hamming a b := by
  have best := FourBitPortCut.best_among_board_optima.1 (row a) (col a) ha
  change 3 ≤ sparse a at best
  by_cases close : hamming a b < 2
  · rcases near_eq_or_edit a b close with same | ⟨p,edit⟩
    · rw [same] at hb; omega
    · have h := one_replacement_bound a p (b p) ha
      rw [←edit] at h; omega
  · omega

/-- Common row/column starting table before the two edits at (row,1,3)
and (column,7,3). -/
def ground : Board := fun t =>
  (115340367647218111683266917363723575547885951215506551248727091356869701795840 : Nat).testBit
    (16*t.2.1.toNat+t.2.2.toNat)

def nearby : Board := pack nearRow nearCol

theorem ground_witness : full ground = 256 ∧ sparse ground = 3 := by decide +kernel
theorem two_edits : disagreements ground nearby = [(false,1,3),(true,7,3)] := by decide +kernel
theorem nearby_witness : sparse nearby = 2 ∧ full nearby = 304 := FourBitPortCut.near_witness

theorem minimum_hamming :
    (∀ a b : Board, full a = 256 → sparse b = 2 → 2 ≤ hamming a b) ∧
    (∃ a b : Board, full a = 256 ∧ sparse b = 2 ∧ hamming a b = 2) := by
  refine ⟨distance_lower,ground,nearby,ground_witness.1,nearby_witness.1,?_⟩
  unfold hamming
  rw [two_edits]
  rfl

end Mobius.PortCutEdits
