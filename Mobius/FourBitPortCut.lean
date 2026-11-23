import Mobius.OneInThree
import Mobius.Rigidity

/-! A K4 port network inside the *original* pair of four-bit tables.
These concrete charts can have additional cell coincidences. The lower
bound uses four odd dependencies in the actual emitted rows; the upper
bound is one pair of tables evaluated at all 78 distinct squares. -/
namespace Mobius.FourBitPortCut
open Mobius.SignObstruction (B Rectangle total total_append total_perm total_paired)
open Mobius.TwoPhases (TaggedCell corners score)
open Mobius.OneInThree (Phase internalNot)

structure Chart where
  a : B
  b : B
  c : B
  d : B
  sx : B
  sy : B

def lin (g : Chart) (w : B) : B :=
  (if w.getLsbD 0 then g.a else 0) ^^^ (if w.getLsbD 1 then g.b else 0) ^^^
  (if w.getLsbD 2 then g.c else 0) ^^^ (if w.getLsbD 3 then g.d else 0)

def embed (g : Chart) (r : Rectangle) : Rectangle :=
  (g.sx ^^^ lin g r.1,g.sy ^^^ lin g r.2.1, lin g r.2.2)

-- In order 01, 02, 03, 12, 13, 23.
def wires : List (List Rectangle) :=
  ([⟨1,2,4,8,0,0⟩, ⟨4,2,5,10,0,4⟩, ⟨14,2,1,9,0,10⟩, ⟨9,12,1,14,4,0⟩,
    ⟨3,12,5,13,4,14⟩, ⟨5,15,4,12,5,15⟩] : List Chart).map fun g => internalNot.map (embed g)

def faces := wires.flatten

private def oriented (r : Rectangle) : Rectangle :=
  if r.1 < r.1 ^^^ r.2.2 then r else (r.1 ^^^ r.2.2, r.2.1 ^^^ r.2.2, r.2.2)

theorem distinct_faces : faces.length = 78 ∧ (faces.map oriented).Nodup := by decide

def costOn (rs : List Rectangle) (r c : Phase) := rs.countP (fun q => !(score r c q))
def cost (r c : Phase) := costOn faces r c

def select3 (a b c : Nat) := wires[a]! ++ wires[b]! ++ wires[c]!
private def halves (xs : List TaggedCell) :=
  xs.eraseDups.flatMap fun c => List.replicate (xs.count c / 2) c

private def evenCorners (rs : List Rectangle) :=
  let xs := rs.flatMap corners
  xs.Perm ((halves xs).flatMap fun c => [c,c])

private theorem parity_bound (rs : List Rectangle) (even : evenCorners rs)
    (odd : total (fun _ : Rectangle => true) rs = true) (r c : Phase) :
    1 ≤ costOn rs r c := by
  have zero (f : TaggedCell → Bool) : total f (rs.flatMap corners) = false :=
    (total_perm f even).trans (total_paired f _)
  let f := fun (p : TaggedCell) => if p.1 then c p.2.1 p.2.2 else r p.2.1 p.2.2
  have flatten (qs : List Rectangle) : total (score r c) qs = total f (qs.flatMap corners) := by
    induction qs with
    | nil => rfl
    | cons q qs ih => rw [List.flatMap_cons,total_append,←ih]; rfl
  have one : ∃ q ∈ rs, score r c q = false := by
    apply Classical.byContradiction
    intro none
    have all (q : Rectangle) (mem : q ∈ rs) : score r c q = true := by
      cases h : score r c q with
      | true => rfl
      | false => exact False.elim (none ⟨q,mem,h⟩)
    have same (qs : List Rectangle) (h : ∀ q ∈ qs, score r c q = true) :
        total (score r c) qs = total (fun _ => true) qs := by
      induction qs with
      | nil => rfl
      | cons q qs ih =>
        simp only [total,h q (by simp),ih (fun p hp => h p (by simp [hp]))]
    have bad := (flatten rs).symm.trans ((same rs all).trans odd)
    rw [zero f] at bad
    contradiction
  obtain ⟨q,mem,fail⟩ := one
  exact List.countP_pos_iff.mpr ⟨q,mem,by simp [fail]⟩

private theorem triangle_certificates :
    ∀ t ∈ ([(0,1,3), (0,2,4), (1,2,5), (3,4,5)] :
      List (Nat × Nat × Nat)), evenCorners (select3 t.1 t.2.1 t.2.2) ∧
        total (fun _ : Rectangle => true) (select3 t.1 t.2.1 t.2.2) = true := by
  unfold evenCorners; decide +kernel

private theorem append_cost (xs ys : List Rectangle) (r c : Phase) :
    costOn (xs++ys) r c = costOn xs r c + costOn ys r c := List.countP_append

theorem lower (r c : Phase) : 2 ≤ cost r c := by
  have each (a b d : Nat) (h : (a,b,d) ∈ ([(0,1,3),(0,2,4),(1,2,5),(3,4,5)] : List (Nat × Nat × Nat))) :
      1 ≤ costOn wires[a]! r c + costOn wires[b]! r c + costOn wires[d]! r c := by
    obtain ⟨even,odd⟩ := triangle_certificates _ h
    simpa only [select3,append_cost] using parity_bound _ even odd r c
  have h₁ := each 0 1 3 (by decide)
  have h₂ := each 0 2 4 (by decide)
  have h₃ := each 1 2 5 (by decide)
  have h₄ := each 3 4 5 (by decide)
  have all : faces = wires[0]! ++ wires[1]! ++ wires[2]! ++ wires[3]! ++ wires[4]! ++ wires[5]! := by decide
  unfold cost; rw [all]; simp only [append_cost]; omega

private def table (mask : Nat) : Phase := fun x y => mask.testBit (16*x.toNat+y.toNat)

def witnessRow : Phase := table 226164189177522500245151737758017633069269865194634599156977890305702363136
def witnessCol : Phase := table 29117639627547775358470814009643733826051453228222242992937472458760344698880

theorem sparse_minimum : (∀ r c : Phase, 2 ≤ cost r c) ∧ cost witnessRow witnessCol = 2 :=
  ⟨lower,by decide +kernel⟩

theorem board_optimum_profile (r c : Phase) (opt : Mobius.TwoPhases.failures r c = 256) :
    cost r c = 3 ∨ cost r c = 6 := by
  obtain ⟨d,pat,_⟩ := Mobius.Rigidity.optimal_direction r c opt
  have good : ∀ q ∈ faces, q.2.2 ≠ 0 := by decide
  have count : cost r c = faces.countP (fun q => decide (q.2.2 = d)) := by
    apply List.countP_congr
    intro q mem
    obtain ⟨x,y,e⟩ := q
    change (!(score r c (x,y,e))) = true ↔ decide (e=d) = true
    rw [pat.2 x y e (good _ mem)]
    by_cases equal : e = d <;> simp [equal]
  rw [count]
  have sizes : ∀ d : B, d ≠ 0 →
      faces.countP (fun q => decide (q.2.2=d)) = 3 ∨
      faces.countP (fun q => decide (q.2.2=d)) = 6 := by decide +kernel
  exact sizes d pat.1

theorem best_among_board_optima :
    (∀ r c : Phase, Mobius.TwoPhases.failures r c = 256 → 3 ≤ cost r c) ∧
    (∃ r c : Phase, Mobius.TwoPhases.failures r c = 256 ∧ cost r c = 3) := by
  refine ⟨fun r c h => ?_,⟨_,_,Mobius.TwoPhases.repair_optimal,by decide +kernel⟩⟩
  rcases board_optimum_profile r c h with h | h <;> omega

def nearRow : Phase := table 115340367647218111683266917363723575547885951215506551248727091356869701271552
def nearCol : Phase := table 115340367647218111683266917363723575547885909677131682970106063112899068035072

set_option maxRecDepth 32768 in
theorem near_witness : cost nearRow nearCol = 2 ∧ Mobius.TwoPhases.failures nearRow nearCol = 304 := by
  decide +kernel

end Mobius.FourBitPortCut
