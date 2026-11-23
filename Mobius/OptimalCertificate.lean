import Mobius.SignObstruction

/-! Optimality of the four-bit obstruction. Drop any one nonzero direction
and quotient by it: the remaining requirements pull back from the valid
eight-square phase on three bits. Thus no contradiction with fewer than
15 individual local squares exists in this precise ansatz. -/
namespace Mobius.SignObstruction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def pivot (d : B) : Nat :=
  if d.getLsbD 0 then 0 else if d.getLsbD 1 then 1 else if d.getLsbD 2 then 2 else 3

/-- Quotient by the line {0,d}: clear the pivot coordinate by adding d,
then delete the cleared coordinate. -/
def quotient (d x : B) : BitVec 3 :=
  let i := pivot d
  let r := if x.getLsbD i then x ^^^ d else x
  BitVec.ofNat 3 ((r.toNat % 2^i) + (r.toNat / 2^(i+1)) * 2^i)

theorem quotient_linear (d x y : B) :
    quotient d (x ^^^ y) = (quotient d x ^^^ quotient d y) := by
  revert d x y
  decide

theorem quotient_nonzero (d s : B) (hd : d ≠ 0) (hs : s ≠ 0) (hne : s ≠ d) :
    quotient d s ≠ 0 := by
  revert hd hs hne d s
  decide

def oddAt (phase : B → B → Bool) (r : Rectangle) :=
  total (fun p : Cell => phase p.1 p.2) (corners r) = true

theorem repair_except (d : B) (hd : d ≠ 0) :
    ∃ phase : B → B → Bool, ∀ x y s, s ≠ 0 → s ≠ d → oddAt phase (x,y,s) := by
  obtain ⟨small, hsmall⟩ := eight_exists
  refine ⟨fun x y => small (quotient d x) (quotient d y), ?_⟩
  intro x y s hs hne
  simpa [oddAt, corners, total, quotient_linear] using
    hsmall (quotient d x) (quotient d y) (quotient d s) (quotient_nonzero d s hd hs hne)

def directions : List B := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]

theorem any_fourteen_consistent (rs : List Rectangle)
    (valid : ∀ r ∈ rs, r.2.2 ≠ 0) (small : rs.length < 15) :
    ∃ phase : B → B → Bool, ∀ r ∈ rs, oddAt phase r := by
  have omitted : ∃ d ∈ directions, d ∉ rs.map (fun r => r.2.2) := by
    apply Classical.byContradiction
    intro none
    have covers : directions ⊆ rs.map (fun r => r.2.2) := by
      intro d hd
      exact Classical.byContradiction (fun h => none ⟨d,hd,h⟩)
    have bound := List.Nodup.length_le_of_subset (show directions.Nodup by decide) covers
    simp [directions] at bound
    omega
  obtain ⟨d, hd, missing⟩ := omitted
  have nz : d ≠ 0 := fun h => (show (0:B) ∉ directions by decide) (h ▸ hd)
  obtain ⟨phase, good⟩ := repair_except d nz
  refine ⟨phase, ?_⟩
  rintro ⟨x,y,s⟩ hr
  apply good x y s (valid _ hr)
  intro eqn
  exact missing (List.mem_map.mpr ⟨(x,y,s),hr,eqn⟩)

theorem fifteen_inconsistent :
    ¬ ∃ phase : B → B → Bool, ∀ r ∈ certificate, oddAt phase r := by
  rintro ⟨phase, h⟩
  let f : Cell → Bool := fun p => phase p.1 p.2
  have odd := sum_corners f certificate h
  have even := (total_perm f cells_paired).trans (total_paired f usedCells)
  have one : total (fun _ => true) certificate = true := by decide
  rw [one, even] at odd
  contradiction

end Mobius.SignObstruction
