import Mobius.RigidityPairs
import Mobius.RigidityCount

/-! Every optimal four-bit signing concentrates its failed squares in one
entire direction. The argument is a partition bound with equality: two
failures in distinct directions would occur together inside a certificate
whose 255 other translates already each have at least one failure. -/
namespace Mobius.Rigidity
open Mobius.SignObstruction (B Cell Rectangle directions shifts translate)
open Mobius.TwoPhases (certificate score)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem dir_mem (d : B) : d ∈ directions ↔ d ≠ 0 := by revert d; decide

private theorem chart_dirs (g : Chart) : (directions.map g.act).Perm directions := by
  have nd : directions.Nodup := by decide
  apply (List.perm_ext_iff_of_nodup (nd.map _ (fun _ _ h e => h (g.inj e))) nd).2
  intro d
  constructor
  · intro h
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
    apply (dir_mem _).2
    intro hz
    exact (dir_mem _).1 he (g.inj (hz.trans g.zero.symm))
  · intro hd
    refine List.mem_map.mpr ⟨g.inv d,(dir_mem _).2 ?_,g.right _⟩
    intro hz
    have h := g.right d
    rw [hz,g.zero] at h
    exact (dir_mem _).1 hd h.symm

private theorem chart_template (g : Chart) : IsTemplate (certificate.map (mapRect g.act)) := by
  have base : (certificate.map dir).Perm directions := by decide
  have p := (base.map g.act).trans (chart_dirs g)
  simpa only [IsTemplate,List.map_map,Function.comp_def,dir,mapRect] using p

private theorem score_chart (g : Chart) (row col : B → B → Bool) (r : Rectangle) :
    score row col (mapRect g.act r) = score (fun x y => row (g.act x) (g.act y))
      (fun x y => col (g.act x) (g.act y)) r := by
  obtain ⟨x,y,d⟩ := r
  simp only [score,mapRect,Mobius.TwoPhases.corners,Mobius.SignObstruction.total,g.linear]

private theorem chart_bad (g : Chart) (row col : B → B → Bool) (s : Cell) :
    ∃ r ∈ certificate, score row col (translate s (mapRect g.act r)) = false := by
  apply Classical.byContradiction
  intro hn
  apply Mobius.TwoPhases.fifteen_inconsistent
  let row' := Mobius.SignObstruction.shiftedPhase row s
  let col' := Mobius.SignObstruction.shiftedPhase col s
  refine ⟨fun x y => row' (g.act x) (g.act y),fun x y => col' (g.act x) (g.act y),?_⟩
  intro r hr
  rw [← score_chart]
  change score (Mobius.SignObstruction.shiftedPhase row s) (Mobius.SignObstruction.shiftedPhase col s) _ = true
  rw [← Mobius.TwoPhases.score_translate]
  cases hv : score row col (translate s (mapRect g.act r)) with
  | false => exact False.elim (hn ⟨r,hr,hv⟩)
  | true => rfl

private theorem exact_one {f : α → Nat} {xs : List α} (all : ∀ x, 1 ≤ f x)
    (eqn : (xs.map f).sum = xs.length) : ∀ x ∈ xs, f x = 1 := by
  have minimum (ys : List α) : ys.length ≤ (ys.map f).sum := by
    induction ys with
    | nil => simp
    | cons y ys ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; have := all y; omega
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons] at eqn
    have := minimum xs
    have := all a
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · omega
    · exact ih (by omega) z hz

private theorem chart_exact (row col : B → B → Bool)
    (opt : Mobius.TwoPhases.failures row col = 256) (g : Chart) (s : Cell) :
    hits (twoBad row col) (certificate.map (mapRect g.act)) s = 1 := by
  let rs := certificate.map (mapRect g.act)
  let f := hits (twoBad row col) rs
  have all (t : Cell) : 1 ≤ f t := by
    obtain ⟨r,hr,hfalse⟩ := chart_bad g row col t
    apply List.length_pos_of_mem (a := mapRect g.act r)
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨r,hr,rfl⟩,by simp [twoBad,hfalse]⟩
  have counted := total_of_template (twoBad row col) rs (chart_template g)
  have eqn : (shifts.map f).sum = shifts.length := calc
    _ = totalDefects (twoBad row col) := counted
    _ = Mobius.TwoPhases.failures row col := (two_count row col).symm
    _ = 256 := opt
    _ = shifts.length := by decide
  exact exact_one all eqn s (Mobius.SignObstruction.shifts_complete s)

private theorem singleton_inj {l : List α} {x y : α} (hl : l.length = 1) (hx : x ∈ l) (hy : y ∈ l) : x = y := by
  cases l with
  | nil => simp at hx
  | cons a tail =>
    have empty : tail.length = 0 := by simpa using hl
    have nilTail := List.length_eq_zero_iff.mp empty
    simp [nilTail] at hx hy
    exact hx.trans hy.symm

/-- Any two failed directed squares of an optimal signing have the same direction. -/
theorem bad_same_direction (row col : B → B → Bool) (opt : Mobius.TwoPhases.failures row col = 256)
    (x y d x' y' e : B) (hd : d ≠ 0) (he : e ≠ 0)
    (first : score row col (x,y,d) = false) (second : score row col (x',y',e) = false) : d = e := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨g,s,r,q,a,b,hr,hq,diff,eqr,eqq⟩ := pair_in_chart x y d x' y' e hd he hne
  have flag {r : Rectangle} {turn : Bool} {z : Rectangle}
      (mem : r ∈ certificate) (eqn : flip (translate s (mapRect g.act r)) turn = z)
      (bad : score row col z = false) :
      mapRect g.act r ∈ ((certificate.map (mapRect g.act)).filter fun t => twoBad row col (translate s t)) := by
    have val := (score_flip row col (translate s (mapRect g.act r)) turn).symm
    rw [eqn,bad] at val
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨r,mem,rfl⟩,by simp [twoBad,val]⟩
  have same := singleton_inj (chart_exact row col opt g s) (flag hr eqr first) (flag hq eqq second)
  obtain ⟨x₀,y₀,d₀⟩ := r
  obtain ⟨x₁,y₁,d₁⟩ := q
  simp only [mapRect,Prod.mk.injEq] at same
  exact diff (Prod.ext (g.inj same.1) (Prod.ext (g.inj same.2.1) (g.inj same.2.2)))

private def identityChart : Chart := ⟨id,id,fun _ _ => rfl,fun _ => rfl,fun _ => rfl⟩

private theorem plain_bad (row col : B → B → Bool) (s : Cell) :
    ∃ r ∈ certificate, score row col (translate s r) = false := by
  obtain ⟨r,hr,h⟩ := chart_bad identityChart row col s
  obtain ⟨x,y,d⟩ := r
  exact ⟨_,hr,h⟩

private theorem template_nz : ∀ r ∈ certificate, dir r ≠ 0 := by decide

private theorem template_dir_inj : ∀ r ∈ certificate, ∀ q ∈ certificate, dir r = dir q → r = q := by decide

/-- Failure occurs at every anchor in the unique exceptional nonzero
   direction, and at no anchor in any of the other fourteen directions. -/
def DirectionPattern (row col : B → B → Bool) (d : B) : Prop :=
  d ≠ 0 ∧ ∀ x y e : B, e ≠ 0 → score row col (x,y,e) = decide (e ≠ d)

theorem optimal_direction (row col : B → B → Bool) (opt : Mobius.TwoPhases.failures row col = 256) :
    ∃ d, DirectionPattern row col d ∧ ∀ e, DirectionPattern row col e → e = d := by
  obtain ⟨⟨a,b,d⟩,hr,hbad⟩ := plain_bad row col (0,0)
  have hd := template_nz _ hr
  change d ≠ 0 at hd
  have witness : score row col (a,b,d) = false := by simpa [translate] using hbad
  have unique_bad (x y e : B) (he : e ≠ 0) (bad : score row col (x,y,e) = false) : e = d :=
    bad_same_direction row col opt x y e a b d he hd bad witness
  refine ⟨d,⟨hd,?_⟩,?_⟩
  · intro x y e he
    by_cases same : e = d
    · subst e
      obtain ⟨s,r,hmem,hit,_⟩ := Mobius.TwoPhases.unique_anchoring (x,y,d) hd
      obtain ⟨q,hq,fail⟩ := plain_bad row col s
      have hrdir : dir r = d := congrArg dir hit
      have hqdir : dir q = d := unique_bad _ _ _ (template_nz q hq) fail
      have eqr := template_dir_inj q hq r hmem (hqdir.trans hrdir.symm)
      rw [eqr,hit] at fail
      simpa using fail
    · cases value : score row col (x,y,e) with
      | false => exact False.elim (same (unique_bad _ _ _ he value))
      | true => simp [same]
  · rintro e ⟨he,hp⟩
    have k := hp a b d hd
    rw [witness] at k
    by_cases de : d = e
    · exact de.symm
    · simp [de] at k

/-- A full exceptional direction occupies 256 anchored squares, with every
other square correct. -/
theorem optimal_of_direction {row col : B → B → Bool} {d : B}
    (pat : DirectionPattern row col d) : Mobius.TwoPhases.failures row col = 256 := by
  obtain ⟨hd,pattern⟩ := pat
  have one (s : Cell) : (Mobius.TwoPhases.badIn row col s).length = 1 := by
    have eqn : Mobius.TwoPhases.badIn row col s = certificate.filter (fun r => decide (dir r = d)) := by
      apply List.filter_congr
      intro r hr
      have p := pattern (s.1 ^^^ r.1) (s.2 ^^^ r.2.1) (dir r) (template_nz r hr)
      change (!score row col (s.1 ^^^ r.1,s.2 ^^^ r.2.1,dir r)) = decide (dir r = d)
      rw [p]; simp
    rw [eqn]
    have freq : ∀ t : B, t ≠ 0 → (certificate.filter (fun r => decide (dir r = t))).length = 1 := by decide
    exact freq d hd
  unfold Mobius.TwoPhases.failures
  simp only [one]
  decide

theorem optimal_iff_direction (row col : B → B → Bool) :
    Mobius.TwoPhases.failures row col = 256 ↔ ∃ d, DirectionPattern row col d :=
  ⟨fun h => let ⟨d,pat,_⟩ := optimal_direction row col h; ⟨d,pat⟩,
   fun ⟨_,pat⟩ => optimal_of_direction pat⟩

/-- Single-table specialization with the original single-table failure count. -/
theorem single_optimal_direction (p : B → B → Bool) (opt : Mobius.SignObstruction.failures p = 256) :
    ∃ d, DirectionPattern p p d ∧ ∀ e, DirectionPattern p p e → e = d :=
  optimal_direction p p ((same_count p).trans opt)

end Mobius.Rigidity
