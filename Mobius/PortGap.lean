import Mobius.LockedGap
import Mobius.AxisPortCost

/-! A short double-counting criterion for the weak spectrum gap needed by
    the three-port board. The certificate pool's pair frequencies are
    explicit inputs below. No theorem here assumes the stronger gap 282. -/
namespace Mobius.PortGap
open Mobius.LockedGap (sumN sum_le sum_add sum_congr)

private theorem total_const (l : List α) (c : Nat) : sumN l (fun _ => c)=l.length*c := by
  induction l with
  | nil => simp [sumN]
  | cons x l ih => change c+sumN l (fun _ => c)=(l.length+1)*c; rw [ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_swap (l : List α) (m : List β) (f : α → β → Nat) :
    sumN l (fun x => sumN m (f x)) = sumN m (fun y => sumN l (fun x => f x y)) := by
  induction l with
  | nil => change 0=sumN m (fun _ => 0); rw [total_const,Nat.mul_zero]
  | cons x l ih =>
    change sumN m (f x)+sumN l (fun a => sumN m (f a)) = sumN m (fun y => f x y + sumN l (fun a => f a y))
    rw [ih,sum_add]

private theorem mem_le (xs : List α) (p : α → Nat) (x : α) (hx : x∈xs) :
    p x ≤ sumN xs p := by
  induction xs with
  | nil => contradiction
  | cons a xs ih => change p x ≤ p a + sumN xs p
                    rcases List.mem_cons.mp hx with rfl | h
                    · omega
                    · have := ih h; omega

/-- Uniform family of actual finite templates, with one bit recording
    membership of a test in each template. Repetitions in the pool carry
    their literal multiplicity. -/
structure Pool (T F : Type) where
  rows : List T
  contains : T → F → Bool

def degree (p : Pool T F) (r : F) := sumN p.rows fun t => (p.contains t r).toNat
def together (p : Pool T F) (r q : F) :=
  sumN p.rows fun t => (p.contains t r && p.contains t q).toNat

private theorem demand (p : Pool T F) (r : F) (others : List F)
    (covered : ∀ t∈p.rows, p.contains t r=true → ∃ q∈others, p.contains t q=true) :
    degree p r ≤ sumN others (together p r) := by
  rw [show sumN others (together p r) =
      sumN p.rows (fun t => sumN others (fun q => (p.contains t r && p.contains t q).toNat)) from sum_swap ..]
  apply sum_le
  intro t ht
  cases e : p.contains t r
  · exact Nat.zero_le _
  · obtain ⟨q,hq,h⟩ := covered t ht e
    simpa only [Bool.true_and,h,Bool.toNat_true] using mem_le others (fun a => (p.contains t a).toNat) q hq

def Paired (p : Pool T F) (d : List F) :=
  ∀ t∈p.rows, ∀ r∈d, p.contains t r=true → ∃ q∈d, q≠r ∧ p.contains t q=true

/-- Every nonempty even difference has weight at least fifteen, from
    the largest conditional pair frequency alone. -/
theorem code_distance (p : Pool T F) (d : List F) (nd : d.Nodup) (ne : d≠[])
    (paired : Paired p d) (size : ∀ r∈d, degree p r=40320)
    (upper : ∀ r∈d, ∀ q∈d, r≠q → together p r q ≤ 2880) : 15≤d.length := by
  cases d with
  | nil => contradiction
  | cons r rest =>
    have hr : r∈r::rest := by simp
    have h := demand p r rest (by
      intro t ht hit
      obtain ⟨q,hq,other,yes⟩ := paired t ht r hr hit
      exact ⟨q,(List.mem_cons.mp hq).resolve_left other,yes⟩)
    rw [size r hr] at h
    have cap := sum_le rest (together p r) (fun _ => 2880) (fun q hq =>
      upper r hr q (by simp [hq]) (fun eq => (List.nodup_cons.mp nd).1 (eq ▸ hq)))
    rw [total_const] at cap
    simp only [List.length_cons]
    omega

/-- Sum over both orders of the incidence matrix. In the reference
    direction, `holes` are the tests missing from the optimum and
    `kept` the tests still failed. All other failures are `outside`. -/
theorem direction_bound (p : Pool T F) (holes kept outside : List F)
    (cover : ∀ r∈holes, ∀ t∈p.rows, p.contains t r=true → ∃ q∈outside, p.contains t q=true)
    (size : ∀ r∈holes, degree p r=40320)
    (balance : ∀ q∈outside, sumN holes (fun r => together p r q)+sumN kept (fun r => together p r q)=40320)
    (lower : ∀ r∈kept, ∀ q∈outside, 160≤together p r q)
    (e : Nat) (mass : outside.length=holes.length+e) :
    kept.length*outside.length ≤ 252*e := by
  have first := sum_le holes (fun _ => 40320) (fun r => sumN outside (together p r)) (fun r hr =>
    (size r hr) ▸ demand p r outside (cover r hr))
  rw [total_const,sum_swap] at first
  have col (q : F) (hq : q∈outside) :
      sumN holes (fun r => together p r q)+kept.length*160 ≤ 40320 := by
    have raw := sum_le kept (fun _ => 160) (fun r => together p r q) (fun r hr => lower r hr q hq)
    rw [total_const] at raw
    have full := balance q hq
    omega
  have cols := sum_le outside _ (fun _ => 40320) col
  rw [total_const,sum_add,total_const] at cols
  have algebra : outside.length*(kept.length*160)=(kept.length*outside.length)*160 := by
    rw [←Nat.mul_assoc,Nat.mul_comm outside.length kept.length]
  rw [algebra] at cols
  rw [mass,Nat.add_mul] at cols
  rw [mass]
  omega

/-- The finite arithmetic needs just the most frequent direction (at least
    nine hits) and `e≤4`. -/
theorem short_difference (e h E : Nat) (small : 1≤e ∧ e≤4) (split : E+h=128)
    (heavy : 9≤E) (bound : E*(h+e)≤252*e) : 2*h+e<15 := by
  have checked : ∀ e : Fin 5, ∀ h : Fin 120,
    (128-h.val)*(h.val+e.val)≤252*e.val → 2*h.val+e.val<15 := by decide
  have hlt : h<120 := by omega
  have z : 128-h=E := by omega
  have numeric : (128-h)*(h+e)≤252*e := z ▸ bound
  exact checked ⟨e,by omega⟩ ⟨h,hlt⟩ numeric

theorem no_small_excess (p : Pool T F) (holes kept outside : List F) (e : Nat)
    (small : 1≤e ∧ e≤4) (split : kept.length+holes.length=128) (heavy : 9≤kept.length)
    (mass : outside.length=holes.length+e)
    (nd : (holes++outside).Nodup) (paired : Paired p (holes++outside))
    (size : ∀ r∈holes++outside, degree p r=40320)
    (upper : ∀ r∈holes++outside, ∀ q∈holes++outside, r≠q → together p r q ≤ 2880)
    (cover : ∀ r∈holes, ∀ t∈p.rows, p.contains t r=true → ∃ q∈outside, p.contains t q=true)
    (balance : ∀ q∈outside, sumN holes (fun r => together p r q)+sumN kept (fun r => together p r q)=40320)
    (lower : ∀ r∈kept, ∀ q∈outside, 160≤together p r q) : False := by
  have nonempty : holes++outside≠[] := by
    intro none
    have h := congrArg List.length none
    simp only [List.length_append,List.length_nil] at h
    omega
  have dist := code_distance p _ nd nonempty paired size upper
  rw [List.length_append,mass] at dist
  have bd := direction_bound p holes kept outside cover (fun r hr => size r (by simp [hr])) balance lower e mass
  rw [mass] at bd
  have short := short_difference e holes.length kept.length small split heavy bd
  omega

/-- The punctured local theorem needs only this weak anchored weight gap. -/
def Gap266 : Prop := ∀ r c : AxisPortCost.Phase, TwoPhases.failures r c≠256 → 266≤TwoPhases.failures r c

theorem geometric_local (weak : Gap266) (p : SignObstruction.B) (small : AxisPortCost.admissible p)
    (r c : AxisPortCost.Phase) : 126≤AxisPortCost.geometricRetained p r c ∧
      (AxisPortCost.geometricRetained p r c=126 ↔ AxisPortCost.Picked p r c) := by
  have twice := AxisPortCost.retained_twice p r c
  by_cases best : TwoPhases.failures r c=256
  · have ok := AxisPortCost.weighted_local p small r c
    unfold AxisPortCost.weighted at ok
    rw [best,twice] at ok
    constructor
    · omega
    · exact ⟨fun hit => ok.2.mp (by omega),fun hit => by have := ok.2.mpr hit; omega⟩
  · have total := AxisPortCost.partition p r c
    have removed := AxisPortCost.removed_le p small r c
    have bound := weak r c best
    refine ⟨by omega,⟨fun eq => False.elim (by omega),?_⟩⟩
    rintro ⟨a,h,profile⟩
    exact False.elim (best (Rigidity.optimal_of_direction profile))

/-- Frequency histogram of the original 15-square certificate. Enumerate
    the columns of each invertible binary matrix, send the two directions to
    1 and 2, and quotient the anchor by the two opposite-anchor moves. -/
def orbitBins : Array Nat := Id.run do
  let mut bins := Array.replicate 64 0
  for u in [1:16] do
    for v in [1:16] do
      if v != u then
        let q := #[0,u,v,u^^^v]
        for w in [1:16] do
          if !(q.contains w) then
            let h := q ++ q.map (· ^^^ w)
            for z in [1:16] do
              if !(h.contains z) then
                let image := h ++ h.map (· ^^^ z)
                let mut dx := 0
                let mut dy := 0
                for (x,y,d) in TwoPhases.certificate do
                  let dest := image[d.toNat]!
                  if dest=1 || dest=2 then
                    dx := dx ^^^ image[x.toNat]!
                    dy := dy ^^^ image[y.toNat]!
                let key := 16*(dx/4)+(dx^^^dy)
                bins := bins.modify key (·+1)
  return bins

abbrev orbitCheck := orbitBins.size=64 ∧ orbitBins.toList.sum=20160 ∧
    orbitBins.toList.all (fun n => 160≤n && n≤2880)=true

/-- Classify all linear relations of four columns (u,v,x,y) relative
    to independent u,v. A zero digit means the vector is outside their
    span. Digits 1,2,3,4 indicate 0,u,v,u+v respectively. -/
private def digit (u v x : Nat) := if x=0 then 1 else if x=u then 2 else if x=v then 3 else if x=u^^^v then 4 else 0
private def relationKey (u v x y : Nat) := digit u v x + 5*digit u v y + 25*digit u v (x^^^y)

private def sourceTypes : Array Nat := Id.run do
  let mut hist := Array.replicate 125 0
  for (x,y,u) in TwoPhases.certificate do
    for (a,b,v) in TwoPhases.certificate do
      if u != v then
        let delta := x ^^^ a
        let key := relationKey u.toNat v.toNat delta.toNat (delta ^^^ y ^^^ b).toNat
        hist := hist.modify key (·+1)
  return hist

/-- Once the images of the two directions and two anchor differences are
    fixed, a rank-2/3/4 partial linear map has 96/8/1 completions. -/
private def completions (key : Nat) :=
  if key=0 then 1 else if key%5 != 0 && key/5%5 != 0 then 96 else 8

private def canonicalMass (hist : Array Nat) (q : Nat) :=
  ((List.range 4).map (fun shift =>
    let key := relationKey 1 2 (4*(q/16)+shift) (q%16)
    hist[key]! * completions key)).sum

/-- A small kernel computation of all normed pair counts. The direct GL
    enumerator `orbitBins` and the Python checker compute the same table
    by scanning bases. The generic counting theorem above explicitly takes
    its actual-template incidence hypotheses. -/
theorem compressed_counts :
    let c := (List.range 64).map (canonicalMass sourceTypes)
    c.sum=20160 ∧ c.all (fun mass => 160≤mass && mass≤2880)=true := by decide +kernel

end Mobius.PortGap
