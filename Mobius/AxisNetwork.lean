import Mobius.AxisPortCost

/-! A linear coordinate atlas compiles a simultaneous one-of-the-designated-
axes problem into a total cost on a single actual pair of ambient sign tables.
The weighted statement has no gap assumption. -/
namespace Mobius.AxisNetwork
open Mobius.SignObstruction (B)
open Mobius.AxisGlue (Axis Atlas World bits restrict Matching)
open Mobius.AxisPortCost (Phase admissible Picked retained weighted Gap282)

/-- Add the cost of each board's explicit tests. Repeated rows, if present,
are counted by their board occurrences. -/
def cost (T : Atlas k v) (p : Fin k → B) (measure : B → Phase → Phase → Nat)
    (r c : World v) :=
  ((List.finRange k).map fun i => measure (p i) (restrict r T i) (restrict c T i)).sum

def Feasible (T : Atlas k v) (p : Fin k → B) :=
  ∃ pick : Fin k → Axis, Matching T pick ∧ ∀ i, bits (p i) (pick i)=true

private theorem lower_sum (xs : List α) (f : α → Nat) (t : Nat) (low : ∀ x∈xs, t ≤ f x) :
    xs.length*t ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := low x (by simp)
    have tail := ih (fun a ha => low a (by simp [ha]))
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.succ_mul]; omega

private theorem all_eq (xs : List α) (f : α → Nat) (t : Nat) (low : ∀ x∈xs, t ≤ f x)
    (cap : (xs.map f).sum ≤ xs.length*t) : ∀ x∈xs, f x=t := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have tailLow := fun b (hb : b∈xs) => low b (by simp [hb])
    have hl := lower_sum xs f t tailLow
    have ha := low a (by simp)
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.succ_mul] at cap
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hs
    · omega
    · exact ih tailLow (by omega) x hs

theorem global_lower (T : Atlas k v) (p : Fin k → B) (good : ∀ i, admissible (p i))
    (measure : B → Phase → Phase → Nat) (base : Nat)
    (localLow : ∀ b, admissible b → ∀ r c, base ≤ measure b r c)
    (r c : World v) : k*base ≤ cost T p measure r c := by
  have h := lower_sum (List.finRange k) (fun i => measure (p i) (restrict r T i) (restrict c T i))
    base (fun i _ => localLow (p i) (good i) _ _)
  simpa only [cost,List.length_finRange] using h

theorem exact_network (T : Atlas k v) (p : Fin k → B) (good : ∀ i, admissible (p i))
    (measure : B → Phase → Phase → Nat) (base : Nat)
    (spec : ∀ b, admissible b → ∀ r c, base ≤ measure b r c ∧ (measure b r c=base ↔ Picked b r c)) :
    (∃ r c : World v, cost T p measure r c ≤ k*base) ↔ Feasible T p := by
  constructor
  · rintro ⟨r,c,budget⟩
    let price := fun i => measure (p i) (restrict r T i) (restrict c T i)
    have each (i : Fin k) : price i = base :=
      all_eq (List.finRange k) price base (fun j _ => (spec (p j) (good j) _ _).1)
        (by simpa only [cost,price,List.length_finRange] using budget) i (List.mem_finRange i)
    have allowed (i : Fin k) := (spec (p i) (good i) (restrict r T i) (restrict c T i)).2.mp (each i)
    let pick (i : Fin k) := Classical.choose (allowed i)
    have hp (i : Fin k) := Classical.choose_spec (allowed i)
    exact ⟨pick,AxisGlue.matching_necessary T pick r c (fun i => (hp i).2),fun i => (hp i).1⟩
  · rintro ⟨pick,ok,allowed⟩
    obtain ⟨t,h⟩ := AxisGlue.pasted_optima T pick ok
    have eq (i : Fin k) : measure (p i) (restrict t T i) (restrict t T i)=base :=
      (spec (p i) (good i) _ _).2.mpr ⟨pick i,allowed i,(h i).1⟩
    refine ⟨t,t,?_⟩
    unfold cost
    have hs (xs : List (Fin k)) : (xs.map (fun _ => base)).sum = xs.length*base := by
      induction xs with
      | nil => simp
      | cons a xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]
    rw [List.map_congr_left (fun i _ => eq i),hs,List.length_finRange]
    exact Nat.le_refl _

theorem weighted_iff (T : Atlas k v) (p : Fin k → B) (good : ∀ i, admissible (p i)) :
    (∃ r c : World v, cost T p weighted r c ≤ k*2300) ↔ Feasible T p :=
  exact_network T p good weighted 2300 AxisPortCost.weighted_local

theorem unweighted_iff (gap : Gap282) (T : Atlas k v) (p : Fin k → B) (good : ∀ i, admissible (p i)) :
    (∃ r c : World v, cost T p retained r c ≤ k*252) ↔ Feasible T p :=
  exact_network T p good retained 252 (AxisPortCost.retained_local gap)

theorem geometric_iff (gap : Gap282) (T : Atlas k v) (p : Fin k → B) (good : ∀ i, admissible (p i)) :
    (∃ r c : World v, cost T p AxisPortCost.geometricRetained r c ≤ k*126) ↔ Feasible T p :=
  exact_network T p good AxisPortCost.geometricRetained 126 (AxisPortCost.geometric_local gap)

/-- A solution is an ordinary Boolean labeling of the physical coordinates.
On every board exactly one of the four bits is set and its axis is permitted. -/
def BooleanSolution (T : Atlas k v) (p : Fin k → B) :=
  ∃ z : Fin v → Bool, ∀ i, ∃ a, bits (p i) a=true ∧ ∀ b, z (T.loc i b)=decide (b=a)

theorem feasible_iff_boolean (T : Atlas k v) (p : Fin k → B) :
    Feasible T p ↔ BooleanSolution T p := by
  constructor
  · rintro ⟨pick,ok,allowed⟩
    let z := fun w => (List.finRange k).any fun i => T.loc i (pick i) == w
    refine ⟨z,fun i => ⟨pick i,allowed i,fun b => ?_⟩⟩
    apply Bool.eq_iff_iff.mpr
    simp only [z,List.any_eq_true,List.mem_finRange,true_and,beq_iff_eq,decide_eq_true_eq]
    constructor
    · rintro ⟨j,h⟩
      exact ((ok j i (pick j) b h).mp rfl).symm
    · rintro rfl; exact ⟨i,rfl⟩
  · rintro ⟨z,localBits⟩
    let pick i := Classical.choose (localBits i)
    have hp i := Classical.choose_spec (localBits i)
    refine ⟨pick,?_,fun i => (hp i).1⟩
    intro i j a b shared
    have h := ((hp i).2 a).symm.trans ((congrArg z shared).trans ((hp j).2 b))
    have core : ∀ a b c d : Axis, decide (a=b)=decide (c=d) → (b=a ↔ d=c) := by decide
    exact core _ _ _ _ h


/-- Shared coordinates really are ports of each incident board; the other
coordinates are private padding axes. -/
def AllSharedArePorts (T : Atlas k v) (p : Fin k → B) :=
  ∀ i j, i≠j → ∀ a b, T.loc i a=T.loc j b → bits (p i) a=true

def actualTest (T : Atlas k v) (i : Fin k) (r : SignObstruction.Rectangle) :=
  (AxisGlue.embed T i r.1,AxisGlue.embed T i r.2.1,AxisGlue.embed T i r.2.2)

/-- Under the port-incidence condition a retained directed test of one board
cannot even belong to another board. This also rules out a second copy in
reverse orientation, since the other local triple here is arbitrary. -/
theorem retained_private (T : Atlas k v) (p : Fin k → B) (allPorts : AllSharedArePorts T p)
    {i j : Fin k} (ne : i≠j) (r t : SignObstruction.Rectangle) (nz : r.2.2≠0)
    (ret : AxisPortCost.dropTest (p i) r=false) : actualTest T i r ≠ actualTest T j t := by
  intro same
  obtain ⟨x,y,d⟩ := r; obtain ⟨u,w,e⟩ := t
  simp only [actualTest,Prod.mk.injEq] at same
  obtain ⟨a,b,hit,dir,hx,hy⟩ := AxisGlue.shared_test_line T ne nz same.1 same.2.1 same.2.2
  have designated : ∀ mask a, AxisPortCost.designated mask (AxisGlue.unit a) = bits mask a := by decide
  have on := allPorts i j ne a b hit
  change d=AxisGlue.unit a at dir
  change x=0 ∨ x=d at hx
  change y=0 ∨ y=d at hy
  subst d
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [AxisPortCost.dropTest,designated,on] at ret

end Mobius.AxisNetwork
