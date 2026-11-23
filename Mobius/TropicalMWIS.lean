import Mobius.TropicalDAG
import Mobius.TourCount

/-! The exposed minima of an ordinary graph cut with all unary prices
are its independent sets. The empty set permits signed vertex weights. -/
namespace Mobius.TropicalMWIS

open Mobius.TropicalDAG

abbrev Graph (n : Nat) := List (Fin n × Fin n)
abbrev Coloring (n : Nat) := Fin n → Bool
abbrev Prices (n : Nat) := Fin n × Bool → Rat

def sumQ {α} (xs : List α) (f : α → Rat) := (xs.map f).sum

private theorem sumQ_add {α} (xs : List α) (f g : α → Rat) :
    sumQ xs (fun a => f a+g a) = sumQ xs f+sumQ xs g := by
  induction xs with
  | nil => simp [sumQ] <;> grind
  | cons x xs ih => simp_all [sumQ]; grind

private theorem sumQ_scale {α} (xs : List α) (f : α → Rat) (t : Rat) :
    sumQ xs (fun a => t*f a) = t*sumQ xs f := by
  induction xs with
  | nil => simp [sumQ] <;> grind
  | cons x xs ih => simp_all [sumQ]; grind

private theorem sumQ_sub {α} (xs : List α) (f g : α → Rat) :
    sumQ xs (fun a => f a-g a) = sumQ xs f-sumQ xs g := by
  induction xs with
  | nil => simp [sumQ]; grind
  | cons x xs ih => simp_all [sumQ]; grind

private theorem sumQ_const {α} (xs : List α) (c : Rat) :
    sumQ xs (fun _ => c) = xs.length*c := by
  induction xs with
  | nil => simp [sumQ] <;> grind
  | cons x xs ih => simp_all [sumQ]; grind

private theorem exchange {α β} (xs : List α) (ys : List β) (f : α → β → Rat) :
    sumQ xs (fun x => sumQ ys (f x)) = sumQ ys (fun y => sumQ xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    simp only [sumQ,List.map_nil,List.sum_nil]
    simpa [sumQ] using (sumQ_const ys 0).symm
  | cons x xs ih =>
    change sumQ ys (f x) + sumQ xs (fun a => sumQ ys (f a)) =
      sumQ ys (fun y => f x y + sumQ xs (fun a => f a y))
    rw [ih,sumQ_add]

private theorem delta {α} [DecidableEq α] (xs : List α) (i : α) (a : Rat) (h : xs.Nodup) :
    sumQ xs (fun j => if j=i then a else 0) = if i∈xs then a else 0 := by
  induction xs with
  | nil => simp [sumQ]
  | cons x xs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp h
    change (if x=i then a else 0)+sumQ xs (fun j => if j=i then a else 0) = _
    rw [ih tail]
    by_cases eq : x=i
    · subst i; simp [fresh,Rat.add_zero]
    · simp [eq,Ne.symm eq,Rat.zero_add]

def bit (b : Bool) : Rat := if b then 1 else 0
def degree (g : Graph n) (u : Fin n) : Rat :=
  sumQ g (fun e => (if u=e.1 then 1 else 0) + (if u=e.2 then 1 else 0))
def base (g : Graph n) : Prices n := fun (u,b) => 1+bit b * degree g u
def labels : Fin n × Bool → Option (Fin n) := fun (u,b) => if b then some u else none
def hit (z : Coloring n) (e : Fin n × Fin n) := z e.1 && z e.2
def conflicts (g : Graph n) (z : Coloring n) := g.countP (hit z)

def cutCost (g : Graph n) (z : Coloring n) := sumQ g fun e => bit (z e.1 == z e.2)
def energy (g : Graph n) (h : Prices n) (z : Coloring n) : Rat :=
    cutCost g z + sumQ (List.finRange n) (fun v => h (v,z v))

def gain (w : Fin n → Rat) (z : Coloring n) :=
    sumQ (List.finRange n) (fun u => if z u then w u else 0)

private theorem vertex_delta (v : Fin n) (f : Fin n → Rat) :
    sumQ (List.finRange n) (fun u => f u*(if u=v then 1 else 0)) = f v := by
  have eq (u : Fin n) : f u*(if u=v then 1 else 0) = if u=v then f v else 0 := by
    by_cases h : u=v <;> simp [h]
  rw [show (fun u => _) = _ from funext eq,delta _ _ _ (List.nodup_finRange n)]
  simp

private theorem count_degree (g : Graph n) (z : Coloring n) :
    sumQ (List.finRange n) (fun u => bit (z u)*degree g u) =
      sumQ g (fun e => bit (z e.1) + bit (z e.2)) := by
  let val := fun (e : Fin n × Fin n) (u : Fin n) =>
    bit (z u)*(if u=e.1 then 1 else 0) + bit (z u)*(if u=e.2 then 1 else 0)
  have distribute (u : Fin n) : bit (z u)*degree g u = sumQ g (fun e => val e u) := by
    unfold degree val
    rw [← sumQ_scale]
    congr 1; funext e; grind
  have endpoint (e : Fin n × Fin n) : sumQ (List.finRange n) (val e) =
      bit (z e.1)+bit (z e.2) := by
    dsimp [val]; rw [sumQ_add,vertex_delta,vertex_delta]
  rw [show (fun u => _) = _ from funext distribute,exchange]
  exact congrArg (sumQ g) (funext endpoint)

private theorem count_hits (g : Graph n) (z : Coloring n) :
    sumQ g (fun e => bit (hit z e)) = (conflicts g z : Rat) := by
  induction g with
  | nil => rfl
  | cons e es ih =>
    cases h : hit z e <;> simp_all [sumQ,conflicts,bit] <;> grind

/-- An incident selected endpoint pays one unit at that endpoint. The
remaining edge contribution is exactly twice the number of internal edges. -/
theorem energy_base (g : Graph n) (z : Coloring n) :
    energy g (base g) z = (n:Rat)+g.length+2*(conflicts g z : Rat) := by
  have one (e : Fin n × Fin n) : bit (z e.1 == z e.2) + (bit (z e.1)+bit (z e.2)) =
      1+2*bit (hit z e) := by
    cases hl : z e.1 <;> cases hr : z e.2 <;> simp [bit,hit,hl,hr] <;> grind
  have sum := congrArg (sumQ g) (funext one)
  clear one
  simp only [sumQ_add,sumQ_const,sumQ_scale,count_hits] at sum
  unfold energy base cutCost
  rw [sumQ_add,sumQ_const,count_degree]
  simp only [sumQ_add,List.length_finRange,Rat.mul_one]
  grind only


def perturbed (g : Graph n) (w : Fin n → Rat) (t : Rat) : Prices n :=
    fun x => base g x - t*slopeInput labels w x

theorem energy_perturbed (g : Graph n) (w : Fin n → Rat) (z : Coloring n) (t : Rat) :
    energy g (perturbed g w t) z =
      (n:Rat)+g.length+2*(conflicts g z : Rat) - t*gain w z := by
  have dir (v : Fin n) : slopeInput labels w (v,z v) = if z v then w v else 0 := by
    cases h : z v <;> simp [slopeInput,labels]
  unfold energy perturbed
  simp only [sumQ_sub,sumQ_scale,dir]
  have base_eq := energy_base g z
  unfold energy at base_eq; unfold gain; grind

private def zeroColor (n : Nat) : Coloring n := fun _ => false
private theorem zero_free (g : Graph n) : conflicts g (zeroColor n) = 0 := by
  simp [conflicts,hit,zeroColor]
private theorem zero_gain (w : Fin n → Rat) : gain w (zeroColor n) = 0 := by
  simp [gain,zeroColor,sumQ_const]

def colors (n : Nat) := Mobius.TourCount.assignments n
private theorem colors_ne (n : Nat) : colors n ≠ [] := by
  exact List.ne_nil_of_mem (Mobius.TourCount.assignments_complete (zeroColor n))

def independent (g : Graph n) := (colors n).filter (fun z => conflicts g z == 0)
private theorem independent_ne (g : Graph n) : independent g ≠ [] := by
  apply List.ne_nil_of_mem (a := zeroColor n)
  simp [independent,colors,zero_free,Mobius.TourCount.assignments_complete]

def optimum (g : Graph n) (h : Prices n) :=
  energy g h ((colors n).minOn (energy g h) (colors_ne n))

def mwis (g : Graph n) (w : Fin n → Rat) :=
  gain w ((independent g).maxOn (gain w) (independent_ne g))

private theorem independent_of_mem {g : Graph n} {z : Coloring n} (h : z∈independent g) :
    conflicts g z=0 := beq_iff_eq.mp (List.mem_filter.mp h).2

private theorem mem_of_independent {g : Graph n} {z : Coloring n} (h : conflicts g z=0) :
    z∈independent g := List.mem_filter.mpr ⟨Mobius.TourCount.assignments_complete z, by simp [h]⟩

theorem at_base (g : Graph n) : optimum g (base g) = (n:Rat)+g.length := by
  have lo := energy_base g ((colors n).minOn (energy g (base g)) (colors_ne n))
  have up := List.apply_minOn_le_of_mem (f := energy g (base g))
    (xs := colors n) (y := zeroColor n) (Mobius.TourCount.assignments_complete _)
  rw [energy_base g (zeroColor n),zero_free] at up
  unfold optimum
  have nonneg : (0:Rat) ≤ (conflicts g ((colors n).minOn (energy g (base g)) (colors_ne n)):Rat) := by grind
  grind

end Mobius.TropicalMWIS

namespace Mobius.TropicalMWIS
open Mobius.TropicalDAG

private theorem bounded_w (n : Nat) (w : Fin n → Rat) :
    ∃ A : Rat, 0 ≤ A ∧ (∀ z : Coloring n, gain w z ≤ A) ∧ (∀ v, w v ≤ A) := by
  let A := gain w ((colors n).maxOn (gain w) (colors_ne n))
  have hi (z : Coloring n) : gain w z ≤ A :=
    List.le_apply_maxOn_of_mem (f := gain w) (xs := colors n) (y := z)
      (Mobius.TourCount.assignments_complete z)
  refine ⟨A,by simpa only [zero_gain] using hi (zeroColor n),hi,?_⟩
  intro v
  let z : Coloring n := fun j => decide (j=v)
  have dz : gain w z = w v := by
    have pt (j : Fin n) : (if z j then w j else 0) = (if j=v then w v else 0) := by
      by_cases h : j=v <;> simp [z,h]
    unfold gain
    rw [show (fun j => _) = _ from funext pt, delta _ _ _ (List.nodup_finRange n)]
    simp
  rw [← dz]; exact hi z

private theorem nonneg_sum {α} (xs : List α) (f : α → Rat) (h : ∀ u,0≤f u) :
    0 ≤ sumQ xs f := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons u xs ih => change 0 ≤ f u+sumQ xs f; have := h u; grind only

private theorem base_positive (g : Graph n) (i : Fin n × Bool) : 1 ≤ base g i := by
  obtain ⟨v,b⟩ := i
  have hd : 0 ≤ degree g v := nonneg_sum _ _ (fun _ => by split <;> split <;> grind)
  cases b <;> simp [base,bit] <;> grind only

/-- The same rational window keeps all prices nonnegative and exposes
exactly the support function of independent sets. -/
theorem mwis_window (g : Graph n) (w : Fin n → Rat) :
    ∃ δ : Rat, 0 < δ ∧ ∀ t : Rat, 0<t → t<δ →
      (∀ i, 0 ≤ perturbed g w t i) ∧
      optimum g (perturbed g w t) = (n:Rat)+g.length-t*mwis g w := by
  obtain ⟨A,hA,hAll,hSingle⟩ := bounded_w n w
  have pos : 0 < 1+A := by grind only
  refine ⟨1/(1+A),(Rat.lt_div_iff pos).2 (by grind),?_⟩
  intro t ht he
  have ht0 : 0 ≤ t := by grind only
  have scaled := (Rat.lt_div_iff pos).1 he
  have small : t*A < 1 := by grind only
  constructor
  · intro i
    obtain ⟨v,b⟩ := i
    have hv := Rat.mul_le_mul_of_nonneg_left (hSingle v) ht0
    have hb := base_positive g (v,b)
    cases b <;> simp only [perturbed,slopeInput,labels,Bool.false_eq_true, ↓reduceIte,
      Option.map_none,Option.getD_none,Option.map_some,Option.getD_some] <;> grind only
  · let best := (independent g).maxOn (gain w) (independent_ne g)
    have hbest : best ∈ independent g := List.maxOn_mem ..
    have zbest := independent_of_mem hbest
    let zero : Coloring n := zeroColor n
    have hz : zero ∈ independent g := mem_of_independent (zero_free g)
    have zero_le : 0 ≤ mwis g w := by
      have bound : gain w zero ≤ gain w best := List.le_apply_maxOn_of_mem hz
      simpa only [zero,zero_gain,mwis,best] using bound
    have costBest : energy g (perturbed g w t) best = (n:Rat)+g.length-t*mwis g w := by
      rw [energy_perturbed,zbest]; change _ = _-t*gain w best; grind only
    have upper : optimum g (perturbed g w t) ≤ energy g (perturbed g w t) best :=
      List.apply_minOn_le_of_mem (f := energy g (perturbed g w t)) (xs := colors n)
        (Mobius.TourCount.assignments_complete best)
    have lower (z : Coloring n) : (n:Rat)+g.length-t*mwis g w ≤ energy g (perturbed g w t) z := by
      rw [energy_perturbed]
      by_cases hz : conflicts g z=0
      · have hlow : gain w z ≤ mwis g w := List.le_apply_maxOn_of_mem (mem_of_independent hz)
        have mul := Rat.mul_le_mul_of_nonneg_left hlow ht0
        rw [hz]; grind only
      · have hcN : 1 ≤ conflicts g z := by omega
        have hc : (1:Rat) ≤ (conflicts g z : Rat) := Rat.natCast_le_natCast.mpr hcN
        have bounded := Rat.mul_le_mul_of_nonneg_left (hAll z) ht0
        have nonneg := Rat.mul_nonneg ht0 zero_le
        grind only
    rw [costBest] at upper
    have other : (n:Rat)+g.length-t*mwis g w ≤ optimum g (perturbed g w t) := lower _
    exact Rat.le_antisymm upper other

/-- One max-plus DAG of no greater size computes MWIS on every rational
weight assignment. The source may be specified only on nonnegative unary
prices. Both graph data and the chosen output port are fixed. -/
theorem compile_for_mwis (g : Graph n) (p : MinDAG (Fin n × Bool) s) (out : Fin s)
    (correct : ∀ h : Prices n, (∀ i,0≤h i) → primal p h out = optimum g h) :
    (compile (base g) labels p).size ≤ s ∧
    ∀ w : Fin n → Rat, (compile (base g) labels p).read w out = mwis g w := by
  refine ⟨size_le ..,?_⟩
  intro w
  apply known_gain
  obtain ⟨δ,hδ,localEq⟩ := mwis_window g w
  refine ⟨δ,hδ,?_⟩
  intro t ht he
  obtain ⟨nonneg,eq⟩ := localEq t ht he
  change primal p (perturbed g w t) out = primal p (base g) out - t*mwis g w
  rw [correct _ nonneg,correct _ (fun i => by have := base_positive g i; grind only),at_base,eq]

end Mobius.TropicalMWIS
