import Mobius.CrossingSplice
import Mobius.CrossingCharge

/-! A single diagonal 3-CNF word carries the lower bound at every halting
fuel, not just at a caller-supplied timeout. Costs count original transitions. -/
namespace Mobius.CrossingMachine
open Complexity
open Mobius.CrossingLayout (word word_sat width firstCut leftPart rightPart joined cut_position)
open Mobius.CrossingCharge (sumOn)
open Mobius.CrossingRun (Event inputTrace sequence)

def sites (m : Nat) : List Int := (List.range (width m)).map fun j => Int.ofNat (firstCut m+j)

theorem sites_nodup (m : Nat) : (sites m).Nodup :=
  List.Pairwise.map _ (fun a b ne (eq : Int.ofNat (firstCut m+a)=Int.ofNat (firstCut m+b)) =>
    ne (Nat.add_left_cancel (Int.ofNat.inj eq))) List.nodup_range

@[simp] theorem sites_length (m : Nat) : (sites m).length = width m := by simp [sites]

private theorem single_indicator (cs : List Int) (p : Int) :
    sumOn cs (fun c => if p=c then 1 else 0) = cs.count p := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : p=c
    · subst c; simp [ih,Nat.add_comm]
    · simp [h,Ne.symm h,ih]

/-- A genuine moving transition crosses just one integer boundary. -/
theorem charge_events {M : Machine} (cs : List Int) (hd : cs.Nodup) (es : List (Event M)) :
    sumOn cs (fun c => (sequence c es).length) ≤ es.length := by
  induction es with
  | nil => simp [sequence,CrossingCharge.sum_const]
  | cons e es ih =>
    obtain ⟨pos,q⟩ := e
    have piece (c : Int) : (sequence c ((pos,q)::es)).length =
        (if pos=c then 1 else 0) + (sequence c es).length := by
      by_cases h : pos=c <;> simp [sequence,h,Nat.add_comm]
    simp only [piece,CrossingCharge.sum_add,single_indicator,List.length_cons]
    have atMost := List.nodup_iff_count.mp hd pos
    omega

theorem records_injective {M : Machine} {m : Nat}
    (sound : ∀ x y : BitVec m, Accepts M (word x y) → x=y)
    (fuels : Fin (2^m) → Nat) (events : Fin (2^m) → List (Event M))
    (run : ∀ i, inputTrace M (fuels i) (word (BitVec.ofFin i) (BitVec.ofFin i)) = some (true,events i))
    (c : Int) (hc : c∈sites m) (i j : Fin (2^m))
    (same : sequence c (events i) = sequence c (events j)) : i=j := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
  have range : k<width m := List.mem_range.mp hk
  let x := BitVec.ofFin i
  let y := BitVec.ofFin j
  have lx := cut_position x (Nat.le_of_lt range)
  have ly := cut_position y (Nat.le_of_lt range)
  have hpos : 0<(leftPart x k).length := by rw [lx]; unfold firstCut; omega
  have runX : inputTrace M (fuels i) (leftPart x k ++ rightPart x k) = some (true,events i) := by
    rw [joined]; exact run i
  have runY : inputTrace M (fuels j) (leftPart y k ++ rightPart y k) = some (true,events j) := by
    rw [joined]; exact run j
  have accepted := CrossingRun.splice_accept (lx.trans ly.symm) hpos runX runY (by rw [lx]; exact same)
  rw [joined] at accepted
  exact congrArg BitVec.toFin (sound x y accepted)

private theorem least_time {p : Nat → Prop} (h : ∃ t, p t) :
    ∃ t, p t ∧ ∀ s, p s → t≤s := by
  obtain ⟨t,ht⟩ := h
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases smaller : ∃ s, s<t ∧ p s
    · obtain ⟨s,hs,hp⟩ := smaller
      exact ih s hs hp
    · refine ⟨t,ht,fun s hp => ?_⟩
      have h : ¬ s<t := fun sl => smaller ⟨s,sl,hp⟩
      omega

/-- The operand is the concrete bit-level formula family. The machine need
be correct only on this promise. No clock is assumed. -/
theorem finite_lower {M : Machine} {m b : Nat}
    (correct : ∀ x y : BitVec m, Accepts M (word x y) ↔ SAT.ThreeSAT (word x y))
    (hm : 0<m) (hb : 0<b) (hs : M.states+1 ≤ 2^b) :
    ∃ x : BitVec m, Accepts M (word x x) ∧ ∀ fuel ans out,
      runInput M fuel (word x x) = some (ans,out) →
      width m*((m-1)/b) ≤ 2*fuel := by
  let w (i : Fin (2^m)) := word (BitVec.ofFin i) (BitVec.ofFin i)
  have accepts (i : Fin (2^m)) : Accepts M (w i) :=
    (correct _ _).mpr ((word_sat _ _).mpr rfl)
  have least (i : Fin (2^m)) :
      ∃ t, (∃ out, runInput M t (w i) = some (true,out)) ∧
        ∀ s, (∃ out, runInput M s (w i) = some (true,out)) → t≤s :=
    least_time (accepts i)
  let fuel (i : Fin (2^m)) := Classical.choose (least i)
  have hmin (i : Fin (2^m)) := Classical.choose_spec (least i)
  have htrace (i : Fin (2^m)) : ∃ es, inputTrace M (fuel i) (w i) = some (true,es) ∧ es.length≤fuel i := by
    obtain ⟨out,r⟩ := (hmin i).1
    exact CrossingRun.trace_of_runInput r
  let es (i : Fin (2^m)) := Classical.choose (htrace i)
  have ready (i : Fin (2^m)) : inputTrace M (fuel i) (w i) = some (true,es i) ∧ (es i).length≤fuel i :=
    Classical.choose_spec (htrace i)
  have sound (x y : BitVec m) (ha : Accepts M (word x y)) : x=y := (word_sat x y).mp ((correct x y).mp ha)
  have cap : b*((m-1)/b) ≤ m-1 := Nat.mul_div_le _ _
  have hard := CrossingCharge.same_input hm hs hb cap (sites m) (fun i c => sequence c (es i)) fuel
    (records_injective sound fuel es (fun i => (ready i).1))
    (fun i => Nat.le_trans (charge_events _ (sites_nodup m) _) (ready i).2)
  obtain ⟨i,time⟩ := hard
  rw [sites_length] at time
  refine ⟨BitVec.ofFin i,accepts i,fun t ans out run => ?_⟩
  obtain ⟨prior,r⟩ := (hmin i).1
  have ha : true=ans := congrArg Prod.fst (run_deterministic M (initial M (w i)) r run)
  subst ans
  exact Nat.le_trans time (Nat.mul_le_mul_left 2 ((hmin i).2 t ⟨out,run⟩))


/-- For every large parameter, one satisfiable ordinary 3-CNF of precisely
the stated length takes Ω_M(N^{3/2}) transitions on the given machine.
The universal quantifier over halting fuels includes the earliest possible
halt, and the explicit acceptance witness ensures it exists. -/
theorem ordinary_threeSAT_time (M : Machine)
    (correct : ∀ w, Accepts M w ↔ SAT.ThreeSAT w)
    (m : Nat) (large : M.states+1 < m) :
    ∃ w : Word, w.length = CrossingLayout.inputLength m ∧ SAT.ThreeSAT w ∧ Accepts M w ∧
      ∀ fuel ans out, runInput M fuel w = some (ans,out) →
        w.length * Nat.sqrt w.length ≤ 884*(M.states+1)*fuel := by
  let b := M.states+1
  have hb : 0<b := Nat.zero_lt_succ _
  have hs : M.states+1 ≤ 2^b := Nat.le_of_lt Nat.lt_two_pow_self
  obtain ⟨x,accepts,hard⟩ := finite_lower (M:=M) (b:=b)
    (fun x y : BitVec m => correct (word x y)) (by omega) hb hs
  refine ⟨word x x,CrossingLayout.word_length x x,(word_sat x x).mpr rfl,accepts,?_⟩
  intro fuel ans out run
  rw [CrossingLayout.word_length]
  exact CrossingCharge.scale hb large (hard fuel ans out run)

end Mobius.CrossingMachine
