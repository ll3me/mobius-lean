import Mobius.MatrixMerge

/-! Nonempty local masks still require quadratic deterministic communication.
Two different public sentinel positions force both masks to be nonempty
without changing the overlap of the remaining independent bits. -/
namespace Mobius.MatrixPromise
open Mobius.OverlapProtocols (Tree intersects)
open Mobius.MatrixMerge (Mask WeightedMerge UnweightedMerge)

def Live (a : BitVec n) := ∃ i : Fin n, a.getLsbD i.val=true

private def leftPad (a : BitVec n) : BitVec (n+2) := BitVec.cons false (BitVec.cons true a)
private def rightPad (a : BitVec n) : BitVec (n+2) := BitVec.cons true (BitVec.cons false a)

private theorem left_live (a : BitVec n) : Live (leftPad a) := by
  refine ⟨⟨n,by omega⟩,?_⟩
  simp [leftPad,BitVec.getLsbD_cons]

private theorem right_live (a : BitVec n) : Live (rightPad a) := by
  refine ⟨⟨n+1,by omega⟩,?_⟩
  simp [rightPad,BitVec.getLsbD_cons]

private theorem pad_intersects (a b : BitVec n) : intersects (leftPad a) (rightPad b) ↔ intersects a b := by
  constructor
  · rintro ⟨i,ha,hb⟩
    simp only [leftPad,BitVec.getLsbD_cons] at ha
    simp only [rightPad,BitVec.getLsbD_cons] at hb
    have small : i.val<n := by
      by_cases h : i.val=n
      · simp [h] at hb
      by_cases h' : i.val=n+1
      · simp [h'] at ha
      omega
    have h₀ : i.val ≠ n := by omega
    have h₁ : i.val ≠ n+1 := by omega
    exact ⟨⟨i.val,small⟩,by simpa only [ite_eq_right h₀,ite_eq_right h₁] using ha,
      by simpa only [ite_eq_right h₀,ite_eq_right h₁] using hb⟩
  · rintro ⟨i,ha,hb⟩
    have h₀ : i.val ≠ n := by omega
    have h₁ : i.val ≠ n+1 := by omega
    exact ⟨⟨i.val,by omega⟩,by simpa [leftPad,BitVec.getLsbD_cons,h₀,h₁] using ha,
      by simpa [rightPad,BitVec.getLsbD_cons,h₀,h₁] using hb⟩

private def embedTree (l r : BitVec n → BitVec m) : Tree m → Tree n
  | .halt answer => .halt (answer ∘ r)
  | .left send a b => .left (send ∘ l) (embedTree l r a) (embedTree l r b)
  | .right send a b => .right (send ∘ r) (embedTree l r a) (embedTree l r b)

private theorem embed_run (l r : BitVec n → BitVec m) (t : Tree m) (a b : BitVec n) :
    (embedTree l r t).run a b=t.run (l a) (r b) ∧ (embedTree l r t).cost a b=t.cost (l a) (r b) := by
  induction t with
  | halt _ => exact ⟨rfl,rfl⟩
  | left send x y ix iy => cases h : send (l a) <;>
      simp [embedTree,Tree.run,Tree.cost,h,ix,iy]
  | right send x y ix iy => cases h : send (r b) <;>
      simp [embedTree,Tree.run,Tree.cost,h,ix,iy]

theorem nonempty_lower {n : Nat} (hn : 2≤n) (t : Tree n)
    (correct : ∀ a b, Live a → Live b → (t.run a b=true ↔ intersects a b)) :
    ∃ a b, Live a ∧ Live b ∧ n-2 ≤ t.cost a b := by
  obtain ⟨d,eq⟩ := Nat.exists_eq_add_of_le hn
  have en : n=d+2 := by omega
  clear eq
  subst n
  let s := embedTree leftPad rightPad t
  have ck (a b : BitVec d) : s.run a b=true ↔ intersects a b := by
    rw [show s.run a b=t.run (leftPad a) (rightPad b) from (embed_run _ _ t a b).1]
    exact (correct _ _ (left_live _) (right_live _)).trans (pad_intersects a b)
  obtain ⟨a,b,long⟩ := OverlapProtocols.interactive_cost_lower s ck
  refine ⟨leftPad a,rightPad b,left_live _,right_live _,?_⟩
  simpa only [s,(embed_run _ _ t a b).2,Nat.add_sub_cancel] using long

theorem weighted_live_lower (hk : 2≤k) (t : Tree (k*k))
    (correct : ∀ a b : Mask k, Live a → Live b → (t.run a b=true ↔ WeightedMerge a b)) :
    ∃ a b : Mask k, Live a ∧ Live b ∧ k*k-2 ≤ t.cost a b := by
  have h := Nat.mul_le_mul hk hk
  apply nonempty_lower (by omega)
  intro a b ha hb
  exact ((correct a b ha hb).trans (MatrixMerge.weighted_merge_iff a b)).trans (MatrixMerge.merge_iff a b)

theorem unweighted_live_lower (gap : AxisPortCost.Gap282) (hk : 2≤k) (t : Tree (k*k))
    (correct : ∀ a b : Mask k, Live a → Live b → (t.run a b=true ↔ UnweightedMerge a b)) :
    ∃ a b : Mask k, Live a ∧ Live b ∧ k*k-2 ≤ t.cost a b := by
  have h := Nat.mul_le_mul hk hk
  apply nonempty_lower (by omega)
  intro a b ha hb
  exact ((correct a b ha hb).trans (MatrixMerge.unweighted_merge_iff gap a b)).trans (MatrixMerge.merge_iff a b)

def allMask (n : Nat) : BitVec n := ~~~0

/-- Each side independently extends on the actual compiled weighted atlas:
pair that side with an all-allowing opposite side. -/
theorem individually_extend (a b : Mask k) (ha : Live a) (hb : Live b) :
    WeightedMerge a (allMask (k*k)) ∧ WeightedMerge (allMask (k*k)) b := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hb
  have ones (w : Fin (k*k)) : (allMask (k*k)).getLsbD w.val=true := by
    simp [allMask,w.isLt]
  exact ⟨(MatrixMerge.weighted_merge_iff ..).mpr ((MatrixMerge.merge_iff ..).mpr ⟨i,hi,ones i⟩),
    (MatrixMerge.weighted_merge_iff ..).mpr ((MatrixMerge.merge_iff ..).mpr ⟨j,ones j,hj⟩)⟩


theorem unweighted_individually_extend (gap : AxisPortCost.Gap282) (a b : Mask k) (ha : Live a) (hb : Live b) :
    UnweightedMerge a (allMask (k*k)) ∧ UnweightedMerge (allMask (k*k)) b := by
  obtain ⟨left,right⟩ := individually_extend a b ha hb
  exact ⟨(MatrixMerge.unweighted_merge_iff gap ..).mpr ((MatrixMerge.weighted_merge_iff ..).mp left),
    (MatrixMerge.unweighted_merge_iff gap ..).mpr ((MatrixMerge.weighted_merge_iff ..).mp right)⟩

theorem hard_extendible_pair (hk : 2≤k) (t : Tree (k*k))
    (correct : ∀ a b : Mask k, Live a → Live b → (t.run a b=true ↔ WeightedMerge a b)) :
    ∃ a b : Mask k, Live a ∧ Live b ∧ WeightedMerge a (allMask (k*k)) ∧
      WeightedMerge (allMask (k*k)) b ∧ k*k-2 ≤ t.cost a b := by
  obtain ⟨a,b,ha,hb,long⟩ := weighted_live_lower hk t correct
  obtain ⟨left,right⟩ := individually_extend a b ha hb
  exact ⟨a,b,ha,hb,left,right,long⟩


/-- The first d transmitted bits; runs that have already halted are padded
with zeros. The code has fixed length regardless of local computation. -/
private def record (d : Nat) (t : Tree n) (x y : BitVec n) : BitVec d :=
  match d,t with
  | 0,_ => 0
  | _+1,.halt _ => 0
  | k+1,.left w a b => BitVec.cons (w x) (record k (if w x then b else a) x y)
  | k+1,.right w a b => BitVec.cons (w y) (record k (if w y then b else a) x y)

private theorem record_mix (d : Nat) (t : Tree n) (x y u v : BitVec n)
    (bound : t.cost u v ≤ d) (same : record d t x y = record d t u v) :
    t.run x v = t.run u v := by
  induction d generalizing t with
  | zero =>
    cases t with
    | halt => rfl
    | left | right => exact False.elim (Nat.not_succ_le_zero _ bound)
  | succ d ih =>
    have hd := congrArg BitVec.msb same
    have tl := congrArg (BitVec.setWidth d) same
    cases t with
    | halt => rfl
    | left w a b =>
      cases ex : w x <;> cases eu : w u <;> simp [record,ex,eu] at hd tl <;>
        simp [Tree.run,ex,eu] <;> simp [Tree.cost,eu] at bound <;>
        first | exact ih a (by omega) tl | exact ih b (by omega) tl
    | right w a b =>
      cases ey : w y <;> cases ev : w v <;> simp [record,ey,ev] at hd tl <;>
        simp [Tree.run,ev] <;> simp [Tree.cost,ev] at bound <;>
        first | exact ih a (by omega) tl | exact ih b (by omega) tl

private theorem live_nonzero {x : BitVec n} (nz : x≠0) : Live x := by
  apply Classical.byContradiction; intro none
  apply nz
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  cases hx : x.getLsbD i with
  | false => simp
  | true => exact False.elim (none ⟨⟨i,hi⟩,hx⟩)

private def interior (i : Fin (2^n-2)) : BitVec n := BitVec.ofFin ⟨i.val+1,by omega⟩

private theorem interior_live (i : Fin (2^n-2)) :
    Live (interior i) ∧ Live (~~~(interior i)) := by
  have val : (interior i).toNat=i.val+1 := rfl
  constructor <;> apply live_nonzero <;> intro e <;> have bad := congrArg BitVec.toNat e
  · change (interior i).toNat=0 at bad; omega
  · rw [BitVec.toNat_not,val] at bad
    change 2^n - 1 - (i.val+1) = 0 at bad
    omega

private theorem self_disjoint (x : BitVec n) : ¬intersects x (~~~x) := by
  rintro ⟨i,h,k⟩
  simp only [BitVec.getLsbD_not,decide_eq_true i.isLt,Bool.true_and,h] at k
  contradiction

private theorem cross_unique (x y : BitVec n)
    (xy : ¬intersects x (~~~y)) (yx : ¬intersects y (~~~x)) : x=y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i
  · rfl
  · exact False.elim (yx ⟨⟨i,hi⟩,hy,by simp only [BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and,hx]; rfl⟩)
  · exact False.elim (xy ⟨⟨i,hi⟩,hx,by simp only [BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and,hy]; rfl⟩)
  · rfl

/-- For n≥3 the nontrivial complement diagonal has 2^n−2>2^(n−1)
elements. Some actual rejecting run there costs the full n bits. -/
theorem exact_nonempty_lower {n : Nat} (size : 3≤n) (t : Tree n)
    (correct : ∀ a b, Live a → Live b → (t.run a b=true ↔ intersects a b)) :
    ∃ a, Live a ∧ Live (~~~a) ∧ n≤t.cost a (~~~a) := by
  cases n with
  | zero => omega
  | succ d =>
    apply Classical.byContradiction
    intro no
    let x := @interior (d+1)
    have live (i) := @interior_live (d+1) i
    have cheap (i) : t.cost (x i) (~~~(x i)) ≤ d := by
      have h : ¬d+1 ≤ t.cost (x i) (~~~(x i)) := fun h => no ⟨_,(live i).1,(live i).2,h⟩
      omega
    let code i := record d t (x i) (~~~(x i))
    have mix {i j} (eq : code i=code j) : ¬intersects (x i) (~~~(x j)) := by
      intro yes
      have accept := (correct _ _ (live i).1 (live j).2).mpr yes
      rw [record_mix _ _ (x i) (~~~(x i)) (x j) (~~~(x j)) (cheap j) eq] at accept
      exact self_disjoint _ ((correct _ _ (live j).1 (live j).2).mp accept)
    have count := Bounded.fin_size_le (fun i => (code i).toFin) (fun i j h => by
      have recEq : code i=code j := congrArg BitVec.ofFin h
      have equal := cross_unique _ _ (mix recEq) (mix recEq.symm)
      have val := congrArg BitVec.toNat equal
      change i.val+1=j.val+1 at val
      exact Fin.ext (by omega))
    change 2^(d+1)-2 ≤ 2^d at count
    have four : 2^2 ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at count
    omega

/-- Tight promised communication. Both halves independently extend,
but their union in this expensive transcript is actually infeasible. -/
theorem exact_weighted_live (hk : 2≤k) (t : Tree (k*k))
    (correct : ∀ a b : Mask k, Live a → Live b → (t.run a b=true ↔ WeightedMerge a b)) :
    ∃ a : Mask k, Live a ∧ Live (~~~a) ∧ WeightedMerge a (allMask (k*k)) ∧
      WeightedMerge (allMask (k*k)) (~~~a) ∧ ¬WeightedMerge a (~~~a) ∧ k*k≤t.cost a (~~~a) := by
  have sq := Nat.mul_le_mul hk hk
  obtain ⟨a,ha,hb,time⟩ := exact_nonempty_lower (n:=k*k) (by omega) t
    (fun x y hx hy => ((correct x y hx hy).trans (MatrixMerge.weighted_merge_iff x y)).trans (MatrixMerge.merge_iff x y))
  obtain ⟨l,r⟩ := individually_extend a (~~~a) ha hb
  exact ⟨a,ha,hb,l,r,fun h => self_disjoint a ((MatrixMerge.merge_iff ..).mp ((MatrixMerge.weighted_merge_iff ..).mp h)),time⟩


theorem exact_unweighted_live (gap : AxisPortCost.Gap282) (hk : 2≤k) (t : Tree (k*k))
    (correct : ∀ a b : Mask k, Live a → Live b → (t.run a b=true ↔ UnweightedMerge a b)) :
    ∃ a : Mask k, Live a ∧ Live (~~~a) ∧ UnweightedMerge a (allMask (k*k)) ∧
      UnweightedMerge (allMask (k*k)) (~~~a) ∧ ¬UnweightedMerge a (~~~a) ∧ k*k≤t.cost a (~~~a) := by
  have same (a b : Mask k) : UnweightedMerge a b ↔ WeightedMerge a b :=
    (MatrixMerge.unweighted_merge_iff gap ..).trans (MatrixMerge.weighted_merge_iff ..).symm
  obtain ⟨a,ha,hb,l,r,no,time⟩ :=
    exact_weighted_live hk t (fun x y hx hy => (correct x y hx hy).trans (same x y))
  exact ⟨a,ha,hb,(same ..).mpr l,(same ..).mpr r,fun h => no ((same ..).mp h),time⟩

end Mobius.MatrixPromise
