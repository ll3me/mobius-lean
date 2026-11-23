import Mobius.Rigidity
import Mobius.Residual

/-!
A change on just one phase table cuts the complete graph in each XOR-symbol
fiber. The old failed edges form a perfect matching of fixed direction h.
The theorem counts ordered edges, as does the ordinary 3,840-entry score.
-/
namespace Mobius.LockedGap
open Mobius.SignObstruction (B alphabet)

def sumN (xs : List α) (f : α → Nat) := (xs.map f).sum
def one (p : Bool) : Nat := if p then 1 else 0

theorem sum_congr (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x = g x) :
    sumN xs f = sumN xs g := congrArg List.sum (List.map_congr_left h)

theorem sum_add (xs : List α) (f g : α → Nat) :
    sumN xs (fun x => f x + g x) = sumN xs f + sumN xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change (f x + g x) + sumN xs (fun x => f x + g x) = (f x + sumN xs f) + (g x + sumN xs g); rw [ih]; omega

theorem sum_const_mul (xs : List α) (f : α → Nat) (c : Nat) :
    sumN xs (fun x => f x * c) = sumN xs f * c := by
  induction xs with
  | nil => simp [sumN]
  | cons x xs ih => change f x * c + sumN xs (fun x => f x * c) = (f x + sumN xs f) * c; rw [ih,Nat.add_mul]

theorem sum_le (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    sumN xs f ≤ sumN xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.add_le_add (h _ (by simp)) (ih fun y hy => h _ (by simp [hy]))

theorem total_ones : sumN alphabet (fun _ => 1) = 16 := by decide

theorem sum_flip (f : B → Nat) (h : B) :
    sumN alphabet (fun x => f (x ^^^ h)) = sumN alphabet f := by
  have hp : (alphabet.map (fun x => x ^^^ h)).Perm alphabet := by revert h; decide
  have eq := (hp.map f).sum_nat
  simpa [sumN, List.map_map, Function.comp_def] using eq

def mass (p : B → Bool) := sumN alphabet (fun x => one (p x))
def crossed (p : B → Bool) (x v : B) := p x ^^ p v
def matched (h x v : B) := decide (v = x ^^^ h)
def blockEnergy (p : B → Bool) (h : B) :=
  sumN alphabet fun x => sumN alphabet fun v => one (matched h x v ^^ crossed p x v)
def cutCount (p : B → Bool) :=
  sumN alphabet fun x => sumN alphabet fun v => one (crossed p x v)
def matchCut (p : B → Bool) (h : B) :=
  sumN alphabet fun x => one (crossed p x (x ^^^ h))

theorem mass_complement (p : B → Bool) : mass p + mass (fun x => !(p x)) = 16 := by
  unfold mass
  rw [← sum_add]
  calc
    _ = sumN alphabet (fun _ => 1) := sum_congr _ _ _ fun x _ => by cases hh : p x <;> simp [hh, one]
    _ = 16 := total_ones

theorem cut_formula (p : B → Bool) :
    cutCount p = 2 * (mass p * mass (fun x => !(p x))) := by
  let q := fun x => !(p x)
  have layer (x : B) : (sumN alphabet fun v => one (crossed p x v)) =
      one (p x) * mass q + one (q x) * mass p := by
    cases hx : p x
    · simp [one, crossed, hx, q, mass]
    · simp [one, crossed, hx, q, mass]
  unfold cutCount
  rw [sum_congr _ _ _ (fun x _ => layer x), sum_add, sum_const_mul, sum_const_mul]
  change mass p * mass q + mass q * mass p = 2 * (mass p * mass q)
  rw [Nat.mul_comm (mass q) (mass p)]; omega

theorem matchCut_le (p : B → Bool) (h : B) : matchCut p h ≤ 2 * mass p := by
  have hb (a b : Bool) : one (a ^^ b) ≤ one a + one b := by cases a <;> cases b <;> decide
  calc
    _ ≤ sumN alphabet (fun x => one (p x) + one (p (x ^^^ h))) := sum_le _ _ _ fun x _ => hb _ _
    _ = _ := by rw [sum_add, sum_flip (fun x => one (p x)) h]; unfold mass; omega

private theorem at_one (f : B → Bool) (i : B) :
    (sumN alphabet fun v => one (decide (v = i) && f v)) = one (f i) := by
  have singleton (j : B) : alphabet.filter (fun v => decide (v = j)) = [j] := by revert j; decide
  have aux (xs : List B) : (sumN xs fun v => one (decide (v=i) && f v)) =
      sumN (xs.filter fun v => decide (v=i)) (fun v => one (f v)) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => by_cases hx : x=i <;> simp [sumN,one,hx] at * <;> exact ih
  rw [aux, singleton]; simp [sumN]

theorem energy_formula (p : B → Bool) (h : B) :
    blockEnergy p h + 2 * matchCut p h = 16 + cutCount p := by
  have bit (a b : Bool) : one (a ^^ b) + (one (a && b) + one (a && b)) = one a + one b := by
    cases a <;> cases b <;> decide
  have layer (x : B) : (sumN alphabet fun v => one (matched h x v ^^ crossed p x v)) +
      (one (crossed p x (x ^^^ h)) + one (crossed p x (x ^^^ h))) =
      1 + sumN alphabet (fun v => one (crossed p x v)) := by
    have hit := at_one (crossed p x) (x ^^^ h)
    have mat : sumN alphabet (fun v => one (matched h x v)) = 1 := by
      have z := at_one (fun _ => true) (x ^^^ h)
      simpa [matched, one] using z
    unfold matched at *
    rw [← hit, ← sum_add, ← sum_add, ← mat, ← sum_add]
    exact sum_congr _ _ _ fun v _ => bit _ _
  have full := sum_congr alphabet _ _ fun x _ => layer x
  rw [sum_add, sum_add, sum_add, total_ones] at full
  unfold blockEnergy matchCut cutCount
  omega

private theorem arithmetic (a b m e : Nat) (sz : a+b=16)
    (lm : m ≤ 2*a) (rm : m ≤ 2*b) (eq : e+2*m=16+2*(a*b)) :
    e = 16 ∨ 42 ≤ e := by
  have ar : ∀ i j : Fin 17, i.val+j.val=16 → i.val≠0 → j.val≠0 →
       42+2*min (2*i.val) (2*j.val) ≤ 16+2*(i.val*j.val) := by decide
  by_cases z : a = 0
  · subst a; simp at lm eq; omega
  by_cases z' : b = 0
  · subst b; simp at rm eq; omega
  have k := ar ⟨a,by omega⟩ ⟨b,by omega⟩ sz z z'
  simp only at k
  have mm : m ≤ min (2*a) (2*b) := Nat.le_min.mpr ⟨lm,rm⟩
  omega

theorem block_gap (p : B → Bool) (h : B) :
    blockEnergy p h = 16 ∨ 42 ≤ blockEnergy p h := by
  have comp : matchCut (fun x => !(p x)) h = matchCut p h := by
    apply sum_congr; intro x _; simp only [crossed]; cases p x <;> cases p (x ^^^ h) <;> rfl
  have right := matchCut_le (fun x => !(p x)) h
  rw [comp] at right
  exact arithmetic _ _ _ _ (mass_complement p) (matchCut_le p h) right
    (by rw [energy_formula, cut_formula])



def blockFamily (p : B → B → Bool) (h : B) :=
  sumN alphabet (fun s => blockEnergy (p s) h)

theorem family_gap (p : B → B → Bool) (h : B) :
    blockFamily p h = 256 ∨ 282 ≤ blockFamily p h := by
  have aux (xs : List B) :
      sumN xs (fun s => blockEnergy (p s) h) = 16 * xs.length ∨
      16 * xs.length + 26 ≤ sumN xs (fun s => blockEnergy (p s) h) := by
    induction xs with
    | nil => exact Or.inl rfl
    | cons x xs ih =>
      change blockEnergy (p x) h + sumN xs _ = 16*(xs.length+1) ∨
        16*(xs.length+1)+26 ≤ blockEnergy (p x) h + sumN xs _
      rcases block_gap (p x) h with he | he <;> rcases ih with he' | he' <;> omega
  exact aux alphabet

private theorem sum_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumN xs (fun x => sumN ys (f x)) = sumN ys (fun y => sumN xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    change 0 = (ys.map (fun _ => (0 : Nat))).sum
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa only [List.map_cons,List.sum_cons,Nat.zero_add] using ih
  | cons x xs ih =>
    change sumN ys (f x) + sumN xs _ = sumN ys (fun y => f x y + sumN xs (fun z => f z y))
    rw [sum_add, ih]

open Mobius.Rigidity (DirectionPattern)
open Mobius.TwoPhases (score)
open Mobius.SignObstruction (directions shifts Cell)

def entry (row col : B → B → Bool) (x y d : B) : Nat :=
  if d = 0 then 0 else one (!(score row col (x,y,d)))

private theorem expand_shifts (f : Cell → Nat) :
    sumN shifts f = sumN alphabet (fun x => sumN alphabet (fun y => f (x,y))) := by
  unfold shifts
  have aux (xs : List B) :
      sumN (xs.flatMap fun x => alphabet.map fun y => (x,y)) f =
        sumN xs (fun x => sumN alphabet fun y => f (x,y)) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [sumN, List.flatMap_cons, List.map_append, List.sum_append_nat,
        List.map_map, Function.comp_def,List.map_cons,List.sum_cons] at ih ⊢
      rw [ih]
  exact aux alphabet

private theorem full_count (row col : B → B → Bool) :
    Mobius.TwoPhases.failures row col =
    sumN alphabet fun d => sumN alphabet fun x => sumN alphabet fun y => entry row col x y d := by
  rw [Mobius.Rigidity.two_count]
  change sumN directions (fun d => sumN shifts (fun s => one (!(score row col (s.1,s.2,d))))) = _
  have split : alphabet = 0 :: directions := by decide
  have expand (f : B → Nat) : sumN alphabet f = f 0 + sumN directions f := by
    rw [split]; rfl
  rw [expand (fun d => sumN alphabet fun x => sumN alphabet fun y => entry row col x y d)]
  have zeroSum (xs : List B) : (sumN xs fun _ => 0) = 0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih => change 0 + sumN xs (fun _ => 0) = 0; omega
  have head : (sumN alphabet fun x => sumN alphabet fun y => entry row col x y 0) = 0 := by
    simp only [entry,ite_true,zeroSum]
  rw [head,Nat.zero_add]
  apply sum_congr
  intro d hd
  have nz : d ≠ 0 := by
    have valid : ∀ v ∈ directions, v ≠ 0 := by decide
    exact valid _ hd
  rw [expand_shifts]
  simp only [entry,nz, ite_false]

private theorem reindex (row col : B → B → Bool) :
    Mobius.TwoPhases.failures row col =
    sumN alphabet fun s => sumN alphabet fun x => sumN alphabet fun v =>
      entry row col x (s ^^^ x) (v ^^^ x) := by
  rw [full_count]
  calc
    _ = sumN alphabet (fun x => sumN alphabet (fun d => sumN alphabet (fun y => entry row col x y d))) :=
      sum_swap _ _ _
    _ = sumN alphabet (fun x => sumN alphabet (fun y => sumN alphabet (fun d => entry row col x y d))) :=
      sum_congr _ _ _ (fun _ _ => sum_swap _ _ _)
    _ = sumN alphabet (fun x => sumN alphabet (fun s => sumN alphabet (fun v => entry row col x (s ^^^ x) (v ^^^ x)))) := by
      apply sum_congr; intro x _
      rw [sum_flip (fun y => sumN alphabet (fun v => entry row col x y (v ^^^ x))) x]
      apply sum_congr; intro y _; exact (sum_flip (entry row col x y) x).symm
    _ = _ := sum_swap _ _ _

def rowDiff (base row : B → B → Bool) (s x : B) :=
  base x (s ^^^ x) ^^ row x (s ^^^ x)

theorem row_entry (base row col : B → B → Bool) (h : B)
    (pattern : DirectionPattern base col h) (s x v : B) :
    entry row col x (s ^^^ x) (v ^^^ x) =
      one (matched h x v ^^ crossed (rowDiff base row s) x v) := by
  have a0 : ∀ i j : B, i ^^^ (j ^^^ i) = j := by decide
  have a := a0 x v
  have b : (s ^^^ x) ^^^ (v ^^^ x) = s ^^^ v := by rw [BitVec.xor_assoc,a]
  by_cases deq : v ^^^ x = 0
  · have eq0 : ∀ i j : B, j ^^^ i = 0 → j=i := by decide
    have vx := eq0 x v deq
    subst v
    have no : x ≠ x ^^^ h := by
      intro heq; apply pattern.1
      simpa [← BitVec.xor_assoc] using (congrArg (fun z => x ^^^ z) heq).symm
    simp [entry,matched,crossed,no,one]
  · have hh : ∀ i j k : B, (j ^^^ i = k) ↔ j = i ^^^ k := by decide
    have bh := pattern.2 x (s ^^^ x) (v ^^^ x) deq
    have ee : decide (v ^^^ x ≠ h) = !(decide (v = x ^^^ h)) := by simp [hh]
    rw [ee] at bh
    simp only [entry,deq,ite_false, matched, crossed, rowDiff,score,
      Mobius.TwoPhases.corners, Mobius.SignObstruction.total, a, b] at *
    have truth : ∀ (p q r t u w k : Bool),
        (p ^^ (q ^^ (u ^^ (w ^^ false)))) = !k →
        (one (!(r ^^ (t ^^ (u ^^ (w ^^ false)))))) =
        one (k ^^ ((p ^^ r) ^^ (q ^^ t))) := by decide
    exact truth _ _ _ _ _ _ _ bh

theorem locked_row_gap (base row col : B → B → Bool)
    (opt : Mobius.TwoPhases.failures base col = 256) :
    Mobius.TwoPhases.failures row col = 256 ∨ 282 ≤ Mobius.TwoPhases.failures row col := by
  obtain ⟨h,pattern,_⟩ := Mobius.Rigidity.optimal_direction base col opt
  have eqn : Mobius.TwoPhases.failures row col = blockFamily (rowDiff base row) h := by
    rw [reindex]
    apply sum_congr; intro s _; apply sum_congr; intro x _; apply sum_congr; intro v _
    exact row_entry _ _ _ _ pattern _ _ _
  rw [eqn]; exact family_gap _ _


theorem exchange_tables (row col : B → B → Bool) :
    Mobius.TwoPhases.failures row col = Mobius.TwoPhases.failures col row := by
  rw [full_count, full_count]
  apply sum_congr; intro d _; apply sum_congr; intro x _
  rw [← sum_flip (fun y => entry col row x y d) d]
  apply sum_congr; intro y _
  by_cases zero : d = 0
  · simp [entry,zero]
  · simp only [entry,zero,ite_false, score, Mobius.TwoPhases.corners,
      Mobius.SignObstruction.total, BitVec.xor_assoc]
    simp [Bool.xor_comm, Bool.xor_left_comm]

theorem locked_col_gap (row base col : B → B → Bool)
    (opt : Mobius.TwoPhases.failures row base = 256) :
    Mobius.TwoPhases.failures row col = 256 ∨ 282 ≤ Mobius.TwoPhases.failures row col := by
  rw [exchange_tables row col]
  exact locked_row_gap base col row ((exchange_tables base row).trans opt)

open Mobius.SignObstruction (repairPhase signed)
def flipOrigin (x y : B) : Bool :=
  if x = 0 ∧ y = 0 then !(repairPhase x y) else repairPhase x y

/-- Half-unit normalization is unnecessary over integers: this is R+C-2W. -/
def witnessResidual (x y u v : B) : Int :=
  (if x ^^^ y = v ^^^ u then signed (flipOrigin x y) * signed (flipOrigin v u) +
     signed (repairPhase x u) * signed (repairPhase v y) else 0)
   - (if x=v ∧ y=u then 2 else 0)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem witness_weight : Mobius.TwoPhases.failures flipOrigin repairPhase = 282 := by
  have hp : DirectionPattern repairPhase repairPhase 8 := by
    constructor
    · decide
    · exact (by decide : ∀ x y e : B, e ≠ 0 →
        score repairPhase repairPhase (x,y,e) = decide (e ≠ 8))
  have eqn : Mobius.TwoPhases.failures flipOrigin repairPhase =
      blockFamily (rowDiff repairPhase flipOrigin) 8 := by
    rw [reindex]; apply sum_congr; intro s _; apply sum_congr; intro x _; apply sum_congr; intro v _
    exact row_entry _ _ _ _ hp _ _ _
  rw [eqn]; decide

/-- A zero row on the row cut, and two zero rows on the column cut. -/
theorem witness_zero_rows :
    (∀ u v, witnessResidual 8 8 u v = 0) ∧
    (∀ y v, witnessResidual 0 y 8 v = 0 ∧ witnessResidual 8 y 0 v = 0) := by decide

end Mobius.LockedGap
