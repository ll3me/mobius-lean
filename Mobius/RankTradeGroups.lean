import Mobius.RankTrade

/-! Exact coefficients and integer factorizations for the signed three-piece crossing. -/
namespace Mobius.RankTrade

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 16384

def sumI {α} (xs : List α) (f : α → Int) := (xs.map f).sum

private theorem sumI_flat {α β} (xs : List α) (g : α → List β) (f : β → Int) :
    sumI (xs.flatMap g) f = sumI xs (fun x => sumI (g x) f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [sumI, List.sum_append]

private theorem sumI_map {α β} (xs : List α) (g : α → β) (f : β → Int) :
    sumI (xs.map g) f = sumI xs (fun x => f (g x)) := by
  simp [sumI, List.map_map, Function.comp_def]

private theorem sumI_mul {α} (xs : List α) (f : α → Int) (v : Int) :
    sumI xs (fun x => f x * v) = sumI xs f * v := by
  induction xs with
  | nil => simp [sumI]
  | cons x xs ih => simp_all [sumI, Int.add_mul]

private theorem sumI_lmul {α} (xs : List α) (f : α → Int) (v : Int) :
    sumI xs (fun x => v * f x) = v * sumI xs f := by
  simpa only [Int.mul_comm] using sumI_mul xs f v

private theorem sumI_add {α} (xs : List α) (f g : α → Int) :
    sumI xs (fun x => f x + g x) = sumI xs f + sumI xs g := by
  induction xs with
  | nil => simp [sumI]
  | cons x xs ih => simp_all [sumI]; omega

private theorem sumI_zero {α} (xs : List α) : sumI xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all [sumI]

private theorem exchange {α β} (xs : List α) (ys : List β) (f : α → β → Int) :
    sumI xs (fun x => sumI ys (f x)) = sumI ys (fun y => sumI xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [sumI, show (List.map (fun _ : β => (0:Int)) ys).sum = 0 from sumI_zero ys]
  | cons x xs ih =>
    change sumI ys (f x) + sumI xs (fun a => sumI ys (f a)) =
      sumI ys (fun y => f x y + sumI xs (fun a => f a y))
    rw [ih, sumI_add]

private theorem sumI_filter {α} (xs : List α) (b : α → Bool) (f : α → Int) :
    sumI (xs.filter b) f = sumI xs (fun x => if b x then f x else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : b x <;> simp_all [sumI]

private theorem sumI_congr {α} (xs : List α) (f g : α → Int) (h : ∀ x ∈ xs, f x = g x) :
    sumI xs f = sumI xs g := by
  unfold sumI
  rw [List.map_congr_left h]

private theorem sumI_all_zero {α} (xs : List α) (f : α → Int) (h : ∀ x ∈ xs, f x = 0) :
    sumI xs f = 0 := (sumI_congr xs f (fun _ => 0) h).trans (sumI_zero xs)

def polys : Nat → List (List Piece)
  | 0 => [[]]
  | t+1 => [.q,.e,.p].flatMap fun a => (polys t).map (a :: ·)

def degree : List Piece → Nat
  | [] => 0
  | p::ps => deg p + degree ps

def patterns (t k : Nat) := (polys t).filter fun ps => degree ps == k

private theorem polys_mem_length {ps : List Piece} {t : Nat} (h : ps ∈ polys t) :
    ps.length = t := by
  induction t generalizing ps with
  | zero => simp_all [polys]
  | succ t ih =>
    obtain ⟨p,_,hs⟩ := List.mem_flatMap.mp h
    obtain ⟨ps,hm,rfl⟩ := List.mem_map.mp hs
    simp [ih hm]

private theorem pattern_mem {ps : List Piece} {t k : Nat} (h : ps ∈ patterns t k) :
    ps.length = t ∧ degree ps = k :=
  ⟨polys_mem_length (List.mem_filter.mp h).1, beq_iff_eq.mp (List.mem_filter.mp h).2⟩

def prod2 {α β} (f : α → β → Int) : List α → List β → Int
  | [], [] => 1
  | a::as, b::bs => f a b * prod2 f as bs
  | _, _ => 0

def amplitudes (col : Bool) (ls : List Pair) (factor : List Pair) :=
    prod2 (basis col) ls factor

def coeff (col : Bool) (ps : List Piece) (ls : List Pair) :=
    prod2 (fun p l => eigen col l p) ps ls

/-- The integer coefficients of the physical crossing, evaluated without an eigenspace choice. -/
def grouped (ws : List Tile) (k : Nat) :=
    sumI (patterns ws.length k) (fun ps => prod2 entry ps ws)

/-- Fourier coefficient for one basis label sequence. -/
def spectral (col : Bool) (t k : Nat) (ls : List Pair) :=
    sumI (patterns t k) (fun ps => coeff col ps ls)

private theorem local_flat (col : Bool) (p : Piece) (w : Tile) :
    sumI labels (fun a => basis col a (w.left col) * eigen col a p * basis col a (w.right col)) =
      8 * entry p w := by
  rw [labels, sumI_flat]
  simp only [sumI_map]
  exact block_factorization col p w

private theorem mask_value (col : Bool) (ws : List Tile) (ps : List Piece)
    (len : ps.length = ws.length) :
    sumI (words ws.length) (fun ls =>
      amplitudes col ls (ws.map (·.left col)) * coeff col ps ls *
      amplitudes col ls (ws.map (·.right col))) =
      8^ws.length * prod2 entry ps ws := by
  induction ws generalizing ps with
  | nil =>
    have := List.length_eq_zero_iff.mp len
    subst ps
    simp [words, sumI, amplitudes, coeff, prod2]
  | cons w ws ih =>
    cases ps with
    | nil => simp at len
    | cons p ps =>
      have h : ps.length = ws.length := Nat.succ.inj len
      simp only [List.length_cons, words, sumI_flat, sumI_map, List.map_cons,
        amplitudes, coeff, prod2]
      let weight := fun ls => amplitudes col ls (ws.map (·.left col)) * coeff col ps ls *
        amplitudes col ls (ws.map (·.right col))
      let scalar := fun a => basis col a (w.left col) * eigen col a p * basis col a (w.right col)
      have eq_sums (a : Pair) :
          sumI (words ws.length) (fun ls =>
            (basis col a (w.left col) * amplitudes col ls (ws.map (·.left col))) *
            (eigen col a p * coeff col ps ls) *
            (basis col a (w.right col) * amplitudes col ls (ws.map (·.right col)))) =
          scalar a * (8^ws.length * prod2 entry ps ws) := by
        have rearr (ls : List Pair) :
            (basis col a (w.left col) * amplitudes col ls (ws.map (·.left col))) *
            (eigen col a p * coeff col ps ls) *
            (basis col a (w.right col) * amplitudes col ls (ws.map (·.right col))) =
              scalar a * weight ls := by unfold scalar weight; ac_rfl
        rw [show (fun ls => _) = _ from funext rearr, sumI_lmul]
        exact congrArg (scalar a * ·) (ih ps h)
      calc
        _ = sumI labels (fun a => scalar a * (8^ws.length * prod2 entry ps ws)) :=
          sumI_congr _ _ _ (fun a _ => eq_sums a)
        _ = _ := by
          rw [sumI_mul, show sumI labels scalar = _ from local_flat col p w, Int.pow_succ]
          ac_rfl

private theorem sparse_mask (col : Bool) (ps : List Piece) (ls : List Pair)
    (h : coeff col ps ls ≠ 0) :
    (if col then 2*ps.length-degree ps else degree ps) ≤ capacity ls := by
  induction ps generalizing ls with
  | nil => cases ls <;> simp [degree, capacity]
  | cons p ps ih =>
    cases ls with
    | nil => simp [coeff, prod2] at h
    | cons l ls =>
      have hn : eigen col l p ≠ 0 ∧ coeff col ps ls ≠ 0 := by
        simpa [coeff, prod2, Int.mul_ne_zero_iff] using h
      have one := spectral_support col l p hn.1
      have tail := ih ls hn.2
      have hd : deg p ≤ 2 := by cases p <;> decide
      cases col
      · exact Nat.add_le_add one tail
      · change 2 - deg p ≤ cap l at one
        change 2 * ps.length - degree ps ≤ capacity ls at tail
        change 2*(ps.length+1) - (deg p + degree ps) ≤ cap l + capacity ls
        omega

private theorem sparse_spectral (col : Bool) (t k : Nat) (ls : List Pair)
    (h : ¬ (if col then 2*t-k else k) ≤ capacity ls) :
    spectral col t k ls = 0 := by
  apply sumI_all_zero
  intro ps hp
  have hd := pattern_mem hp
  by_cases hc : coeff col ps ls = 0
  · exact hc
  · have bad := sparse_mask col ps ls hc
    rw [hd.1, hd.2] at bad
    exact False.elim (h bad)

/-- The retained basis labels give separated integer factors on each cut. -/
def admissible (col : Bool) (t k : Nat) :=
    (words t).filter fun ls => decide ((if col then 2*t-k else k) ≤ capacity ls)

theorem integer_factorization (col : Bool) (ws : List Tile) (k : Nat) :
    sumI (admissible col ws.length k) (fun ls =>
      amplitudes col ls (ws.map (·.left col)) * spectral col ws.length k ls *
      amplitudes col ls (ws.map (·.right col))) = 8^ws.length * grouped ws k := by
  let left := fun ls => amplitudes col ls (ws.map (·.left col))
  let right := fun ls => amplitudes col ls (ws.map (·.right col))
  let t := ws.length
  let pats := patterns t k
  change sumI (admissible col t k) (fun ls => left ls * spectral col t k ls * right ls) = _
  rw [admissible, sumI_filter]
  have clean (ls : List Pair) :
      (if decide ((if col then 2*t-k else k) ≤ capacity ls) then
        left ls * spectral col t k ls * right ls else 0) =
        sumI pats (fun ps => left ls * coeff col ps ls * right ls) := by
    rw [sumI_mul, sumI_lmul]
    by_cases h : (if col then 2*t-k else k) ≤ capacity ls
    · simp [h, spectral, pats]
    · have hz := sparse_spectral col t k ls h
      change (if decide _ then _ else 0) = left ls * spectral col t k ls * right ls
      simp [h,hz]
  rw [show (fun ls => _) = _ from funext clean, exchange]
  have eq (ps : List Piece) (hp : ps ∈ pats) :
      sumI (words t) (fun ls => left ls * coeff col ps ls * right ls) =
        8^t * prod2 entry ps ws := mask_value col ws ps (pattern_mem hp).1
  rw [sumI_congr pats _ _ eq, sumI_lmul]
  rfl

theorem integer_rank_product (ws : List Tile) (k : Nat) (h : k ≤ 2*ws.length) :
    (admissible false ws.length k).length * (admissible true ws.length k).length ≤
      1521^ws.length := rank_product_budget ws.length k h

private theorem degree_bound (ps : List Piece) : degree ps ≤ 2*ps.length := by
  induction ps with
  | nil => simp [degree]
  | cons p ps ih =>
    have hd : deg p ≤ 2 := by cases p <;> decide
    simp only [degree, List.length_cons]; omega

private theorem delta (xs : List Nat) (k : Nat) (v : Int) (unique : xs.Nodup) :
    sumI xs (fun i => if k = i then v else 0) = if k ∈ xs then v else 0 := by
  induction xs with
  | nil => simp [sumI]
  | cons j js ih =>
    obtain ⟨fresh,ht⟩ := List.nodup_cons.mp unique
    change (if k = j then v else 0) + sumI js (fun i => if k = i then v else 0) = _
    rw [ih ht]
    by_cases h : k = j <;> simp_all

def crosses (ws : List Tile) := (ws.map crossing).prod

private theorem all_patterns (ws : List Tile) :
    sumI (polys ws.length) (fun ps => prod2 entry ps ws) = crosses ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.length_cons, polys, sumI_flat, sumI_map, prod2, sumI_lmul, ih]
    change Q w * crosses ws + (E w * crosses ws + (P w * crosses ws + 0)) =
        crossing w * crosses ws
    rw [Int.add_zero, ← Int.add_mul, ← Int.add_mul, ← Int.add_assoc, crossing_sum]

/-- Summing the 2t+1 coefficient tensors recovers the actual crossing product. -/
theorem recover_crossing (ws : List Tile) :
    sumI (List.range (2*ws.length+1)) (grouped ws) = crosses ws := by
  unfold grouped patterns
  simp only [sumI_filter]
  rw [exchange, ← all_patterns ws]
  apply sumI_congr
  intro ps hp
  have member : degree ps ∈ List.range (2*ws.length+1) := by
    have h := degree_bound ps
    have hl := polys_mem_length hp
    simp only [List.mem_range]; omega
  simpa only [beq_iff_eq, member, ite_true] using
    delta (List.range (2*ws.length+1)) (degree ps) (prod2 entry ps ws) List.nodup_range

end Mobius.RankTrade
