import Mobius.RankTradeGroups

/-! Leading spectral coefficients survive in the central group. -/
namespace Mobius.RankTrade

set_option linter.constructorNameAsVariable false

def top (l : Pair) : Piece := if cap l = 2 then .p else if cap l = 1 then .e else .q

def topAt (col : Bool) (l : Pair) : Piece := if col then flip (top l) else top l

def edeg (col : Bool) (p : Piece) := if col then deg (flip p) else deg p

def grade (col : Bool) (ps : List Piece) := (ps.map (edeg col)).sum

private theorem support_one (col : Bool) (l : Pair) (p : Piece) (h : eigen col l p ≠ 0) :
    edeg col p ≤ cap l ∧ (edeg col p = cap l → p = topAt col l) := by
  obtain ⟨a,b⟩ := l
  cases p <;> (revert col a b h; decide)

private theorem top_one (col : Bool) (l : Pair) :
    edeg col (topAt col l) = cap l ∧ eigen col l (topAt col l) ≠ 0 := by
  obtain ⟨a,b⟩ := l; revert col a b; decide

private theorem sparse (col : Bool) (ps : List Piece) (ls : List Pair) (h : coeff col ps ls ≠ 0) :
    grade col ps ≤ capacity ls ∧ (grade col ps = capacity ls → ps = ls.map (topAt col)) := by
  induction ps generalizing ls with
  | nil =>
    cases ls with
    | nil => simp [grade,capacity]
    | cons _ _ => simp [coeff,prod2] at h
  | cons p ps ih =>
    cases ls with
    | nil => simp [coeff,prod2] at h
    | cons l ls =>
      have hn : eigen col l p ≠ 0 ∧ coeff col ps ls ≠ 0 := by
        simpa [coeff,prod2, Int.mul_ne_zero_iff] using h
      obtain ⟨hc,hu⟩ := support_one col l p hn.1
      obtain ⟨tc,tu⟩ := ih ls hn.2
      change (edeg col p + grade col ps ≤ cap l + capacity ls) ∧ _
      refine ⟨Nat.add_le_add hc tc, ?_⟩
      intro he
      change edeg col p + grade col ps = cap l + capacity ls at he
      have e1 := hu (by omega)
      have e2 := tu (by omega)
      simp [e1,e2]

private theorem top_val (col : Bool) (ls : List Pair) :
    coeff col (ls.map (topAt col)) ls ≠ 0 := by
  induction ls with
  | nil => change (1:Int) ≠ 0; decide
  | cons l ls ih =>
    change eigen col l (topAt col l) * coeff col (ls.map (topAt col)) ls ≠ 0
    exact Int.mul_ne_zero (top_one col l).2 ih

private theorem deg_bound' (ps : List Piece) : degree ps ≤ 2*ps.length := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hd : deg p ≤ 2 := by cases p <;> decide
    simp [degree]; omega

private theorem grade_rev (col : Bool) (ps : List Piece) :
    grade col ps = if col then 2*ps.length-degree ps else degree ps := by
  induction ps with
  | nil => cases col <;> rfl
  | cons p ps ih =>
    have db := deg_bound' ps
    cases col <;> cases p <;> simp [grade,edeg,degree,deg,flip] at * <;> omega

private theorem top_grade (col : Bool) (ls : List Pair) :
    grade col (ls.map (topAt col)) = capacity ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    change edeg col (topAt col l) + grade col (ls.map (topAt col)) = _
    rw [(top_one col l).1,ih]
    rfl

private theorem sumI_list_congr {α} (xs : List α) {f g : α → Int} (h : ∀ x ∈ xs, f x = g x) :
    sumI xs f = sumI xs g := by unfold sumI; rw [List.map_congr_left h]

private theorem sumI_nothing {α} (xs : List α) : sumI xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all [sumI]

private theorem pattern_delta (ps : List Piece) (v : Int) :
    sumI (polys ps.length) (fun x => if x = ps then v else 0) = v := by
  induction ps with
  | nil => simp [polys,sumI]
  | cons p ps ih =>
    cases p <;>
      simp [polys,sumI, List.map_map, Function.comp_def,
        List.sum_append] at * <;>
      simp_all [show (List.map (fun _ : List Piece => (0:Int)) (polys ps.length)).sum = 0 from
        sumI_nothing (polys ps.length)]

private theorem length_mem' {ps : List Piece} {n : Nat} (h : ps ∈ polys n) : ps.length = n := by
  induction n generalizing ps with
  | zero => simp_all [polys]
  | succ n ih =>
    obtain ⟨p,_,h'⟩ := List.mem_flatMap.mp h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h'
    simp [ih hq]

/-- At the largest permitted degree (or smallest degree in the column cut)
the coefficient is the product of nonzero leading factors. -/
theorem top_spectral (col : Bool) (ls : List Pair) :
    spectral col ls.length (degree (ls.map (topAt col))) ls =
      coeff col (ls.map (topAt col)) ls := by
  let best := ls.map (topAt col)
  let k := degree best
  let v := coeff col best ls
  have hl : best.length = ls.length := by simp [best]
  change sumI ((polys ls.length).filter (fun ps => degree ps == k)) (fun ps => coeff col ps ls) = v
  rw [show ∀ (xs : List (List Piece)), sumI (xs.filter (fun p => degree p == k))
          (fun p => coeff col p ls) =
       sumI xs (fun p => if degree p = k then coeff col p ls else 0) from by
         intro xs; induction xs with
         | nil => rfl
         | cons p xs ih => by_cases h : degree p = k <;> simp_all [sumI]]
  have reduce (ps : List Piece) (hs : ps ∈ polys ls.length) :
      (if degree ps = k then coeff col ps ls else 0) = if ps = best then v else 0 := by
    by_cases he : ps = best
    · subst ps; simp [k,v]
    · by_cases hd : degree ps = k
      · have hz : coeff col ps ls = 0 := by
          by_cases h : coeff col ps ls = 0
          · exact h
          · have unusual := (sparse col ps ls h).2
            have gt : grade col ps = grade col best := by
              simp only [grade_rev, length_mem' hs, hl, hd, k]
            exact False.elim (he (unusual (gt.trans (top_grade col ls))))
        simp [hd,he,hz]
      · simp [hd,he]
  rw [sumI_list_congr (polys ls.length) reduce, ← hl]
  exact pattern_delta best v

/-- No cancellation at a center label on the two cuts. -/
theorem central_nonzero (col : Bool) (ls : List Pair) (h : capacity ls = ls.length) :
    spectral col ls.length ls.length ls ≠ 0 := by
  have gt := top_grade col ls
  rw [grade_rev,List.length_map,h] at gt
  have hd := deg_bound' (ls.map (topAt col))
  rw [List.length_map] at hd
  have he : degree (ls.map (topAt col)) = ls.length := by cases col <;> simp at * <;> omega
  rw [← he] at ⊢
  conv => lhs; arg 2; rw [he]
  rw [top_spectral]
  exact top_val col ls

end Mobius.RankTrade

namespace Mobius.RankTrade

/-- Symmetric Laurent coefficient at either offset ±j of
(6z+27+6/z)^n. -/
def walk : Nat → Nat → Nat
  | 0,0 => 1
  | 0,_+1 => 0
  | n+1,0 => 27*walk n 0 + 12*walk n 1
  | n+1,j+1 => 6*walk n j + 27*walk n (j+1) + 6*walk n (j+2)

theorem walk_unimodal (n j : Nat) : walk n (j+1) ≤ walk n j := by
  induction n generalizing j with
  | zero => cases j <;> simp [walk]
  | succ n ih =>
    cases j with
    | zero =>
      have h0 : walk n 1 ≤ walk n 0 := ih 0
      have h1 : walk n 2 ≤ walk n 1 := ih 1
      change 6*walk n 0+27*walk n 1+6*walk n 2 ≤ 27*walk n 0+12*walk n 1
      omega
    | succ j =>
      have h0 : walk n (j+1) ≤ walk n j := ih j
      have h1 : walk n (j+2) ≤ walk n (j+1) := ih (j+1)
      have h2 : walk n (j+3) ≤ walk n (j+2) := ih (j+2)
      change 6*walk n (j+1)+27*walk n (j+2)+6*walk n (j+3) ≤
        6*walk n j+27*walk n (j+1)+6*walk n (j+2)
      omega

theorem walk_outside (n j : Nat) (h : n < j) : walk n j = 0 := by
  induction n generalizing j with
  | zero => cases j <;> simp_all [walk]
  | succ n ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [walk, ih j (by omega), ih (j+1) (by omega), ih (j+2) (by omega)]

private theorem walk_le_peak (n j : Nat) : walk n j ≤ walk n 0 := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih => exact Nat.le_trans (walk_unimodal n j) ih

def mass (n : Nat) : Nat → Nat
  | 0 => walk n 0
  | j+1 => mass n j + 2 * walk n (j+1)

private theorem conservation (n j : Nat) :
    mass (n+1) j + 12*walk n j = 39*mass n j + 12*walk n (j+1) := by
  induction j with
  | zero =>
    change 27*walk n 0+12*walk n 1+12*walk n 0 = 39*walk n 0+12*walk n 1
    omega
  | succ j ih =>
    change mass (n+1) j + 2*(6*walk n j+27*walk n (j+1)+6*walk n (j+2)) +
        12*walk n (j+1) = 39*(mass n j + 2*walk n (j+1)) + 12*walk n (j+2)
    omega

theorem walk_total (n : Nat) : mass n n = 39^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := conservation n (n+1)
    have hz : mass n (n+1) = mass n n := by rw [mass,walk_outside n (n+1) (by omega)]; simp
    rw [walk_outside n (n+1) (by omega), walk_outside n (n+2) (by omega), hz, ih] at h
    rw [Nat.pow_succ]; omega

private theorem peak_dominates (n j : Nat) : mass n j ≤ (2*j+1)*walk n 0 := by
  induction j with
  | zero => simp [mass]
  | succ j ih =>
    have h := walk_le_peak n (j+1)
    rw [mass]
    have expand : (2*(j+1)+1)*walk n 0 = (2*j+1)*walk n 0+2*walk n 0 := by
      rw [← Nat.add_mul]; congr 1
    rw [expand]; omega

theorem central_trinomial_bound (t : Nat) : 39^t ≤ (2*t+1)*walk t 0 := by
  rw [← walk_total]
  exact peak_dominates t t

end Mobius.RankTrade

namespace Mobius.RankTrade

def offset (ls : List Pair) : Int := (capacity ls : Int) - ls.length

def hist (t : Nat) (j : Int) := ((words t).filter (fun ls => decide (offset ls = j))).length

private theorem cap_measure (f : Nat → Nat) :
    sumN labels (fun l => f (cap l)) = 36*f 0 + 27*f 1 + f 2 := by
  have h : (labels.map cap).Perm (List.replicate 36 0 ++ List.replicate 27 1 ++ [2]) := by decide
  have v := (h.map f).sum_nat
  simp only [List.map_map,Function.comp_def,List.map_append,List.map_replicate,
    List.map_cons,List.map_nil,List.sum_append,List.sum_replicate_nat,List.sum_cons,
    List.sum_nil,Nat.add_zero,Nat.add_assoc] at v
  rw [Nat.add_assoc]; exact v

private theorem raised (l : Pair) (ls : List Pair) (j : Int) :
    (offset (l::ls) = j) ↔ (offset ls = j+1-cap l) := by
  simp only [offset, capacity,List.length_cons]; omega

private theorem hist_rec (t : Nat) (j : Int) :
    hist (t+1) j = 36*hist t (j+1) + 27*hist t j + hist t (j-1) := by
  unfold hist
  rw [← List.countP_eq_length_filter, words, List.countP_flatMap]
  have h (l : Pair) : List.countP (fun ls => decide (offset ls = j))
      ((words t).map (l :: ·)) = hist t (j+1-cap l) := by
    simp [hist, List.countP_eq_length_filter, List.filter_map, raised, Function.comp_def]
  change sumN labels (fun l => _) = _
  simp only [Function.comp_apply]
  rw [show (fun l => _) = _ from funext h]
  have val := cap_measure (fun k => hist t (j+1-k))
  have h0 : j+1-(0:Nat) = j+1 := by omega
  have h1 : j+1-(1:Nat) = j := by omega
  have h2 : j+1-(2:Nat) = j-1 := by omega
  simpa only [h0,h1,h2,hist] using val

private theorem hist_pair (t j : Nat) :
    6^j * hist t j = walk t j ∧ hist t (-(j:Int)) = 6^j * walk t j := by
  induction t generalizing j with
  | zero =>
    cases j with
    | zero => decide
    | succ j =>
      have hz (z : Int) (neq : (0:Int) ≠ z) : hist 0 z = 0 := by
        unfold hist
        change ((([[]] : List (List Pair)).filter (fun ls => decide (offset ls = z)))).length = 0
        have e : offset [] ≠ z := neq
        simp [e]
      rw [hz _ (by omega), hz _ (by omega)]
      simp [walk]
  | succ t ih =>
    cases j with
    | zero =>
      obtain ⟨h0,_⟩ := ih 0
      obtain ⟨h1,hm1⟩ := ih 1
      change 1*hist t 0 = walk t 0 at h0
      change 6*hist t 1 = walk t 1 at h1
      change hist t (-1) = 6*walk t 1 at hm1
      have rev : hist (t+1) 0 = walk (t+1) 0 := by
        rw [hist_rec]
        change 36*hist t 1+27*hist t 0+hist t (-1) = 27*walk t 0+12*walk t 1
        omega
      simpa using And.intro rev rev
    | succ j =>
      obtain ⟨h0,m0⟩ := ih j
      obtain ⟨h1,m1⟩ := ih (j+1)
      obtain ⟨h2,m2⟩ := ih (j+2)
      have u := hist_rec t (j+1:Nat)
      have v := hist_rec t (-(j+1:Nat))
      have iu : ((j+1:Nat):Int) + 1 = (j+2:Nat) := by omega
      have id : ((j+1:Nat):Int) - 1 = j := by omega
      have im : (-(↑(j+1):Int)) + 1 = -(j:Int) := by omega
      have ip : (-(↑(j+1):Int)) - 1 = -(↑(j+2):Int) := by omega
      rw [iu,id] at u; rw [im,ip] at v
      constructor
      · rw [u, walk]
        calc
          _ = 6 * (6^j * hist t j) + 27 * (6^(j+1) * hist t (j+1:Nat)) +
              6 * (6^(j+2) * hist t (j+2:Nat)) := by
                simp only [Nat.pow_succ,Nat.mul_add]; grind
          _ = _ := by rw [h0,h1,h2]
      · rw [v,m0,m1,m2,walk]
        simp only [Nat.pow_succ,Nat.mul_add]; grind

/-- At least this many actual eight-letter eigenbasis labels survive on
each cut of the center piece. The two remaining factors are polynomial. -/
theorem center_labels_lower (t : Nat) : 39^t ≤ (2*t+1) * hist t 0 := by
  have eq := (hist_pair t 0).1
  simp at eq
  rw [eq]; exact central_trinomial_bound t

end Mobius.RankTrade

namespace Mobius.RankTrade

private def shift (col : Bool) (x : B) := if col then x ^^^ 1 else x

private theorem basis_dot_cell (col : Bool) (a b c d x y : B) :
    basis col (a,b) (x,y) * basis col (c,d) (x,y) =
      if a = c then
        (if y = shift col x ^^^ a then ch b (shift col x) * ch d (shift col x) else 0)
      else 0 := by
  have inv (s z k : B) : s ^^^ z = k ↔ z = s ^^^ k := by revert s z k; decide
  have sign_sq (q : Bool) : bitSign q * bitSign q = 1 := by cases q <;> rfl
  let s := shift col x
  let f := if col then bitSign (x.getLsbD 0) else 1
  have f_sq : f*f = 1 := by cases col <;> simp [f, sign_sq]
  change (if s ^^^ y = a then f * ch b s else 0) *
         (if s ^^^ y = c then f * ch d s else 0) = _
  by_cases ac : a = c
  · subst c
    by_cases h : s ^^^ y = a
    · have hy : y = s ^^^ a := (inv s y a).mp h
      change _ = if a = a then (if y = s ^^^ a then _ else _) else _
      rw [ite_eq_left h, ite_eq_left h, ite_eq_left rfl, ite_eq_left hy]
      calc
        _ = (f*f) * (ch b s * ch d s) := by ac_rfl
        _ = _ := by rw [f_sq, Int.one_mul]
    · have hy := mt (inv s y a).mpr h
      change _ = if a = a then (if y = s ^^^ a then _ else _) else _
      simp [h,hy]
  · by_cases ha : s ^^^ y = a
    · have hc : s ^^^ y ≠ c := fun he => ac (ha.symm.trans he)
      rw [ite_eq_left ha, ite_eq_right hc, ite_eq_right ac, Int.mul_zero]
    · simp [ac,ha]

private theorem delta8 (a : B) (v : Int) :
    (alphabet.map (fun y => if y = a then v else 0)).sum = v := by
  have h : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by
    revert a; decide
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [alphabet]

private theorem char_dot (col : Bool) (b d : B) :
    (alphabet.map (fun x => ch b (shift col x) * ch d (shift col x))).sum =
      if b = d then 8 else 0 := by revert col b d; decide

private theorem sumI_bind' {α β} (xs : List α) (g : α → List β) (f : β → Int) :
    sumI (xs.flatMap g) f = sumI xs (fun a => sumI (g a) f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp_all [sumI,List.sum_append]

private theorem sumI_map' {α β} (xs : List α) (g : α → β) (f : β → Int) :
    sumI (xs.map g) f = sumI xs (fun a => f (g a)) := by simp [sumI,List.map_map,Function.comp_def]

private theorem sumI_smul {α} (xs : List α) (v : Int) (f : α → Int) :
    sumI xs (fun x => v * f x) = v * sumI xs f := by
  induction xs with
  | nil => simp [sumI]
  | cons x xs ih => simp_all [sumI,Int.mul_add]

private theorem sumI_rmul {α} (xs : List α) (v : Int) (f : α → Int) :
    sumI xs (fun x => f x * v) = sumI xs f * v := by
  simpa only [Int.mul_comm] using sumI_smul xs v f

theorem basis_orthogonal (col : Bool) (l m : Pair) :
    sumI labels (fun w => basis col l w * basis col m w) = if l=m then 8 else 0 := by
  obtain ⟨a,b⟩ := l
  obtain ⟨c,d⟩ := m
  simp only [labels,sumI_bind',sumI_map',basis_dot_cell]
  by_cases he : a = c
  · subst c
    simp only [ite_true,Prod.mk.injEq,true_and]
    change (alphabet.map (fun x =>
        (alphabet.map (fun y => if y = shift col x ^^^ a then _ else 0)).sum)).sum = _
    simp only [delta8]
    exact char_dot col b d
  · simp [he,sumI_nothing]

/-- The integral paired bases are orthogonal with uniform squared norm
8^t. In particular distinct surviving spectral labels are independent. -/
theorem word_orthogonal (col : Bool) (ls ms : List Pair) (len : ms.length = ls.length) :
    sumI (words ls.length) (fun w => amplitudes col ls w * amplitudes col ms w) =
      if ls=ms then 8^ls.length else 0 := by
  induction ls generalizing ms with
  | nil =>
    have h := List.length_eq_zero_iff.mp len
    subst ms; decide +revert
  | cons a ls ih =>
    cases ms with
    | nil => simp at len
    | cons b ms =>
      have hl : ms.length = ls.length := Nat.succ.inj len
      simp only [List.length_cons,words,sumI_bind',sumI_map']
      let am := fun l => basis col a l * basis col b l
      let tail := fun w => amplitudes col ls w * amplitudes col ms w
      have sum_for_label (l : Pair) :
          sumI (words ls.length) (fun w => amplitudes col (a::ls) (l::w) *
            amplitudes col (b::ms) (l::w)) = am l * (if ls=ms then 8^ls.length else 0) := by
        have h (w : List Pair) : amplitudes col (a::ls) (l::w) * amplitudes col (b::ms) (l::w) =
            am l * tail w := by simp only [amplitudes,prod2,am,tail]; ac_rfl
        rw [show (fun w => _) = _ from funext h, sumI_smul]
        exact congrArg (am l * ·) (ih ms hl)
      rw [show (fun l => _) = _ from funext sum_for_label, sumI_rmul,
        show sumI labels am = _ from basis_orthogonal col a b]
      by_cases eq : a = b <;> by_cases rest : ls = ms <;>
        simp [eq,rest,Int.pow_succ,Int.mul_comm]

end Mobius.RankTrade

namespace Mobius.RankTrade

def live (col : Bool) (t k : Nat) :=
    ((words t).filter fun ls => decide (spectral col t k ls ≠ 0)).length

private theorem words_mem_length {t : Nat} {ls : List Pair} (h : ls ∈ words t) : ls.length = t := by
  induction t generalizing ls with
  | zero => simp_all [words]
  | succ t ih =>
    obtain ⟨l,_,hs⟩ := List.mem_flatMap.mp h
    obtain ⟨ws,hw,rfl⟩ := List.mem_map.mp hs
    simp [ih hw]

private theorem filtered_le {α} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = true → g x = true) :
    (xs.filter f).length ≤ (xs.filter g).length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x (by simp)
    cases eq : f x <;> cases eq' : g x <;> simp_all <;> omega

theorem live_center_bound (col : Bool) (t : Nat) : 39^t ≤ (2*t+1)*live col t t := by
  apply Nat.le_trans (center_labels_lower t)
  apply Nat.mul_le_mul_left
  apply filtered_le
  intro ls hm hz
  have hl := words_mem_length hm
  have zero : offset ls = 0 := of_decide_eq_true hz
  have he : capacity ls = ls.length := by unfold offset at zero; omega
  have present := central_nonzero col ls he
  rw [hl] at present
  exact decide_eq_true present

theorem center_spectrum_product (t : Nat) :
    1521^t ≤ (2*t+1)^2 * (live false t t * live true t t) := by
  have h := Nat.mul_le_mul (live_center_bound false t) (live_center_bound true t)
  calc
    1521^t = 39^t * 39^t := by rw [← Nat.mul_pow]
    _ ≤ _ := h
    _ = _ := by rw [Nat.pow_two]; ac_rfl

end Mobius.RankTrade

namespace Mobius.RankTrade

theorem words_unique (t : Nat) : (words t).Nodup := by
  induction t with
  | zero => decide
  | succ t ih =>
    change List.Pairwise (· ≠ ·) (labels.flatMap fun a => (words t).map (a :: ·))
    apply List.pairwise_flatMap.mpr
    constructor
    · intro a _
      apply List.pairwise_map.mpr
      exact ih.imp (fun h eq => h (List.cons.inj eq).2)
    · have unique : labels.Nodup := by decide
      apply unique.imp
      intro a b h x hx y hy
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
      exact fun eq => h (List.cons.inj eq).1

end Mobius.RankTrade
