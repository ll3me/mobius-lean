import Mobius.RankTradeSharp

/-! A finite rank lower bound without a matrix library or division.
A pivot on the first diagonal row eliminates one separated term. -/
namespace Mobius.RankTrade

abbrev Separation (α : Type) := (α → Int) × (α → Int)

def sep {α} (fs : List (Separation α)) (x y : α) :=
  sumI fs (fun f => f.1 x * f.2 y)

private theorem plus_sep {α} (a b : List (Separation α)) (x y : α) :
    sep (a++b) x y = sep a x y + sep b x y := by simp [sep,sumI,List.sum_append]

private theorem pivot_exists {α} (fs : List (Separation α)) (x : α) (h : sep fs x x ≠ 0) :
    ∃ pre f post, fs = pre ++ (f :: post) ∧ f.1 x ≠ 0 := by
  induction fs with
  | nil => simp [sep,sumI] at h
  | cons f fs ih =>
    by_cases hz : f.1 x = 0
    · have t : sep fs x x ≠ 0 := by simpa [sep,sumI,hz] using h
      obtain ⟨a,g,b,hg,nz⟩ := ih t
      exact ⟨f::a,g,b,by simp [hg],nz⟩
    · exact ⟨[],f,fs,rfl,hz⟩

private def removeRow {α} (x : α) (p : Separation α) (f : Separation α) : Separation α :=
    (fun y => p.1 x*f.1 y-p.1 y*f.1 x, f.2)

private theorem remove_value {α} (fs : List (Separation α)) (x : α) (p : Separation α) (y z : α) :
    sep (fs.map (removeRow x p)) y z = p.1 x * sep fs y z - p.1 y * sep fs x z := by
  induction fs with
  | nil => simp [sep,sumI]
  | cons f fs ih =>
    change (p.1 x*f.1 y-p.1 y*f.1 x)*f.2 z + sep (fs.map (removeRow x p)) y z =
      p.1 x * (f.1 y*f.2 z+sep fs y z) - p.1 y*(f.1 x*f.2 z+sep fs x z)
    rw [ih]
    grind

/-- An integer separated factorization of a diagonal matrix with nonzero
diagonal needs at least as many terms as there are distinct indices. -/
theorem diagonal_lower {α} (keys : List α) (fs : List (Separation α)) (nodup : keys.Nodup)
    (diag : ∀ i ∈ keys, sep fs i i ≠ 0)
    (off : ∀ i ∈ keys, ∀ j ∈ keys, i ≠ j → sep fs i j = 0) :
    keys.length ≤ fs.length := by
  induction keys generalizing fs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp nodup
    obtain ⟨a,p,b,rfl,nz⟩ := pivot_exists fs x (diag x (by simp))
    let shorter := (a++b).map (removeRow x p)
    have value (y z : α) (hz : z ∈ xs) :
        sep shorter y z = p.1 x * sep (a++p::b) y z := by
      have eq : sep ((a++p::b).map (removeRow x p)) y z = sep shorter y z := by
        simp only [List.map_append,List.map_cons,plus_sep,shorter]
        change _ + ((p.1 x*p.1 y-p.1 y*p.1 x)*p.2 z+_) = _
        rw [Int.mul_comm (p.1 x) (p.1 y),Int.sub_self,Int.zero_mul,Int.zero_add]; rfl
      rw [← eq,remove_value,off x (by simp) z (by simp [hz]) (fun h => fresh (h ▸ hz))]
      simp
    have h := ih shorter tail
      (fun y hy => by rw [value y y hy]; exact Int.mul_ne_zero nz (diag y (by simp [hy])))
      (fun y hy z hz neq => by rw [value y z hz, off y (by simp [hy]) z (by simp [hz]) neq,
          Int.mul_zero])
    simp only [List.length_map, List.length_append, List.length_cons, shorter] at h ⊢
    omega

abbrev Word := List Pair

private theorem factor_sum {α} (xs : List α) (f g : α → Int) (h : ∀ x ∈ xs, f x = g x) :
    sumI xs f = sumI xs g := by unfold sumI; rw [List.map_congr_left h]

private theorem add_sum {α} (xs : List α) (f g : α → Int) :
    sumI xs (fun x => f x+g x) = sumI xs f + sumI xs g := by
  induction xs <;> simp_all [sumI] <;> omega

private theorem zero_sum {α} (xs : List α) : sumI xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all [sumI]

private theorem left_sum {α} (xs : List α) (f : α → Int) (s : Int) :
    sumI xs (fun x => s*f x) = s*sumI xs f := by
  induction xs <;> simp_all [sumI,Int.mul_add]

private theorem right_sum {α} (xs : List α) (f : α → Int) (s : Int) :
    sumI xs (fun x => f x*s) = sumI xs f*s := by simpa only [Int.mul_comm] using left_sum xs f s

private theorem sum_swap {α β} (xs : List α) (ys : List β) (f : α → β → Int) :
    sumI xs (fun x => sumI ys (f x)) = sumI ys (fun y => sumI xs (fun x => f x y)) := by
  induction xs with
  | nil => change 0 = sumI ys (fun _ => 0); rw [zero_sum]
  | cons x xs ih =>
    change sumI ys (f x) + sumI xs (fun a => sumI ys (f a)) =
      sumI ys (fun y => f x y + sumI xs (fun a => f a y))
    rw [ih,add_sum]

private theorem length_of_word {t : Nat} {w : Word} (h : w ∈ words t) : w.length=t := by
  induction t generalizing w with
  | zero => simp_all [words]
  | succ t ih =>
    obtain ⟨a,_,hz⟩ := List.mem_flatMap.mp h
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz
    simp [ih hr]

/-- Project one side of an arbitrary integer factor into the Pauli basis. -/
def project (col : Bool) (t : Nat) (f : Word → Int) (lab : Word) :=
    sumI (words t) (fun x => amplitudes col lab x * f x)

def probe (col : Bool) (t : Nat) (m : Word → Word → Int) (i j : Word) :=
    sumI (words t) (fun x => amplitudes col i x * project col t (m x) j)

private theorem project_linear (col : Bool) (t : Nat) (fs : List (Separation Word)) (i j : Word) :
    probe col t (sep fs) i j =
      sep (fs.map fun f => (project col t f.1,project col t f.2)) i j := by
  induction fs with
  | nil => simp [probe,project,sep,sumI,show
        (List.map (fun _ : Word => (0:Int)) (words t)).sum = 0 from zero_sum (words t)]
  | cons f fs ih =>
    have inn (x : Word) : project col t (sep (f::fs) x) j =
        f.1 x * project col t f.2 j + project col t (sep fs x) j := by
      unfold project
      have h (y : Word) : amplitudes col j y * sep (f::fs) x y =
          f.1 x * (amplitudes col j y*f.2 y) + amplitudes col j y*sep fs x y := by
        change _*(f.1 x*f.2 y + sep fs x y) = _
        grind
      rw [show (fun y => _) = _ from funext h, add_sum,left_sum]
    unfold probe
    simp only [inn]
    have ho (x : Word) : amplitudes col i x *
          (f.1 x * project col t f.2 j + project col t (sep fs x) j) =
          (amplitudes col i x*f.1 x)*project col t f.2 j +
          amplitudes col i x*project col t (sep fs x) j := by grind
    rw [show (fun x => _) = _ from funext ho,add_sum,right_sum]
    change project col t f.1 i * project col t f.2 j + probe col t (sep fs) i j = _
    rw [ih]; rfl

end Mobius.RankTrade

namespace Mobius.RankTrade

def mode (col : Bool) (t k : Nat) (l : Word) : Separation Word :=
  (fun x => amplitudes col l x * spectral col t k l, amplitudes col l)

def canonical (col : Bool) (t k : Nat) := (admissible col t k).map (mode col t k)

private theorem canonical_physical (col : Bool) (ws : List Tile) (k : Nat) :
    sep (canonical col ws.length k) (ws.map (·.left col)) (ws.map (·.right col)) =
      8^ws.length * grouped ws k := by
  simpa only [sep,canonical,sumI,List.map_map,Function.comp_def,mode] using
    integer_factorization col ws k

private theorem projected_mode (col : Bool) (t k : Nat) (l i j : Word)
    (hl : l.length=t) (hi : i.length=t) (hj : j.length=t) :
    project col t (mode col t k l).1 i * project col t (mode col t k l).2 j =
      ((if i=l then 8^t else 0)*spectral col t k l) * (if j=l then 8^t else 0) := by
  have hi' := word_orthogonal col i l (hl.trans hi.symm)
  have hj' := word_orthogonal col j l (hl.trans hj.symm)
  rw [hi] at hi'; rw [hj] at hj'
  have first : project col t (mode col t k l).1 i =
      (if i=l then 8^t else 0)*spectral col t k l := by
    unfold project mode
    have re (x : Word) : amplitudes col i x * (amplitudes col l x * spectral col t k l) =
        (amplitudes col i x * amplitudes col l x) * spectral col t k l := by ac_rfl
    rw [show (fun x => _) = _ from funext re, right_sum, hi']
  rw [first]
  exact congrArg (_ * ·) hj'

private theorem single_key {α} [DecidableEq α] (xs : List α) (i : α) (v : Int) (h : xs.Nodup) :
    sumI xs (fun x => if i=x then v else 0) = if i ∈ xs then v else 0 := by
  induction xs with
  | nil => simp [sumI]
  | cons x xs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp h
    change (if i=x then v else 0) + sumI xs (fun y => if i=y then v else 0) = _
    rw [ih tail]
    by_cases eq : i=x <;> simp_all

def centers (t : Nat) := (words t).filter (fun ls => decide (offset ls=0))

private theorem center_mem {t : Nat} {i : Word} (h : i ∈ centers t) :
    i ∈ words t ∧ i.length=t ∧ capacity i=t := by
  obtain ⟨hi,hz⟩ := List.mem_filter.mp h
  have len := length_of_word hi
  have h0 : offset i=0 := of_decide_eq_true hz
  unfold offset at h0
  exact ⟨hi,len,by omega⟩

private theorem center_allowed (col : Bool) {t : Nat} {i : Word} (h : i ∈ centers t) :
    i ∈ admissible col t t := by
  obtain ⟨hi,_,cap⟩ := center_mem h
  apply List.mem_filter.mpr
  refine ⟨hi,?_⟩
  cases col <;> simp [cap] <;> omega

private theorem center_probe (col : Bool) (t : Nat) (i j : Word)
    (hi : i ∈ centers t) (hj : j ∈ centers t) :
    probe col t (sep (canonical col t t)) i j =
      if i=j then (8^t * spectral col t t i) * 8^t else 0 := by
  obtain ⟨_,li,_⟩ := center_mem hi
  obtain ⟨_,lj,_⟩ := center_mem hj
  rw [project_linear]
  unfold sep canonical
  simp only [sumI,List.map_map,Function.comp_def]
  change sumI (admissible col t t) (fun l => project col t (mode col t t l).1 i *
      project col t (mode col t t l).2 j) = _
  by_cases eq : i=j
  · subst j
    have one (l : Word) (mem : l ∈ admissible col t t) :
        project col t (mode col t t l).1 i * project col t (mode col t t l).2 i =
        if i=l then (8^t*spectral col t t i)*8^t else 0 := by
      rw [projected_mode col t t l i i (length_of_word (List.mem_filter.mp mem).1) li li]
      by_cases hl : i=l <;> simp [hl]
    have unique : (admissible col t t).Nodup := (words_unique t).filter _
    rw [factor_sum _ _ _ one, single_key (admissible col t t) i _ unique]
    simp [center_allowed col hi]
  · have none (l : Word) (mem : l ∈ admissible col t t) :
        project col t (mode col t t l).1 i * project col t (mode col t t l).2 j = 0 := by
      rw [projected_mode col t t l i j (length_of_word (List.mem_filter.mp mem).1) li lj]
      by_cases hl : i=l
      · have hjl : j≠l := fun e => eq (hl.trans e.symm)
        simp [hjl]
      · simp [hl]
    rw [factor_sum _ _ _ none, zero_sum]
    simp [eq]

def makeTile (col : Bool) (l r : Pair) : Tile :=
    if col then ⟨l.1,r.2,l.2,r.1⟩ else ⟨l.1,l.2,r.2,r.1⟩

private theorem assemble (col : Bool) (x y : Word) (len : x.length=y.length) :
    let ws := List.zipWith (makeTile col) x y
    ws.map (·.left col) = x ∧ ws.map (·.right col) = y ∧ ws.length=x.length := by
  induction x generalizing y with
  | nil =>
    have hy : y=[] := List.length_eq_zero_iff.mp len.symm
    subst y; simp
  | cons a x ih =>
    cases y with
    | nil => simp at len
    | cons b y =>
      obtain ⟨hl,hr,hn⟩ := ih y (Nat.succ.inj len)
      have l : (makeTile col a b).left col = a := by cases col <;> rfl
      have r : (makeTile col a b).right col = b := by cases col <;> rfl
      simp [List.zipWith,l,r,hl,hr,hn]

private theorem probe_congr (col : Bool) (t : Nat) (a b : Word → Word → Int)
    (h : ∀ x ∈ words t, ∀ y ∈ words t, a x y = b x y) (i j : Word) :
    probe col t a i j = probe col t b i j := by
  apply factor_sum
  intro x hx
  apply congrArg (amplitudes col i x * ·)
  apply factor_sum
  intro y hy
  rw [h x hx y hy]

/-- Every integer separated factorization of the physical center piece, on
either cut, has exponential rate at least 39 per three-bit block. -/
theorem arbitrary_center_lower (col : Bool) (t : Nat) (fs : List (Separation Word))
    (rep : ∀ ws : List Tile, ws.length=t →
      sep fs (ws.map (·.left col)) (ws.map (·.right col)) = 8^t*grouped ws t) :
    39^t ≤ (2*t+1)*fs.length := by
  have same (x : Word) (hx : x ∈ words t) (y : Word) (hy : y ∈ words t) :
      sep fs x y = sep (canonical col t t) x y := by
    have lx := length_of_word hx
    have ly := length_of_word hy
    let ws := List.zipWith (makeTile col) x y
    obtain ⟨rl,rr,ln⟩ := assemble col x y (lx.trans ly.symm)
    have hlen : ws.length=t := ln.trans lx
    have canon := canonical_physical col ws t
    have f := rep ws hlen
    change ws.map (·.left col) = x at rl
    change ws.map (·.right col) = y at rr
    rw [rl,rr,hlen] at canon
    rw [rl,rr] at f
    exact f.trans canon.symm
  let projected : List (Separation Word) :=
    fs.map fun f => (project col t f.1,project col t f.2)
  have agreement (i j : Word) (hi : i ∈ centers t) (hj : j ∈ centers t) :
      sep projected i j = if i=j then (8^t*spectral col t t i)*8^t else 0 := by
    rw [show sep projected i j = _ from (project_linear col t fs i j).symm,
      probe_congr col t _ _ same i j, center_probe col t i j hi hj]
  have h := diagonal_lower (centers t) projected ((words_unique t).filter _)
    (fun i hi => by
      rw [agreement i i hi hi, ite_eq_left rfl]
      obtain ⟨_,len,hcap⟩ := center_mem hi
      have lives := central_nonzero col i (hcap.trans len.symm)
      rw [len] at lives
      exact Int.mul_ne_zero (Int.mul_ne_zero (Int.pow_ne_zero (by decide)) lives)
        (Int.pow_ne_zero (by decide)))
    (fun i hi j hj hne => by rw [agreement i j hi hj, ite_eq_right hne])
  change hist t 0 ≤ (fs.map _).length at h
  rw [List.length_map] at h
  exact Nat.le_trans (center_labels_lower t) (Nat.mul_le_mul_left _ h)

/-- A lower bound for arbitrary row and column certificates of the center. -/
theorem arbitrary_center_product (t : Nat) (r c : List (Separation Word))
    (row : ∀ ws : List Tile, ws.length=t →
      sep r (ws.map (·.left false)) (ws.map (·.right false)) = 8^t*grouped ws t)
    (column : ∀ ws : List Tile, ws.length=t →
      sep c (ws.map (·.left true)) (ws.map (·.right true)) = 8^t*grouped ws t) :
    1521^t ≤ (2*t+1)^2*(r.length*c.length) := by
  calc
    1521^t = 39^t * 39^t := by rw [← Nat.mul_pow]
    _ ≤ _ := Nat.mul_le_mul (arbitrary_center_lower false t r row)
      (arbitrary_center_lower true t c column)
    _ = _ := by rw [Nat.pow_two]; ac_rfl

end Mobius.RankTrade
