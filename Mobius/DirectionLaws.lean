import Mobius.OptimalCertificate

/-!
# Direction-homogeneous seam laws

An arbitrary phase table can realize every sum of positive-degree monomials
of degree at most three. Conversely, a homogeneous direction function has
zero parity on every Boolean cube of dimension at least four based at zero.
Using coordinate directions, these parities are its multilinear ANF
coefficients. A slice induction establishes the sharp directional failure
bound in arbitrary dimension. The ANF identification is in docs/DirectionLaws.md.
-/

namespace Mobius.DirectionLaws

open SignObstruction

def square (p : BitVec m → BitVec m → Bool) (x y d : BitVec m) : Bool :=
  p x y ^^ (p (x ^^^ d) y ^^ (p x (y ^^^ d) ^^ p (x ^^^ d) (y ^^^ d)))

def Homogeneous (p : BitVec m → BitVec m → Bool) (g : BitVec m → Bool) : Prop :=
  ∀ x y d, square p x y d = g d

theorem law_zero {p : BitVec m → BitVec m → Bool} {g} (law : Homogeneous p g) : g 0 = false := by
  simpa [square] using (law 0 0 0).symm

private theorem total_map (f : β → Bool) (e : α → β) (xs : List α) :
    total f (xs.map e) = total (fun a => f (e a)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [total, ih]

private theorem sum_over_rectangles (f : Cell → Bool) (g : Rectangle → Bool)
    (localLaw : ∀ r, total f (corners r) = g r) (rs : List Rectangle) :
    total f (rs.flatMap corners) = total g rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [List.flatMap_cons, total_append, localLaw, ih]; rfl

/-- The image of the 15-direction certificate has zero parity under *any*
    linear map, including maps for which some chosen directions coincide. -/
theorem four_space_parity {p : BitVec m → BitVec m → Bool} {g} (law : Homogeneous p g)
    (e : B → BitVec m) (lin : ∀ x y, e (x ^^^ y) = e x ^^^ e y) :
    total (fun d => g (e d)) directions = false := by
  let f (c : Cell) := p (e c.1) (e c.2)
  let weight (r : Rectangle) := g (e r.2.2)
  have localLaw (r : Rectangle) : total f (corners r) = weight r := by
    obtain ⟨x,y,d⟩ := r
    simpa [weight, f, corners, total, lin, square] using law (e x) (e y) (e d)
  have parity := (sum_over_rectangles f weight localLaw certificate).symm.trans
    ((total_perm f cells_paired).trans (total_paired f usedCells))
  have shape : (certificate.map fun r => r.2.2).Perm directions := by decide
  rw [← total_perm (fun z => g (e z)) shape, total_map]
  exact parity

/-- Enumerate vertices with multiplicity: dependent directions pair equal
    vertices, so this works without an independence hypothesis. -/
def cube (steps : List (BitVec m)) (x : BitVec m) : List (BitVec m) :=
  match steps with
  | [] => [x]
  | a :: tail => cube tail x ++ cube tail (x ^^^ a)

def cubeParity (steps : List (BitVec m)) (g : BitVec m → Bool) (x : BitVec m) : Bool :=
  total g (cube steps x)

private theorem parity_cons (a : BitVec m) (steps : List (BitVec m))
    (g : BitVec m → Bool) (x : BitVec m) :
    cubeParity (a::steps) g x = (cubeParity steps g x ^^ cubeParity steps g (x ^^^ a)) :=
  total_append ..

private theorem cube_pullback (e : BitVec m → BitVec n) (lin : ∀ a b, e (a ^^^ b) = e a ^^^ e b)
    (steps : List (BitVec m)) (g : BitVec n → Bool) (x : BitVec m) :
    cubeParity steps (fun a => g (e a)) x = cubeParity (steps.map e) g (e x) := by
  induction steps generalizing x with
  | nil => rfl
  | cons d ds ih => simp only [parity_cons, List.map_cons, ih, lin]

private def gate (t : Bool) (x : BitVec m) := if t then x else 0

private def linear4 (a b c d : BitVec m) (x : B) : BitVec m :=
  gate (x.getLsbD 0) a ^^^ gate (x.getLsbD 1) b ^^^
  gate (x.getLsbD 2) c ^^^ gate (x.getLsbD 3) d

private theorem gate_xor (p q : Bool) (x : BitVec m) :
    gate (p ^^ q) x = gate p x ^^^ gate q x := by
  cases p <;> cases q <;> simp [gate]

private theorem linear4_xor (a b c d : BitVec m) (x y : B) :
    linear4 a b c d (x ^^^ y) = linear4 a b c d x ^^^ linear4 a b c d y := by
  simp only [linear4, BitVec.getLsbD_xor, gate_xor]
  ac_rfl

private theorem cube_four {p : BitVec m → BitVec m → Bool} {g} (law : Homogeneous p g)
    (a b c d : BitVec m) : cubeParity [a,b,c,d] g 0 = false := by
  let e := linear4 a b c d
  have lin := linear4_xor a b c d
  have basis : ([1,2,4,8] : List B).map e = [a,b,c,d] := by
    change [a ^^^ 0 ^^^ 0 ^^^ 0, 0 ^^^ b ^^^ 0 ^^^ 0, 0 ^^^ 0 ^^^ c ^^^ 0,
      0 ^^^ 0 ^^^ 0 ^^^ d] = _
    simp
  have zero : e 0 = 0 := by
    change ((0 : BitVec m) ^^^ 0 ^^^ 0 ^^^ 0) = 0
    simp
  have list_eq : (cube ([1,2,4,8] : List B) 0).Perm (0 :: directions) := by decide
  have translated := cube_pullback e lin [1,2,4,8] g 0
  rw [basis, zero] at translated
  rw [← translated]
  unfold cubeParity
  rw [total_perm _ list_eq]
  change (g (e 0) ^^ total (fun z => g (e z)) directions) = false
  rw [zero, law_zero law, four_space_parity law e lin]; rfl

private theorem xor_join (w x y z : Bool) :
    ((w ^^ y) ^^ (x ^^ z)) = ((w ^^ x) ^^ ((w ^^ y) ^^ (w ^^ z))) := by
  cases w <;> cases x <;> cases y <;> cases z <;> rfl

/-- Δ_a Δ_b = Δ_a + Δ_b + Δ_(a+b) over GF(2). It replaces a long
    cube by three shorter cubes, including one in a non-coordinate direction. -/
theorem merge_steps (a b : BitVec m) (steps : List (BitVec m)) (g : BitVec m → Bool) :
    cubeParity (a::b::steps) g 0 =
      (cubeParity (a::steps) g 0 ^^
        (cubeParity (b::steps) g 0 ^^ cubeParity ((a ^^^ b)::steps) g 0)) := by
  simp only [parity_cons, BitVec.xor_assoc]
  exact xor_join ..

theorem high_cube_coefficients_vanish {p : BitVec m → BitVec m → Bool} {g}
    (law : Homogeneous p g) (steps : List (BitVec m)) (high : 4 ≤ steps.length) :
    cubeParity steps g 0 = false := by
  have go (k : Nat) : ∀ ds : List (BitVec m), ds.length = 4 + k → cubeParity ds g 0 = false := by
    induction k with
    | zero =>
      intro ds h
      cases ds with | nil => simp at h | cons a ds =>
      cases ds with | nil => simp at h | cons b ds =>
      cases ds with | nil => simp at h | cons c ds =>
      cases ds with | nil => simp at h | cons d ds =>
      cases ds with
      | nil => exact cube_four law a b c d
      | cons z tail => simp at h
    | succ k ih =>
      intro ds h
      cases ds with | nil => simp at h | cons a ds =>
      cases ds with
      | nil => simp at h; omega
      | cons b rest =>
        rw [merge_steps]
        have len (t : BitVec m) : (t::rest).length = 4 + k := by
          simp only [List.length_cons] at h ⊢; omega
        rw [ih _ (len a), ih _ (len b), ih _ (len (a ^^^ b))]
        rfl
  exact go (steps.length-4) steps (by omega)

inductive Monomial (n : Nat) where
  | linear (i : Fin n)
  | quad (i j : Fin n)
  | cubic (i j k : Fin n)

def Monomial.eval (t : Monomial n) (d : BitVec n) : Bool :=
  match t with
  | .linear i => d.getLsbD i.val
  | .quad i j => d.getLsbD i.val && d.getLsbD j.val
  | .cubic i j k => d.getLsbD i.val && d.getLsbD j.val && d.getLsbD k.val

private def primitive3 (a b c u v w : Bool) : Bool :=
  (a && b && w) ^^ ((b && c && u) ^^ (c && a && v))

def Monomial.phase (t : Monomial n) (x y : BitVec n) : Bool :=
  match t with
  | .linear i => x.getLsbD i.val && y.getLsbD i.val
  | .quad i j => x.getLsbD i.val && y.getLsbD j.val
  | .cubic i j k => primitive3 (x.getLsbD i.val) (x.getLsbD j.val) (x.getLsbD k.val)
      (y.getLsbD i.val) (y.getLsbD j.val) (y.getLsbD k.val)

private theorem product_table (a u z t : Bool) :
    ((a && u) ^^ (((a ^^ z) && u) ^^ ((a && (u ^^ t)) ^^ ((a ^^ z) && (u ^^ t))))) =
    (z && t) := by
  revert a u z t
  decide

private theorem cubic_table (a b c u v w h i j : Bool) :
    (primitive3 a b c u v w ^^ (primitive3 (a^^h) (b^^i) (c^^j) u v w ^^
     (primitive3 a b c (u^^h) (v^^i) (w^^j) ^^
      primitive3 (a^^h) (b^^i) (c^^j) (u^^h) (v^^i) (w^^j)))) = (h && i && j) := by
  revert a b c u v w h i j
  decide

theorem monomial_homogeneous (t : Monomial n) : Homogeneous t.phase t.eval := by
  intro x y d
  cases t <;> simp only [square, Monomial.eval, Monomial.phase, BitVec.getLsbD_xor]
  · rename_i i
    simpa only [Bool.and_self] using product_table (x.getLsbD i) (y.getLsbD i)
      (d.getLsbD i) (d.getLsbD i)
  · exact product_table ..
  · exact cubic_table ..

private theorem xor8 (a b c d e f g h : Bool) :
    ((a^^e) ^^ ((b^^f) ^^ ((c^^g) ^^ (d^^h)))) = ((a^^(b^^(c^^d))) ^^ (e^^(f^^(g^^h)))) := by
  revert a b c d e f g h
  decide

/-- The constructive converse for any ANF given as a list of degree 1–3
    monomials. Repeated indices and repeated monomials are allowed. -/
theorem cubic_ANF_realized (terms : List (Monomial n)) :
    Homogeneous (fun x y => total (fun t => t.phase x y) terms)
                (fun d => total (fun t => t.eval d) terms) := by
  intro x y d
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [square, total, xor8] at ih ⊢
    change (square t.phase x y d ^^ _) = _
    rw [monomial_homogeneous t x y d, ih]

/-- Derivative formulation of bounded Boolean degree. -/
def DegreeLE (r : Nat) (g : BitVec m → Bool) : Prop :=
  ∀ (ds : List (BitVec m)) x, r < ds.length → cubeParity ds g x = false

theorem homogeneous_degree {p : BitVec m → BitVec m → Bool} {g} (law : Homogeneous p g) :
    DegreeLE 3 g := by
  intro ds x h
  have big := high_cube_coefficients_vanish law (x::ds) (by simp; omega)
  have orig := high_cube_coefficients_vanish law ds (by omega)
  have zx : (0 : BitVec m) ^^^ x = x := by simp
  rw [parity_cons, orig, zx] at big
  simpa only [Bool.false_xor] using big

private theorem parity_xor (ds : List (BitVec m)) (f g : BitVec m → Bool) (x) :
    cubeParity ds (fun v => f v ^^ g v) x = (cubeParity ds f x ^^ cubeParity ds g x) := by
  induction ds generalizing x with
  | nil => simp [cubeParity, cube, total]
  | cons a ds ih =>
    simp only [parity_cons, ih]
    generalize cubeParity ds f x = a1; generalize cubeParity ds g x = a2
    generalize cubeParity ds f (x ^^^ a) = a3; generalize cubeParity ds g (x ^^^ a) = a4
    cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> rfl

private theorem parity_constant (ds : List (BitVec m)) (b : Bool) (x) :
    cubeParity ds (fun _ => b) x = (if ds = [] then b else false) := by
  induction ds generalizing x with
  | nil => simp [cubeParity, cube, total]
  | cons a ds ih => simp [parity_cons, ih]

theorem degree_not (H : DegreeLE r (m := m) g) : DegreeLE r (fun a => !(g a)) := by
  intro ds v h
  have nonempty : ds ≠ [] := fun e => by subst ds; simp at h
  have not_as_xor : (fun a => !(g a)) = (fun a => g a ^^ true) := by simp
  rw [not_as_xor, parity_xor, H ds v h, parity_constant]
  simp [nonempty]

/-- Truth-table Hamming weight, enumerating the two values of the final bit. -/
def weight : {m : Nat} → (BitVec m → Bool) → Nat
  | 0, f => (f 0).toNat
  | m+1, f => weight (fun a : BitVec m => f (a.concat false)) +
      weight (fun a : BitVec m => f (a.concat true))

private theorem weight_positive (f : BitVec m → Bool) (x : BitVec m) (hx : f x = true) :
    0 < weight f := by
  induction m with
  | zero =>
    have he : x = 0 := BitVec.of_length_zero
    simp only [weight, ← he, hx]; decide
  | succ m ih =>
    let hi := x.extractLsb' 1 m
    let bit := x.getLsb 0
    have rebuild : hi.concat bit = x := BitVec.concat_extractLsb'_getLsb
    have h : f (hi.concat bit) = true := rebuild ▸ hx
    unfold weight
    cases hb : bit with
    | false =>
      have := ih (fun a => f (a.concat false)) hi (hb ▸ h)
      omega
    | true =>
      have := ih (fun a => f (a.concat true)) hi (hb ▸ h)
      omega

private theorem weight_xor_le (f g : BitVec m → Bool) :
    weight (fun a => f a ^^ g a) ≤ weight f + weight g := by
  induction m with
  | zero =>
    simp only [weight]
    cases f 0 <;> cases g 0 <;> decide
  | succ m ih =>
    have left := ih (fun a => f (a.concat false)) (fun a => g (a.concat false))
    have right := ih (fun a => f (a.concat true)) (fun a => g (a.concat true))
    simp only [weight]
    omega

private theorem slice_parity (b : Bool) (ds : List (BitVec m)) (f : BitVec (m+1) → Bool) (x) :
    cubeParity ds (fun a => f (a.concat b)) x =
      cubeParity (ds.map (fun a => a.concat false)) f (x.concat b) := by
  induction ds generalizing x with
  | nil => rfl
  | cons a ds ih =>
    simp only [List.map_cons, parity_cons, ih, BitVec.concat_xor_concat, Bool.xor_false]

private theorem slice_degree (f : BitVec (m+1) → Bool) (h : DegreeLE r f) (b : Bool) :
    DegreeLE r (fun a => f (a.concat b)) := by
  intro ds x high
  rw [slice_parity]
  exact h _ _ (by simpa using high)

private theorem difference_degree (f : BitVec (m+1) → Bool) (h : DegreeLE (r+1) f) :
    DegreeLE r (fun a : BitVec m => f (a.concat false) ^^ f (a.concat true)) := by
  intro ds x high
  let steps := ds.map (fun a => a.concat false)
  let toggle := (0 : BitVec m).concat true
  have v := h (toggle :: steps) (x.concat false) (by simp [steps]; omega)
  have turn : x.concat false ^^^ toggle = x.concat true := by
    unfold toggle; rw [BitVec.concat_xor_concat]; simp
  rw [parity_cons,turn] at v
  rw [parity_xor, slice_parity, slice_parity]
  exact v

/-- Elementary minimum-weight bound for Reed–Muller functions, proved by
    comparing two slices and their Boolean difference. -/
theorem minimum_weight (f : BitVec m → Bool) (positive : 0 < weight f)
    (h : DegreeLE r f) : 2^(m-r) ≤ weight f := by
  induction m generalizing r with
  | zero => simp; omega
  | succ m ih =>
    by_cases large : m < r
    · have s : m+1-r = 0 := by omega
      simp [s]; omega
    let left (x : BitVec m) := f (x.concat false)
    let right (x : BitVec m) := f (x.concat true)
    have split : weight f = weight left + weight right := rfl
    by_cases same : left = right
    · rw [← same] at split
      have posL : 0 < weight left := by omega
      have bound := ih left posL (slice_degree f h false)
      rw [show m+1-r = (m-r)+1 by omega, Nat.pow_succ, split]
      omega
    · have differs : ∃ x, left x ≠ right x := by
        apply Classical.byContradiction
        intro none
        apply same
        funext x
        exact Classical.byContradiction (fun ne => none ⟨x,ne⟩)
      obtain ⟨x,hx⟩ := differs
      have value : (left x ^^ right x) = true := by
        cases a : left x <;> cases b : right x <;> simp_all
      cases r with
      | zero =>
        have impossible := h [(0 : BitVec m).concat true] (x.concat false) (by simp)
        have turn : x.concat false ^^^ (0 : BitVec m).concat true = x.concat true := by
          rw [BitVec.concat_xor_concat]; simp
        rw [parity_cons, turn] at impossible
        simp only [cubeParity, cube, total, Bool.xor_false] at impossible
        change (left x ^^ right x) = false at impossible
        rw [value] at impossible
        contradiction
      | succ r =>
        have posD := weight_positive (fun a => left a ^^ right a) x value
        have bound := ih _ posD (difference_degree f h)
        have cost := weight_xor_le left right
        simpa only [Nat.succ_sub_succ, split] using Nat.le_trans bound cost

/-- Counts failures including d=0. Every homogeneous law fails there. -/
theorem failures_including_zero {p : BitVec m → BitVec m → Bool} {g} (law : Homogeneous p g) :
    2^(m-3) ≤ weight (fun d => !(g d)) := by
  apply minimum_weight
  · exact weight_positive _ 0 (by rw [law_zero law]; rfl)
  · exact degree_not (homogeneous_degree law)

/-- The lower bound is sharp. Start with the 3-bit identity, then add bits
    ignored by both the phase and the direction function. -/
theorem failures_attained (extra : Nat) :
    ∃ (p : BitVec (3+extra) → BitVec (3+extra) → Bool) (g : BitVec (3+extra) → Bool),
      Homogeneous p g ∧ weight (fun d => !(g d)) = 2^extra := by
  induction extra with
  | zero =>
    refine ⟨EightSquare.phase, fun d => decide (d ≠ 0), ?_, ?_⟩
    · intro x y d
      revert x y d
      decide
    · decide
  | succ k ih =>
    obtain ⟨p,g,law,wt⟩ := ih
    let drop (x : BitVec (3+k+1)) := x.extractLsb' 1 (3+k)
    have linear (x y) : drop (x ^^^ y) = drop x ^^^ drop y := BitVec.extractLsb'_xor
    have leftInv (x : BitVec (3+k)) (b : Bool) : drop (x.concat b) = x :=
      BitVec.extractLsb'_append_eq_left
    refine ⟨fun x y => p (drop x) (drop y), fun d => g (drop d), ?_, ?_⟩
    · intro x y d
      simpa only [square, linear] using law (drop x) (drop y) (drop d)
    · change weight (fun d => !(g (drop (d.concat false)))) +
          weight (fun d => !(g (drop (d.concat true)))) = _
      simp only [leftInv, wt, Nat.pow_succ]
      omega

end Mobius.DirectionLaws
