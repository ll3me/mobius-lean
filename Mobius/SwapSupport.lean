import Mobius.Transport
import Mobius.ParityWindow

/-!
# Rational pair-swap group algebra

The basis is the Boolean cube with multiplication given by XOR. A one-bit
mask swaps one pair of wires. Rational terms are kept in sparse, uncollected
lists; `coefficient` sums every contribution to a specified basis mask,
including cancellations. `partial_swaps` gives the operator support bound in
the paper's equation `overview-partial-swaps`. The logical argument is
independent of any matrix dimension or asymptotic rank claim.
-/
namespace Mobius.SwapSupport

open Mobius.Transport.Independent (signature)

structure Term (q : Nat) where
  coefficient : Rat
  swaps : List (Fin q)
deriving DecidableEq

/-- The two terms in (I−Πᵢ)/2 times one monomial. -/
def contribution (i : Fin q) (t : Term q) : List (Term q) :=
  [⟨t.coefficient / 2, t.swaps⟩, ⟨-(t.coefficient / 2), i :: t.swaps⟩]

def weightTimes (indices : List (Fin q)) (terms : List (Term q)) : List (Term q) :=
  indices.flatMap fun i => terms.flatMap (contribution i)

/-- Horner expansion of f(W₀) in ascending coefficient order. -/
def atWeight (q : Nat) : List Rat → List (Term q)
  | [] => []
  | c :: cs => ⟨c, []⟩ :: weightTimes (List.finRange q) (atWeight q cs)

abbrev BasisTerm (q : Nat) := Rat × BitVec q

/-- Left multiplication by the complete swap V₀ complements the raw mask. -/
def repaired (q : Nat) (cs : List Rat) : List (BasisTerm q) :=
  (atWeight q cs).map fun t => (t.coefficient, BitVec.allOnes q ^^^ signature t.swaps)

def coefficient (m : BitVec q) : List (BasisTerm q) → Rat
  | [] => 0
  | (a, v) :: rest => (if m = v then a else 0) + coefficient m rest

private theorem coefficient_witness (m : BitVec q) (terms : List (BasisTerm q))
    (h : coefficient m terms ≠ 0) : ∃ a, (a,m) ∈ terms := by
  induction terms with
  | nil => exact False.elim (h rfl)
  | cons t rest ih =>
    obtain ⟨a,v⟩ := t
    by_cases hv : m = v
    · exact ⟨a, by simp [hv]⟩
    · have nonzero : coefficient m rest ≠ 0 := by simpa [coefficient, hv, Rat.zero_add] using h
      obtain ⟨b,hb⟩ := ih nonzero
      exact ⟨b, List.mem_cons_of_mem _ hb⟩

private theorem degree_bound (cs : List Rat) (t : Term q) (h : t ∈ atWeight q cs) :
    t.swaps.length < cs.length := by
  induction cs generalizing t with
  | nil => simp [atWeight] at h
  | cons c cs ih =>
    simp only [atWeight, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨i, _, old, ho, ht⟩ := by
        simpa only [weightTimes, List.mem_flatMap] using h
      have bound := ih old ho
      simp only [contribution, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp <;> omega

/-- Cancel repeat occurrences instead of counting every occurrence as an
exceptional wire. The result lists each actually undone swap exactly once. -/
def exceptions : List (Fin q) → List (Fin q)
  | [] => []
  | i :: rest =>
    let tail := exceptions rest
    if i ∈ tail then tail.erase i else i :: tail

theorem exceptions_nodup (w : List (Fin q)) : (exceptions w).Nodup := by
  induction w with
  | nil => simp [exceptions]
  | cons i rest ih =>
    simp only [exceptions]
    split
    · exact List.Nodup.erase i ih
    · next h => exact List.nodup_cons.mpr ⟨h,ih⟩

theorem exceptions_length (w : List (Fin q)) : (exceptions w).length ≤ w.length := by
  induction w with
  | nil => exact Nat.le_refl _
  | cons i rest ih =>
    simp only [exceptions, List.length_cons]
    split
    · exact Nat.le_trans List.length_erase_le (Nat.le_trans ih (by omega))
    · simpa using ih

theorem exception_bit (w : List (Fin q)) (j : Fin q) :
    (signature w).getLsbD j.val = decide (j ∈ exceptions w) := by
  induction w with
  | nil => simp [signature, exceptions]
  | cons i rest ih =>
    simp only [signature, BitVec.getLsbD_xor, BitVec.getLsbD_twoPow, ih, exceptions]
    have nd := exceptions_nodup rest
    by_cases same : i=j
    · subst i
      by_cases hit : j ∈ exceptions rest <;> simp [j.isLt, hit, nd.not_mem_erase]
    · have vals : i.val ≠ j.val := fun e => same (Fin.ext e)
      by_cases hit : i ∈ exceptions rest <;>
        simp [vals, hit, List.mem_erase_of_ne (Ne.symm same), Ne.symm same]

/-- Nonzero coefficient in V₀f(W₀) implies a swap of every pair outside a
set of at most degree(f) exceptional indices. The formula also handles the
empty coefficient list (zero operator). -/
theorem partial_swaps (cs : List Rat) (mask : BitVec q)
    (supported : coefficient mask (repaired q cs) ≠ 0) :
    ∃ skip : List (Fin q), skip.Nodup ∧ skip.length ≤ cs.length-1 ∧
      ∀ i : Fin q, mask.getLsbD i.val = !(decide (i ∈ skip)) := by
  obtain ⟨a, ha⟩ := coefficient_witness _ _ supported
  obtain ⟨t, active, eqn⟩ := List.mem_map.mp ha
  have hm : BitVec.allOnes q ^^^ signature t.swaps = mask := congrArg Prod.snd eqn
  obtain lengthBound := degree_bound cs t active
  refine ⟨exceptions t.swaps, exceptions_nodup _, ?_, ?_⟩
  · have h := exceptions_length t.swaps
    omega
  · intro i
    rw [← hm, BitVec.allOnes_xor, BitVec.getLsbD_not, exception_bit]
    simp [i.isLt]

/-! A sign assignment encodes one common eigenspace: an index marked true
has eigenvalue −1 for that pair swap. The formulas below evaluate a formal
sum on this character without constructing dense matrices. -/

def eigenWord (minus : Fin q → Bool) : List (Fin q) → Rat
  | [] => 1
  | i :: rest => (if minus i then -1 else 1) * eigenWord minus rest

def eigenSum (minus : Fin q → Bool) : List (Term q) → Rat
  | [] => 0
  | t :: rest => t.coefficient * eigenWord minus t.swaps + eigenSum minus rest

private theorem eigen_append (minus : Fin q → Bool) (a b : List (Term q)) :
    eigenSum minus (a++b) = eigenSum minus a + eigenSum minus b := by
  induction a with
  | nil => simp [eigenSum, Rat.zero_add]
  | cons t a ih => simp [eigenSum, ih, Rat.add_assoc]

private theorem eigen_one_pair (minus : Fin q → Bool) (i : Fin q) (terms : List (Term q)) :
    eigenSum minus (terms.flatMap (contribution i)) =
      (if minus i then 1 else 0) * eigenSum minus terms := by
  induction terms with
  | nil => simp [eigenSum]
  | cons t rest ih =>
    simp only [List.flatMap_cons, eigen_append, contribution, eigenSum, eigenWord, ih]
    cases minus i <;> simp <;> grind

theorem eigen_weightTimes (minus : Fin q → Bool) (indices : List (Fin q)) (terms : List (Term q)) :
    eigenSum minus (weightTimes indices terms) = (indices.countP minus : Rat) * eigenSum minus terms := by
  induction indices with
  | nil => simp [weightTimes, eigenSum]
  | cons i rest ih =>
    change eigenSum minus (terms.flatMap (contribution i) ++ weightTimes rest terms) = _
    rw [eigen_append, eigen_one_pair, ih, List.countP_cons]
    cases minus i <;> simp <;> grind

def horner (j : Rat) : List Rat → Rat
  | [] => 0
  | c :: cs => c + j * horner j cs

def minusCount (minus : Fin q → Bool) : Nat := (List.finRange q).countP minus

theorem eigen_atWeight (minus : Fin q → Bool) (cs : List Rat) :
    eigenSum minus (atWeight q cs) = horner (minusCount minus : Rat) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [atWeight, eigenSum, eigenWord, eigen_weightTimes, horner, ih, minusCount]

theorem eigenWord_parity (minus : Fin q → Bool) (w : List (Fin q)) :
    eigenWord minus w = (ParityWindow.parity (w.countP minus) : Rat) := by
  induction w with
  | nil => rfl
  | cons i rest ih =>
    simp only [eigenWord, List.countP_cons, ih]
    cases minus i <;> simp [ParityWindow.parity, Rat.intCast_neg] <;> grind

/-- Evaluation on a common eigenvector is a character of the Boolean mask
group. Each true entry of `minus` supplies eigenvalue −1. -/
def sign (b : Bool) : Rat := if b then -1 else 1

private theorem sign_xor (a b : Bool) : sign (Bool.xor a b) = sign a * sign b := by
  cases a <;> cases b <;> decide +kernel

def characterOn (minus : Fin q → Bool) (mask : BitVec q) : List (Fin q) → Rat
  | [] => 1
  | i :: rest => sign (minus i && mask.getLsbD i.val) * characterOn minus mask rest

private theorem character_xor (minus : Fin q → Bool) (a b : BitVec q) (ids : List (Fin q)) :
    characterOn minus (a ^^^ b) ids = characterOn minus a ids * characterOn minus b ids := by
  induction ids with
  | nil => simp [characterOn]
  | cons i rest ih =>
    simp only [characterOn, BitVec.getLsbD_xor, ih]
    have hx : (minus i && Bool.xor (a.getLsbD i.val) (b.getLsbD i.val)) =
        Bool.xor (minus i && a.getLsbD i.val) (minus i && b.getLsbD i.val) := by
      cases minus i <;> simp
    rw [hx, sign_xor]
    grind

private theorem character_zero (minus : Fin q → Bool) (ids : List (Fin q)) :
    characterOn minus 0 ids = 1 := by
  induction ids with
  | nil => rfl
  | cons i rest ih => rw [characterOn, ih]; simp [sign]

private theorem character_single (minus : Fin q → Bool) (i : Fin q)
    (ids : List (Fin q)) (nd : ids.Nodup) :
    characterOn minus (BitVec.twoPow q i.val) ids =
      if i ∈ ids then sign (minus i) else 1 := by
  induction ids with
  | nil => simp [characterOn]
  | cons j rest ih =>
    obtain ⟨fresh, nd'⟩ := List.nodup_cons.mp nd
    simp only [characterOn, BitVec.getLsbD_twoPow, ih nd']
    by_cases same : i=j
    · subst j; simp [i.isLt, fresh]
    · have vn : i.val ≠ j.val := fun e => same (Fin.ext e)
      simp [vn, same, sign]

private theorem character_signature (minus : Fin q → Bool) (w : List (Fin q)) :
    characterOn minus (signature w) (List.finRange q) = eigenWord minus w := by
  induction w with
  | nil => exact character_zero _ _
  | cons i rest ih =>
    rw [signature, character_xor, character_single _ _ _ (List.nodup_finRange q), ih]
    simp [eigenWord, sign]

private theorem character_full (minus : Fin q → Bool) (ids : List (Fin q)) :
    characterOn minus (BitVec.allOnes q) ids = eigenWord minus ids := by
  induction ids with
  | nil => rfl
  | cons i rest ih =>
    simp only [characterOn, eigenWord, BitVec.getLsbD_allOnes, i.isLt, decide_true,
      Bool.and_true, ih, sign]

def evaluateBasis (minus : Fin q → Bool) : List (BasisTerm q) → Rat
  | [] => 0
  | (c,mask) :: rest => c * characterOn minus mask (List.finRange q) + evaluateBasis minus rest

/-- Character of the same collected-mask operator for which we proved the
support bound. The full swap contributes parity; W₀ contributes the weight. -/
theorem eigen_repaired (minus : Fin q → Bool) (cs : List Rat) :
    evaluateBasis minus (repaired q cs) =
    (ParityWindow.parity (minusCount minus) : Rat) * horner (minusCount minus : Rat) cs := by
  have fold (rows : List (Term q)) :
      evaluateBasis minus (rows.map fun t =>
        (t.coefficient, BitVec.allOnes q ^^^ signature t.swaps)) =
        eigenWord minus (List.finRange q) * eigenSum minus rows := by
    induction rows with
    | nil => simp [evaluateBasis, eigenSum]
    | cons t rows ih =>
      simp only [List.map_cons, evaluateBasis, eigenSum, ih, character_xor,
        character_full, character_signature]
      grind
  rw [repaired, fold, eigen_atWeight, eigenWord_parity]
  rfl

/-! Construct rational coefficients for a repair, and use one coefficient list
for both the support and the spectral conclusions. The construction adds
one vanishing-product correction at each new weight. -/

private def plus : List Rat → List Rat → List Rat
  | [], b => b
  | a, [] => a
  | x::a, y::b => (x+y) :: plus a b

private theorem horner_plus (x : Rat) (a b : List Rat) :
    horner x (plus a b) = horner x a + horner x b := by
  induction a generalizing b with
  | nil => simp [plus, horner, Rat.zero_add]
  | cons y a ih =>
    cases b with
    | nil => simp [plus, horner, Rat.add_zero]
    | cons z b => simp only [plus, horner, ih]; grind

private theorem plus_len (a b : List Rat) :
    (plus a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [plus]
  | cons y a ih =>
    cases b with
    | nil => simp [plus]
    | cons z b => simp [plus, ih]

private theorem horner_scale (x k : Rat) (a : List Rat) :
    horner x (a.map (k*·)) = k * horner x a := by
  induction a with
  | nil => simp [horner]
  | cons y a ih => simp only [List.map_cons, horner, ih]; grind

private def roots (start : Nat) : Nat → List Rat
  | 0 => [1]
  | width+1 =>
    let prev := roots start width
    plus (0::prev) (prev.map (-(↑(start+width) : Rat)*·))

private theorem roots_len (a w : Nat) : (roots a w).length = w+1 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [roots, plus_len, ih]

private theorem roots_step (a w : Nat) (x : Rat) :
    horner x (roots a (w+1)) = (x-(↑(a+w) : Rat)) * horner x (roots a w) := by
  rw [roots, horner_plus, horner_scale, horner]
  grind

private theorem roots_zero (a w j : Nat) (inside : j<w) :
    horner (↑(a+j) : Rat) (roots a w) = 0 := by
  induction w with
  | zero => omega
  | succ w ih =>
    rw [roots_step]
    by_cases same : w=j
    · subst j; grind
    · rw [ih (by omega)]; grind

private theorem roots_nonzero (a w j : Nat) (after : w ≤ j) :
    horner (↑(a+j) : Rat) (roots a w) ≠ 0 := by
  induction w with
  | zero => simp [roots, horner, Rat.add_zero]
  | succ w ih =>
    rw [roots_step]
    have ne : (↑(a+j) : Rat) ≠ (↑(a+w) : Rat) := fun h => by
      have := Rat.natCast_inj.mp h; omega
    have nonzero := ih (show w ≤ j by omega)
    grind

/-- Add one interpolation node using a correction vanishing at all older
nodes. Exposing the construction avoids any polynomial-existence axiom. -/
def interpolate (start : Nat) (value : Nat → Rat) : Nat → List Rat
  | 0 => []
  | w+1 =>
    let previous := interpolate start value w
    let x : Rat := ↑(start+w)
    let k := (value (start+w) - horner x previous) / horner x (roots start w)
    plus previous ((roots start w).map (k*·))

theorem interpolate_length (a : Nat) (f : Nat → Rat) (w : Nat) :
    (interpolate a f w).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [interpolate, plus_len, roots_len, ih]

theorem interpolate_matches (a : Nat) (f : Nat → Rat) (w j : Nat) (hj : j<w) :
    horner (↑(a+j) : Rat) (interpolate a f w) = f (a+j) := by
  induction w with
  | zero => omega
  | succ w ih =>
    rw [interpolate, horner_plus, horner_scale]
    by_cases atEnd : j=w
    · subst j
      rw [Rat.div_mul_cancel (roots_nonzero a w w (by omega))]
      grind
    · rw [roots_zero a w j (by omega), ih (by omega)]
      grind

/-- For every window, the *same explicit operator* fixes all its characters,
while every supported basis mask leaves at most width−1 pairs unswapped. -/
theorem support_and_window (q a w : Nat) :
    ∃ cs : List Rat, cs.length = w ∧
      (∀ mask : BitVec q, coefficient mask (repaired q cs) ≠ 0 →
        ∃ skip : List (Fin q), skip.Nodup ∧ skip.length ≤ w-1 ∧
          ∀ i : Fin q, mask.getLsbD i.val = !(decide (i ∈ skip))) ∧
      (∀ minus : Fin q → Bool, a ≤ minusCount minus → minusCount minus < a+w →
        evaluateBasis minus (repaired q cs) = 1) := by
  let f := fun i : Nat => (ParityWindow.parity i : Rat)
  let cs := interpolate a f w
  have lengthOK : cs.length = w := interpolate_length a f w
  refine ⟨cs, lengthOK, ?_, ?_⟩
  · intro mask nonzero
    simpa only [← lengthOK] using partial_swaps cs mask nonzero
  · intro minus lo hi
    let j := minusCount minus - a
    have idx : minusCount minus = a+j := by dsimp [j]; omega
    have matched := interpolate_matches a f w j (by omega)
    rw [eigen_repaired, idx, matched]
    have square := congrArg (fun z : Int => (z : Rat)) (ParityWindow.parity_sq (a+j))
    simpa only [f, Rat.intCast_mul, Rat.intCast_one] using square

/-- A direct two-pair check: f(z)=1−2z gives Π₁+Π₂−Π₁Π₂. -/
example :
    coefficient (0#2) (repaired 2 [1,-2]) = 0 ∧
    coefficient (1#2) (repaired 2 [1,-2]) = 1 ∧
    coefficient (2#2) (repaired 2 [1,-2]) = 1 ∧
    coefficient (3#2) (repaired 2 [1,-2]) = -1 := by decide +kernel

end Mobius.SwapSupport
