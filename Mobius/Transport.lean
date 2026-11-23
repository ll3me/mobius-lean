import Std

/-!
# Transport of the two roles of a proof obligation

A vertex is a position in a proof template. An edge records whether its two
roles are preserved or exchanged. The labels belong to the proof graph. They
do not refer to variables of a SAT instance.

The rooted classification below has two forms. For directed inference steps
the exact obstruction is disagreement between two paths. For reversible steps,
one can turn that disagreement into a single odd closed walk.
-/

namespace Mobius.Transport

universe u w
variable {V : Type u}

abbrev SignedEdges (V : Type u) := V → V → Bool → Prop

def Orients (E : SignedEdges V) (side : V → Bool) : Prop :=
  ∀ {a b flip}, E a b flip → side b = Bool.xor (side a) flip

def Orientable (E : SignedEdges V) : Prop := ∃ side, Orients E side

inductive Walk (E : SignedEdges V) : V → V → Bool → Prop where
  | nil (v : V) : Walk E v v false
  | snoc {a b c : V} {p q : Bool} :
      Walk E a b p → E b c q → Walk E a c (Bool.xor p q)

private theorem xorAssoc (a b c : Bool) :
    Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;> decide

private theorem xorComm (a b : Bool) : Bool.xor a b = Bool.xor b a := by
  cases a <;> cases b <;> decide

private theorem xorRightFalse (b : Bool) : Bool.xor b false = b := by cases b <;> rfl
private theorem xorLeftFalse (b : Bool) : Bool.xor false b = b := by cases b <;> rfl

private theorem xorCancelLeft {b c : Bool} (a : Bool)
    (h : Bool.xor a b = Bool.xor a c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

variable {E : SignedEdges V}

theorem Walk.single {a b : V} {p : Bool} (e : E a b p) : Walk E a b p := by
  simpa only [xorLeftFalse] using Walk.snoc (Walk.nil a) e

theorem Walk.append {a b c : V} {p q : Bool}
    (left : Walk E a b p) (right : Walk E b c q) : Walk E a c (Bool.xor p q) := by
  induction right with
  | nil => simpa only [xorRightFalse] using left
  | snoc path edge ih =>
    simpa only [xorAssoc] using Walk.snoc ih edge

theorem Walk.reverse (symmetric : ∀ {a b bit}, E a b bit → E b a bit)
    {a b : V} {p : Bool} (path : Walk E a b p) : Walk E b a p := by
  induction path with
  | nil => exact .nil _
  | snoc path edge ih =>
    simpa only [xorComm] using (Walk.single (symmetric edge)).append ih

theorem Walk.transport {side : V → Bool} (orient : Orients E side)
    {a b : V} {p : Bool} (path : Walk E a b p) : side b = Bool.xor (side a) p := by
  induction path with
  | nil => exact (xorRightFalse _).symm
  | snoc path edge ih =>
    rw [orient edge, ih, xorAssoc]

theorem oddLoop_forbids_orientation {v : V} (loop : Walk E v v true) :
    ¬ Orientable E := by
  rintro ⟨side, orient⟩
  have h := Walk.transport (E := E) (side := side) (@orient) loop
  cases hSide : side v <;> simp [hSide] at h

def PathIndependent (E : SignedEdges V) (root : V) : Prop :=
  ∀ {v p q}, Walk E root v p → Walk E root v q → p = q

/-- No ability to undo inference steps is assumed. Classical choice selects
one path sign per vertex, without claiming an efficient way of computing it. -/
theorem orientable_iff_pathIndependent (root : V)
    (reaches : ∀ v, ∃ p, Walk E root v p) :
    Orientable E ↔ PathIndependent E root := by
  constructor
  · rintro ⟨side, orient⟩ v p q path other
    exact xorCancelLeft (side root) ((Walk.transport (E := E) (side := side) (@orient) path).symm.trans (Walk.transport (E := E) (side := side) (@orient) other))
  · intro independent
    let side := fun v => Classical.choose (reaches v)
    have getPath (v : V) : Walk E root v (side v) := Classical.choose_spec (reaches v)
    refine ⟨side, ?_⟩
    intro a b flip edge
    exact independent (getPath b) (.snoc (getPath a) edge)

/-- On a rooted connected reversible proof graph the obstruction is complete:
orientation fails exactly when some return to the root switches roles. -/
theorem orientable_iff_no_odd_return (root : V)
    (reaches : ∀ v, ∃ p, Walk E root v p)
    (symmetric : ∀ {a b bit}, E a b bit → E b a bit) :
    Orientable E ↔ ¬ Walk E root root true := by
  constructor
  · intro orient loop
    exact oddLoop_forbids_orientation loop orient
  · intro noLoop
    apply (orientable_iff_pathIndependent root reaches).2
    intro v p q outward other
    have loop := outward.append (Walk.reverse (E := E) (@symmetric) other)
    cases p <;> cases q <;> first | rfl | exact False.elim (noLoop loop)

/-- The lifted vertex remembers which of the two roles is currently active. -/
def Cover (E : SignedEdges V) : SignedEdges (V × Bool) := fun a b flip =>
  E a.1 b.1 flip ∧ b.2 = Bool.xor a.2 flip

theorem cover_orientable (E : SignedEdges V) : Orientable (Cover E) :=
  ⟨Prod.snd, fun edge => edge.2⟩

theorem Walk.lift {a b : V} {p : Bool} (path : Walk E a b p) (side : Bool) :
    Walk (Cover E) (a, side) (b, Bool.xor side p) p := by
  induction path with
  | nil => simpa only [xorRightFalse] using Walk.nil (E := Cover E) (_, side)
  | snoc path edge ih =>
    exact Walk.snoc ih ⟨edge, (xorAssoc _ _ _).symm⟩

theorem Walk.project {a b : V × Bool} {p : Bool} (path : Walk (Cover E) a b p) :
    Walk E a.1 b.1 p := by
  induction path with
  | nil => exact Walk.nil _
  | snoc path edge ih => exact Walk.snoc ih edge.1

theorem cover_walk_iff {a b : V} {start finish flip : Bool} :
    Walk (Cover E) (a, start) (b, finish) flip ↔
      Walk E a b flip ∧ finish = Bool.xor start flip := by
  constructor
  · intro lifted
    exact ⟨lifted.project, lifted.transport (side := Prod.snd) (fun edge => edge.2)⟩
  · rintro ⟨path, rfl⟩
    exact path.lift start

/-! Changing the local names of the two sides cannot erase the obstruction.
This is the elementary, coordinate-free content of a Boolean cocycle. -/

def retag (atSource flip atTarget : Bool) : Bool :=
  Bool.xor (Bool.xor atSource flip) atTarget

private theorem retag_same (a p : Bool) : retag a p a = p := by
  cases a <;> cases p <;> rfl

private theorem retag_join (a b c p q : Bool) :
    Bool.xor (retag a p b) (retag b q c) = retag a (Bool.xor p q) c := by
  cases a <;> cases b <;> cases c <;> cases p <;> cases q <;> rfl

def Switch (E : SignedEdges V) (gauge : V → Bool) : SignedEdges V := fun a b flip =>
  ∃ old, E a b old ∧ flip = retag (gauge a) old (gauge b)

theorem Walk.switch (gauge : V → Bool) {a b : V} {p : Bool} (path : Walk E a b p) :
    Walk (Switch E gauge) a b (retag (gauge a) p (gauge b)) := by
  induction path with
  | nil => simpa only [retag_same] using Walk.nil (E := Switch E gauge) _
  | @snoc b c p q path edge ih =>
    have edge' : Switch E gauge b c (retag (gauge b) q (gauge c)) :=
      ⟨q, edge, rfl⟩
    simpa only [retag_join] using ih.snoc edge'

theorem odd_return_after_switch (gauge : V → Bool) {v : V}
    (loop : Walk E v v true) : Walk (Switch E gauge) v v true := by
  simpa only [retag_same] using loop.switch gauge

/-- A signed graph is orientable precisely when some local renaming turns
every edge into a role-preserving edge. -/
theorem orientable_iff_trivializes :
    Orientable E ↔ ∃ gauge : V → Bool,
      ∀ {a b flip}, E a b flip → retag (gauge a) flip (gauge b) = false := by
  have cancel (x f y : Bool) : y = Bool.xor x f ↔ retag x f y = false := by
    cases x <;> cases f <;> cases y <;> decide
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, fun edge => (cancel _ _ _).1 (hg edge)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, fun edge => (cancel _ _ _).2 (hg edge)⟩

/-! Folding proof positions is a separate operation. Its exact price is
fiber constancy: a choice made upstairs must agree between *all* original
positions identified by the fold. This condition holds for some lifts but
fails for the fuel-erasure example below. -/

variable {W : Type w}

def Fold (q : V → W) (E : SignedEdges V) : SignedEdges W := fun v w bit =>
  ∃ a b, q a = v ∧ q b = w ∧ E a b bit

theorem fold_orientable_iff (q : V → W) (onto : ∀ w, ∃ a, q a = w) :
    Orientable (Fold q E) ↔ ∃ side : V → Bool, Orients E side ∧
      ∀ a b, q a = q b → side a = side b := by
  constructor
  · rintro ⟨down, hd⟩
    refine ⟨fun a => down (q a), ?_, fun _ _ h => congrArg down h⟩
    intro a b f edge
    exact hd (show Fold q E (q a) (q b) f from ⟨a, b, rfl, rfl, edge⟩)
  · rintro ⟨up, hu, agrees⟩
    let pick (w : W) := Classical.choose (onto w)
    have picks (w : W) : q (pick w) = w := Classical.choose_spec (onto w)
    refine ⟨fun w => up (pick w), ?_⟩
    rintro _ _ bit ⟨a, b, rfl, rfl, edge⟩
    exact (agrees (pick (q b)) b (picks (q b))).trans
      ((hu edge).trans (congrArg (fun s => Bool.xor s bit)
        (agrees (pick (q a)) a (picks (q a))).symm))

/-! A proof-dependency example. The node represents the operation of deriving
an equivalence of negations; its two roles are the two implications of an iff.
The concrete unfolded derivation has a finite fuel parameter. Erasing *only*
the parameter produces the loop below, even though all proofs are valid. -/

def addNegations : Nat → Prop → Prop
  | 0, a => a
  | n+1, a => ¬ addNegations n a

theorem twistedEquivalence {a b : Prop} (h : a ↔ b) :
    ∀ n, addNegations n a ↔ addNegations n b
  | 0 => h
  | n+1 =>
      let prev := twistedEquivalence h n
      ⟨mt prev.mpr, mt prev.mp⟩

def StageEdge : SignedEdges Nat := fun fromStage toStage swap =>
  fromStage = toStage + 1 ∧ swap = true

def stageSide : Nat → Bool
  | 0 => false
  | n+1 => !(stageSide n)

theorem stages_orientable : Orients StageEdge stageSide := by
  intro a b p edge
  rcases edge with ⟨rfl, rfl⟩
  change stageSide b = Bool.xor (!(stageSide b)) true
  cases stageSide b <;> rfl

/-- Existential image of the actual dependencies after forgetting their stage. -/
def FoldedEdge : SignedEdges Unit := fun _ _ flip =>
  ∃ fromStage toStage, StageEdge fromStage toStage flip

theorem folded_odd_return : Walk FoldedEdge () () true :=
  .single ⟨1, 0, rfl, rfl⟩

theorem folded_not_orientable : ¬ Orientable FoldedEdge :=
  oddLoop_forbids_orientation folded_odd_return

/-! Several proof roles may flip independently. A monitor receives the indices
of the flips and need only answer the *one-bit* question whether every role
has returned to its initial orientation. Counting its control states gives
an exponential lower bound, attained by one packed register of `m` bits.
This counts distinguishable states, not Turing-machine running time. -/

namespace Independent

/-- Parity of the flip count in each coordinate. -/
def signature {m : Nat} : List (Fin m) → BitVec m
  | [] => 0
  | i :: rest => BitVec.twoPow m i.val ^^^ signature rest

theorem signature_append {m : Nat} (firstPart suffix : List (Fin m)) :
    signature (firstPart ++ suffix) = signature firstPart ^^^ signature suffix := by
  induction firstPart with
  | nil => simp [signature]
  | cons i tail ih => simp [signature, ih, BitVec.xor_assoc]

/-- The actual streaming implementation makes one packed-XOR update per symbol. -/
def scan {m : Nat} (start : BitVec m) (steps : List (Fin m)) : BitVec m :=
  steps.foldl (fun reg i => reg ^^^ BitVec.twoPow m i.val) start

theorem scan_correct {m : Nat} (steps : List (Fin m)) (start : BitVec m) :
    scan start steps = start ^^^ signature steps := by
  induction steps generalizing start with
  | nil => simp [scan, signature]
  | cons i tail ih =>
    simpa only [scan, List.foldl_cons, signature, BitVec.xor_assoc] using
      ih (start ^^^ BitVec.twoPow m i.val)

private theorem signature_bit (steps : List (Fin m)) (unique : steps.Nodup) (j : Fin m) :
    (signature steps).getLsbD j.val = decide (j ∈ steps) := by
  induction steps with
  | nil => simp [signature]
  | cons i rest ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    simp only [signature, BitVec.getLsbD_xor, BitVec.getLsbD_twoPow, ih tail]
    by_cases eq : i = j
    · subst i
      simp [fresh]
    · have neq : i.val ≠ j.val := fun h => eq (Fin.ext h)
      simp [neq, Ne.symm eq]

/-- A short history for any prescribed combination of role flips. -/
def canonical {m : Nat} (bits : BitVec m) : List (Fin m) :=
  (List.finRange m).filter fun i => bits.getLsbD i.val

theorem canonical_short {m : Nat} (bits : BitVec m) : (canonical bits).length ≤ m := by
  simpa [canonical] using List.length_filter_le (fun i : Fin m => bits.getLsbD i.val) (List.finRange m)

theorem signature_canonical {m : Nat} (bits : BitVec m) :
    signature (canonical bits) = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin m := ⟨i, hi⟩
  have unique : (canonical bits).Nodup :=
    (List.nodup_finRange m).filter _
  have h := signature_bit (canonical bits) unique j
  simpa [canonical, j, hi] using h

/-- Distinguishing suffix argument. Two different orientation vectors cannot
share a monitor state: append the history cancelling the first vector and
only the first will then have trivial transport. -/
theorem monitor_states {m : Nat} {S : Type w} (initial : S) (next : S → Fin m → S)
    (accept : S → Bool)
    (recognizes : ∀ steps : List (Fin m),
      accept (steps.foldl next initial) = decide (signature steps = 0)) :
    ∃ code : Fin (2 ^ m) → S, ∀ i j, code i = code j → i = j := by
  let word (i : Fin (2 ^ m)) := canonical (BitVec.ofFin i)
  refine ⟨fun i => (word i).foldl next initial, ?_⟩
  intro i j same
  have eqAccept : accept ((word i ++ word i).foldl next initial) =
      accept ((word j ++ word i).foldl next initial) := by
    simp only [List.foldl_append]
    exact congrArg (fun s => accept ((word i).foldl next s)) same
  rw [recognizes, recognizes] at eqAccept
  simp only [word, signature_append, signature_canonical, BitVec.xor_self] at eqAccept
  have zero : BitVec.ofFin j ^^^ BitVec.ofFin i = 0 :=
    of_decide_eq_true (eqAccept.symm.trans (decide_eq_true rfl))
  exact (congrArg BitVec.toFin (BitVec.xor_eq_zero_iff.mp zero)).symm

end Independent

end Mobius.Transport
