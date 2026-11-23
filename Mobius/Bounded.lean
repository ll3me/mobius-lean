import Std

/-!
# A seam that really must remember its history

A summary of a proof-search context may be reused for a continuation if all
accepted/rejected continuations remain correct. For the prefixes below, different
histories admit different continuations. This is the right-congruence argument
behind Myhill–Nerode and the deterministic one-way lower bound for equality.

All clauses have exactly three distinct variables. The model consumes a clause
stream from left to right. Its state includes *all* information passed across
the cut. No claim about random-access decision time follows from its state bound.
-/

namespace Mobius.Bounded

inductive Var (n : Nat) where
  | data (index : Fin n)
  | auxA
  | auxB
  deriving DecidableEq

structure Literal (n : Nat) where
  var : Var n
  sign : Bool
  deriving DecidableEq

structure Clause (n : Nat) where
  left : Literal n
  middle : Literal n
  right : Literal n
  deriving DecidableEq

abbrev Formula (n : Nat) := List (Clause n)
abbrev Assignment (n : Nat) := Var n → Bool

def Clause.Holds (c : Clause n) (a : Assignment n) : Prop :=
  a c.left.var = c.left.sign ∨ a c.middle.var = c.middle.sign ∨
  a c.right.var = c.right.sign

def Satisfies (a : Assignment n) (f : Formula n) : Prop :=
  ∀ c ∈ f, c.Holds a

def Satisfiable (f : Formula n) : Prop := ∃ a, Satisfies a f

def Clause.DistinctVars (c : Clause n) : Prop :=
  c.left.var ≠ c.middle.var ∧ c.left.var ≠ c.right.var ∧
    c.middle.var ≠ c.right.var

/-- The four auxiliary sign choices exclude exactly the assignments with
    the wrong data bit. The same two auxiliary variables can be reused. -/
def pinClause (i : Fin n) (bit u v : Bool) : Clause n :=
  ⟨⟨.data i, bit⟩, ⟨.auxA, u⟩, ⟨.auxB, v⟩⟩

def pin (i : Fin n) (bit : Bool) : Formula n :=
  [pinClause i bit false false, pinClause i bit false true,
   pinClause i bit true false, pinClause i bit true true]

private theorem pin_correct (a : Assignment n) (i : Fin n) (bit : Bool) :
    Satisfies a (pin i bit) ↔ a (.data i) = bit := by
  cases hu : a .auxA <;> cases hv : a .auxB <;>
    simp [Satisfies, pin, pinClause, Clause.Holds, hu, hv]

def block (x : BitVec n) : Formula n :=
  (List.ofFn fun i : Fin n => pin i (x.getLsbD i.val)).flatten

theorem block_correct (a : Assignment n) (x : BitVec n) :
    Satisfies a (block x) ↔ ∀ i : Fin n, a (.data i) = x.getLsbD i.val := by
  constructor
  · intro h i
    apply (pin_correct a i _).mp
    intro c hc
    apply h c
    exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hc⟩
  · intro h c hc
    obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hcs
    exact (pin_correct a i _).mpr (h i) c hc

theorem block_distinct (x : BitVec n) (c : Clause n) (hc : c ∈ block x) :
    c.DistinctVars := by
  obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hcs
  simp only [pin, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Clause.DistinctVars, pinClause]

/-- There are four clauses for each bit of the left or right context. -/
theorem block_length (x : BitVec n) : (block x).length = 4 * n := by
  have general (k : Nat) (f : Fin k → Formula n) (h : ∀ i, (f i).length = 4) :
      (List.ofFn f).flatten.length = 4 * k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons, List.length_append, h]
      have tail := ih (fun i => f i.succ) (fun i => h i.succ)
      omega
  apply general
  intro i
  rfl

private def assignmentOf (x : BitVec n) : Assignment n
  | .data i => x.getLsbD i.val
  | .auxA | .auxB => false

/-- An actual exact-width 3-CNF encoding of the two-party equality relation. -/
theorem sat_append_iff_eq (x y : BitVec n) :
    Satisfiable (block x ++ block y) ↔ x = y := by
  constructor
  · rintro ⟨a, ha⟩
    have hx : Satisfies a (block x) := fun c hc => ha c (List.mem_append_left _ hc)
    have hy : Satisfies a (block y) := fun c hc => ha c (List.mem_append_right _ hc)
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    exact ((block_correct a x).mp hx ⟨i, hi⟩).symm.trans
      ((block_correct a y).mp hy ⟨i, hi⟩)
  · rintro rfl
    have hx := (block_correct (assignmentOf x) x).mpr (fun _ => rfl)
    refine ⟨assignmentOf x, fun c hc => ?_⟩
    exact hx c ((List.mem_append.mp hc).elim id id)

/-- A continuation can inspect its private suffix arbitrarily. Even with this
    additional freedom, the state at the seam separates every pair of prefixes. -/
theorem seam_injective {State : Type} (send : BitVec n → State)
    (finish : State → BitVec n → Bool)
    (correct : ∀ x y, finish (send x) y = true ↔ Satisfiable (block x ++ block y)) :
    ∀ x y, send x = send y → x = y := by
  intro x y h
  have accepted := (correct y y).mpr ((sat_append_iff_eq y y).mpr rfl)
  rw [← h] at accepted
  exact (sat_append_iff_eq x y).mp ((correct x y).mp accepted)

/-- The matching upper bound for the equality *subfamily* at this cut. -/
theorem echo_summary_correct (x y : BitVec n) :
    decide (x = y) = true ↔ Satisfiable (block x ++ block y) := by
  simp [sat_append_iff_eq]

/-- Read the data bit from the false/false auxiliary-sign clause in each pin. -/
def readPins (f : Formula n) : List Bool :=
  (f.filter fun c => !c.middle.sign && !c.right.sign).map fun c => c.left.sign

private theorem readPins_append (a b : Formula n) :
    readPins (a ++ b) = readPins a ++ readPins b := by
  simp [readPins]

private theorem readPins_pin (i : Fin n) (bit : Bool) :
    readPins (pin i bit) = [bit] := rfl

theorem readPins_block (x : BitVec n) :
    readPins (block x) = List.ofFn (fun i : Fin n => x.getLsbD i.val) := by
  have general (k : Nat) (f : Fin k → Fin n) :
      readPins (List.ofFn (fun i => pin (f i) (x.getLsbD (f i).val))).flatten =
        List.ofFn (fun i => x.getLsbD (f i).val) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.ofFn_succ, List.flatten_cons, readPins_append, readPins_pin,
        List.singleton_append]
      rw [ih (fun i => f i.succ)]
  exact general n id

/-- A linear number of list operations decides the gadget *on its promise*.
    The input really is the clause list. Off the promise no SAT claim is made. -/
def pairedChecker (f : Formula n) : Bool :=
  let bits := readPins f
  decide (bits.take n = bits.drop n)

theorem pairedChecker_correct (x y : BitVec n) :
    pairedChecker (block x ++ block y) = true ↔ Satisfiable (block x ++ block y) := by
  rw [sat_append_iff_eq]
  unfold pairedChecker
  rw [readPins_append, readPins_block, readPins_block]
  let xs := List.ofFn (fun i : Fin n => x.getLsbD i.val)
  let ys := List.ofFn (fun i : Fin n => y.getLsbD i.val)
  change decide ((xs ++ ys).take n = (xs ++ ys).drop n) = true ↔ x = y
  have size : xs.length = n := List.length_ofFn
  have take : (xs ++ ys).take n = xs := by rw [← size, List.take_left]
  have drop : (xs ++ ys).drop n = ys := by rw [← size, List.drop_left]
  rw [take, drop, decide_eq_true_eq]
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    have bits := congrArg (fun l : List Bool => l[i]?) h
    simpa [xs, ys, List.getElem?_ofFn, hi] using bits
  · rintro rfl
    rfl

private def closeGap (r x : Nat) : Nat := if x < r then x else x - 1

private theorem closeGap_lt {r x n : Nat} (hr : r < n + 1) (hx : x < n + 1)
    (h : x ≠ r) : closeGap r x < n := by
  unfold closeGap
  split <;> omega

private theorem closeGap_inj {r x y : Nat} (hx : x ≠ r) (hy : y ≠ r)
    (h : closeGap r x = closeGap r y) : x = y := by
  by_cases a : x < r <;> by_cases b : y < r <;>
    simp [closeGap, a, b] at h <;> omega

/-- Finite pigeonhole principle by removing the image of the last argument. -/
theorem fin_size_le {a b : Nat} (f : Fin a → Fin b)
    (inj : ∀ i j, f i = f j → i = j) : a ≤ b := by
  induction b generalizing a with
  | zero =>
    cases a with
    | zero => exact Nat.le_refl _
    | succ a => exact (Fin.elim0 (f 0))
  | succ b ih =>
    cases a with
    | zero => exact Nat.zero_le _
    | succ a =>
      let last := f (Fin.last a)
      have ne (i : Fin a) : (f i.castSucc).val ≠ last.val := by
        intro eq
        have h := inj i.castSucc (Fin.last a) (Fin.ext eq)
        have valEq := congrArg Fin.val h
        have lt := i.isLt
        change i.val = a at valEq
        omega
      let g (i : Fin a) : Fin b :=
        ⟨closeGap last.val (f i.castSucc).val, closeGap_lt last.isLt (f i.castSucc).isLt (ne i)⟩
      have ginj : ∀ i j, g i = g j → i = j := by
        intro i j e
        have same := closeGap_inj (ne i) (ne j) (congrArg Fin.val e)
        exact Fin.ext (congrArg (fun t : Fin (a + 1) => t.val) (inj i.castSucc j.castSucc (Fin.ext same)))
      exact Nat.succ_le_succ (ih g ginj)

theorem state_lower_bound (send : BitVec n → Fin s)
    (finish : Fin s → BitVec n → Bool)
    (correct : ∀ x y, finish (send x) y = true ↔ Satisfiable (block x ++ block y)) :
    2 ^ n ≤ s := by
  apply fin_size_le (fun x => send (BitVec.ofFin x))
  intro i j e
  exact congrArg BitVec.toFin (seam_injective send finish correct _ _ e)

/-- A formal proof interface: a left subproof and a right subproof can be
    joined when their boundary labels agree after transport across the seam.
    Each local judgment can itself quantify over witnesses or proof terms. -/
structure CutInterface (n : Nat) (Label : Type) where
  left : BitVec n → Label → Prop
  right : Label → BitVec n → Prop
  transport : Label → Label

def CutInterface.Derives (cut : CutInterface n Label) (x y : BitVec n) : Prop :=
  ∃ label, cut.left x label ∧ cut.right (cut.transport label) y

/-- The twist is on the inference rule joining two subproofs. Neither
    determinism nor a bound on the cost of the individual subproofs is needed.
    A shared boundary label would let two valid diagonal proofs be spliced
    into a derivation that the 3-CNF semantics rules out. -/
theorem proof_cut_lower_bound (cut : CutInterface n (Fin s))
    (sound : ∀ x y, cut.Derives x y → Satisfiable (block x ++ block y))
    (complete : ∀ x, cut.Derives x x) : 2 ^ n ≤ s := by
  classical
  let label (x : BitVec n) := Classical.choose (complete x)
  have spec (x : BitVec n) :
      cut.left x (label x) ∧ cut.right (cut.transport (label x)) x :=
    Classical.choose_spec (complete x)
  have inj (x y : BitVec n) (h : label x = label y) : x = y := by
    have sewn : cut.Derives x y := ⟨label x, (spec x).1, h ▸ (spec y).2⟩
    exact (sat_append_iff_eq x y).mp (sound x y sewn)
  apply fin_size_le (fun i : Fin (2 ^ n) => label (.ofFin i))
  intro i j h
  exact congrArg BitVec.toFin (inj _ _ h)

/-- A specified reversible turn can be incorporated in the right subproof.
    It can be genuinely nontrivial (e.g. bitwise complement for n > 0). -/
def reversibleCut (turn : BitVec n → BitVec n) : CutInterface n (BitVec n) where
  left x label := x = label
  right label y := turn label = y
  transport := turn

theorem reversibleCut_correct (turn : BitVec n → BitVec n)
    (involution : ∀ x, turn (turn x) = x) (x y : BitVec n) :
    (reversibleCut turn).Derives x y ↔ Satisfiable (block x ++ block y) := by
  rw [sat_append_iff_eq]
  constructor
  · rintro ⟨label, rfl, h⟩
    simpa only [reversibleCut, involution] using h
  · rintro rfl
    exact ⟨x, rfl, involution x⟩

theorem complementCut_correct (x y : BitVec n) :
    (reversibleCut (fun w => ~~~w)).Derives x y ↔ Satisfiable (block x ++ block y) :=
  reversibleCut_correct _ (by intro w; simp) x y

/-- The state at the midpoint in a one-pass clause fold is a one-way message.
    Correctness is required only on this explicit subfamily. -/
theorem one_pass_lower_bound (initial : Fin s) (step : Fin s → Clause n → Fin s)
    (accept : Fin s → Bool)
    (correct : ∀ x y : BitVec n,
      accept ((block x ++ block y).foldl step initial) = true ↔
        Satisfiable (block x ++ block y)) : 2 ^ n ≤ s := by
  apply state_lower_bound (fun x => (block x).foldl step initial)
    (fun state y => accept ((block y).foldl step state))
  intro x y
  simpa only [List.foldl_append] using correct x y

/-- An interactive proof interface. At each crossing one side consults its
    own private context and sends a b-bit message. The next rule may depend
    on the entire preceding conversation. At a leaf the right side answers. -/
inductive Protocol (n b : Nat) : Nat → Type where
  | done (answer : BitVec n → Bool) : Protocol n b 0
  | left (write : BitVec n → BitVec b)
      (next : BitVec b → Protocol n b k) : Protocol n b (k + 1)
  | right (write : BitVec n → BitVec b)
      (next : BitVec b → Protocol n b k) : Protocol n b (k + 1)

def Protocol.run (p : Protocol n b k) (x y : BitVec n) : Bool :=
  match p with
  | .done answer => answer y
  | .left write next => (next (write x)).run x y
  | .right write next => (next (write y)).run x y

def Protocol.transcript (p : Protocol n b k) (x y : BitVec n) : BitVec (b * k) :=
  match p with
  | .done _ => 0#0
  | .left write next => (next (write x)).transcript x y ++ write x
  | .right write next => (next (write y)).transcript x y ++ write y

private theorem append_parts {hi hi' : BitVec u} {lo lo' : BitVec v}
    (h : hi ++ lo = hi' ++ lo') : hi = hi' ∧ lo = lo' := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun t : BitVec (u + v) => t.extractLsb' v u) h
  · simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun t : BitVec (u + v) => t.extractLsb' 0 v) h

/-- Transport across a common interface transcript is legitimate: the left
    context can come from the first run and the right context from the second. -/
theorem transcript_mix (p : Protocol n b k) (x y x' y' : BitVec n)
    (same : p.transcript x y = p.transcript x' y') :
    p.run x y' = p.run x' y' := by
  induction p with
  | done answer => rfl
  | left write next ih =>
    simp only [Protocol.transcript] at same
    obtain ⟨tail, head⟩ := append_parts same
    simp only [Protocol.run]
    rw [← head] at tail ⊢
    exact ih _ tail
  | right write next ih =>
    simp only [Protocol.transcript] at same
    obtain ⟨tail, head⟩ := append_parts same
    simp only [Protocol.run]
    rw [head] at tail
    exact ih _ tail

/-- k crossings carrying b bits each have a total capacity of bk bits.
    The lower bound holds even with arbitrary private computation on both sides. -/
theorem interaction_lower_bound (p : Protocol n b k)
    (correct : ∀ x y, p.run x y = true ↔ Satisfiable (block x ++ block y)) :
    n ≤ b * k := by
  have diag_inj (x y : BitVec n) (h : p.transcript x x = p.transcript y y) : x = y := by
    have cross := transcript_mix p x x y y h
    have ok := (correct y y).mpr ((sat_append_iff_eq y y).mpr rfl)
    exact (sat_append_iff_eq x y).mp ((correct x y).mp (cross.trans ok))
  have cap : 2 ^ n ≤ 2 ^ (b * k) := by
    apply fin_size_le (fun i : Fin (2 ^ n) =>
      (p.transcript (BitVec.ofFin i) (BitVec.ofFin i)).toFin)
    intro i j e
    have h := diag_inj (.ofFin i) (.ofFin j) (congrArg BitVec.ofFin e)
    exact congrArg BitVec.toFin h
  exact Nat.le_of_not_lt (fun bad => Nat.not_lt_of_ge cap
    (Nat.pow_lt_pow_right (by decide : 1 < 2) bad))

/-- A stream processor scans the same ordered clause list repeatedly.
    The only data surviving between steps is its state. -/
def scanPasses (step : σ → Clause n → σ) (f : Formula n) : Nat → σ → σ
  | 0, state => state
  | p + 1, state => scanPasses step f p (f.foldl step state)

private def crossings : Nat → Nat
  | 0 => 1
  | r + 1 => crossings r + 1 + 1

private def streamProtocol (step : BitVec b → Clause n → BitVec b)
    (accept : BitVec b → Bool) :
    (extra : Nat) → BitVec b → Protocol n b (crossings extra)
  | 0, state =>
      .left (fun x => (block x).foldl step state)
        (fun msg => .done fun y => accept ((block y).foldl step msg))
  | r + 1, state =>
      .left (fun x => (block x).foldl step state) (fun fromLeft =>
        .right (fun y => (block y).foldl step fromLeft)
          (fun fromRight => streamProtocol step accept r fromRight))

private theorem run_streamProtocol (step : BitVec b → Clause n → BitVec b)
    (accept : BitVec b → Bool) (x y : BitVec n) (r : Nat) (state : BitVec b) :
    (streamProtocol step accept r state).run x y =
      accept (scanPasses step (block x ++ block y) (r + 1) state) := by
  induction r generalizing state with
  | zero => simp [streamProtocol, Protocol.run, scanPasses]
  | succ r ih =>
    simp only [streamProtocol, Protocol.run]
    rw [ih]
    rw [← List.foldl_append]
    rfl

/-- With r+1 full passes there are 2r+1 crossings between the holders of
    the two halves. For b bits of working state, the product is at least n. -/
theorem multipass_lower_bound (step : BitVec b → Clause n → BitVec b)
    (accept : BitVec b → Bool) (initial : BitVec b) (r : Nat)
    (correct : ∀ x y : BitVec n,
      accept (scanPasses step (block x ++ block y) (r + 1) initial) = true ↔
        Satisfiable (block x ++ block y)) : n ≤ b * (2 * r + 1) := by
  have bound := interaction_lower_bound (streamProtocol step accept r initial)
    (fun x y => (run_streamProtocol step accept x y r initial) ▸ correct x y)
  have count (k : Nat) : crossings k = 2 * k + 1 := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [crossings, ih]; omega
  simpa only [count] using bound

end Mobius.Bounded
