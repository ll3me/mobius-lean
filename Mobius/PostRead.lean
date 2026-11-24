/-! A subcube adversary for scalar computations after all input bits are in
registers. Operations include arbitrary binary functions, data-dependent
control, indexed register reads, and unbounded conjunctions of unary tests. -/
namespace Mobius.PostRead

abbrev Input (I : Type) := I → Bool
abbrev Pin (I : Type) := Option (I × Bool)

def restrict [DecidableEq I] (p : Pin I) (x : Input I) : Input I :=
  match p with
  | none => x
  | some (i, b) => fun j => if j = i then b else x j

def cube [DecidableEq I] : List (Pin I) → Input I → Input I
  | [], x => x
  | p :: ps, x => restrict p (cube ps x)

def Unary (f : Input I → R) : Prop :=
  (∃ c, ∀ x, f x = c) ∨ ∃ i : I, ∃ g : Bool → R, ∀ x, f x = g (x i)

private theorem map_unary {f : Input I → A} (h : Unary f) (g : A → B) :
    Unary (fun x => g (f x)) := by
  rcases h with ⟨v, hv⟩ | ⟨i, u, hu⟩
  · exact Or.inl ⟨g v, fun x => congrArg g (hv x)⟩
  · exact Or.inr ⟨i, fun b => g (u b), fun x => congrArg g (hu x)⟩

private theorem on_face [DecidableEq I] {f : Input I → R} (h : Unary f) (p : Pin I) :
    Unary (fun x => f (restrict p x)) := by
  rcases h with ⟨v, hv⟩ | ⟨j, u, hu⟩
  · exact Or.inl ⟨v, fun x => hv _⟩
  · cases p with
    | none => exact Or.inr ⟨j, u, hu⟩
    | some pair =>
      obtain ⟨i, b⟩ := pair
      by_cases same : j = i
      · exact Or.inl ⟨u b, fun x => (hu _).trans (by simp [restrict, same])⟩
      · exact Or.inr ⟨j, u, fun x => (hu _).trans (by simp [restrict, same])⟩

private theorem freeze [DecidableEq I] {f : Input I → R} (h : Unary f) (atInput : Input I) :
    ∃ p : Pin I, ∀ x, f (restrict p x) = f atInput := by
  rcases h with ⟨v, hv⟩ | ⟨i, u, hu⟩
  · exact ⟨none, fun x => (hv _).trans (hv _).symm⟩
  · exact ⟨some (i, atInput i), fun x => by simp [hu, restrict]⟩

theorem binary_step [DecidableEq I] {f : Input I → A} {g : Input I → B}
    (hf : Unary f) (hg : Unary g) (op : A → B → R) :
    ∃ p : Pin I, Unary (fun x => op (f (restrict p x)) (g (restrict p x))) := by
  obtain ⟨p, fixed⟩ := freeze hf (fun _ => false)
  refine ⟨p, ?_⟩
  simp only [fixed]
  exact map_unary (on_face hg p) (op _)

private def batch (tests : List J) (observe : J → Input I → Bool) (x : Input I) :=
  tests.all (fun t => observe t x)

theorem batch_step [DecidableEq I] (tests : List J) (observe : J → Input I → Bool)
    (unary : ∀ t ∈ tests, Unary (observe t)) :
    ∃ p : Pin I, ∃ b, ∀ x, batch tests observe (restrict p x) = b := by
  by_cases always : ∀ x, batch tests observe x = true
  · exact ⟨none, true, fun x => always x⟩
  · obtain ⟨w, bad⟩ := Classical.not_forall.mp always
    have fails : ¬ ∀ t ∈ tests, observe t w = true := fun h => bad (List.all_eq_true.mpr h)
    obtain ⟨t, ht⟩ := Classical.not_forall.mp fails
    have present : t ∈ tests := Classical.byContradiction (fun hn => ht (fun h => (hn h).elim))
    have no : observe t w ≠ true := fun h => ht (fun _ => h)
    obtain ⟨p, fixed⟩ := freeze (unary t present) w
    refine ⟨p, false, fun x => Bool.eq_false_iff.mpr ?_⟩
    intro ok
    exact no ((fixed x).symm.trans (List.all_eq_true.mp ok t present))

abbrev Bank (R : Type) := Nat → R
private def put (b : Bank R) (dst : Nat) (v : R) : Bank R := fun i => if i=dst then v else b i

/-- The index is a bound on the number of paid instructions of a real run. -/
inductive Code (R : Type) : Nat → Type where
  | halt {n} (src : Nat) : Code R n
  | binary {n} (i j dst : Nat) (op : R → R → R) (next : Code R n) : Code R (n+1)
  | branch {n} (i : Nat) (next : R → Code R n) : Code R (n+1)
  | lookup {n} (i dst : Nat) (index : R → Nat) (next : Code R n) : Code R (n+1)
  | ask {n} (tests : List (Nat × (R → Bool))) (dst : Nat) (pack : Bool → R)
      (next : Bool → Code R n) : Code R (n+1)

def run : {n : Nat} → Code R n → Bank R → R
  | _, .halt i, b => b i
  | _, .binary i j d op c, b => run c (put b d (op (b i) (b j)))
  | _, .branch i c, b => run (c (b i)) b
  | _, .lookup i d index c, b => run c (put b d (b (index (b i))))
  | _, .ask tests d pack c, b =>
    let result := tests.all (fun (i, test) => test (b i))
    run (c result) (put b d (pack result))

private theorem updated {bank : Input I → Bank R} {value : Input I → R} (d : Nat)
    (hu : ∀ i, Unary (fun x => bank x i)) (hv : Unary value) :
    ∀ j, Unary (fun x => put (bank x) d (value x) j) := by
  intro j
  by_cases h : j = d
  · simpa [put, h] using hv
  · simpa [put, h] using hu j

/-- There is one surviving subcube after any number of adaptive steps.
Repeated reads of old registers require no copies in this induction. -/
theorem leave_unary [DecidableEq I] (c : Code R n) (bank : Input I → Bank R)
    (initial : ∀ j, Unary (fun x => bank x j)) :
    ∃ ps : List (Pin I), ps.length ≤ n ∧ Unary (fun x => run c (bank (cube ps x))) := by
  induction c generalizing bank with
  | halt i => exact ⟨[], by simp, initial i⟩
  | binary i j d op c ih =>
    obtain ⟨p, new⟩ := binary_step (initial i) (initial j) op
    let b x := bank (restrict p x)
    obtain ⟨ps, len, good⟩ := ih (fun x => put (b x) d (op (b x i) (b x j)))
      (updated d (fun j => on_face (initial j) p) new)
    exact ⟨p::ps, by simp; omega, good⟩
  | branch i c ih =>
    obtain ⟨p, fixed⟩ := freeze (initial i) (fun _ => false)
    obtain ⟨ps, len, good⟩ := ih _ (fun x => bank (restrict p x)) (fun j => on_face (initial j) p)
    exact ⟨p::ps, by simp; omega, by simpa only [run, cube, fixed] using good⟩
  | lookup i d index c ih =>
    obtain ⟨p, fixed⟩ := freeze (initial i) (fun _ => false)
    let j := index (bank (fun _ => false) i)
    let b x := bank (restrict p x)
    obtain ⟨ps, len, good⟩ := ih (fun x => put (b x) d (b x j))
      (updated d (fun j => on_face (initial j) p) (on_face (initial j) p))
    exact ⟨p::ps, by simp; omega, by simpa only [run, cube, fixed, b, j] using good⟩
  | ask tests d pack c ih =>
    let obs (t : Nat × (R → Bool)) := fun x => t.2 (bank x t.1)
    obtain ⟨p, value, fixed⟩ := batch_step tests obs (fun t _ => map_unary (initial t.1) t.2)
    let b x := bank (restrict p x)
    obtain ⟨ps, len, good⟩ := ih value (fun x => put (b x) d (pack value))
      (updated d (fun j => on_face (initial j) p) (Or.inl ⟨_, fun _ => rfl⟩))
    refine ⟨p::ps, by simp; omega, ?_⟩
    change Unary (fun x => run (c (batch tests obs (restrict p (cube ps x))))
      (put (b (cube ps x)) d (pack (batch tests obs (restrict p (cube ps x))))))
    simp only [fixed]
    exact good

def output3 (shift : Fin 3) (a b : Bool) : Bool := decide ((shift.val+a.toNat+b.toNat)%3 ≠ 0)

theorem two_free : ∀ shift : Fin 3,
    (∃ a, output3 shift a false ≠ output3 shift a true) ∧
    (∃ b, output3 shift false b ≠ output3 shift true b) := by decide

private def indices (ps : List (Pin I)) := ps.filterMap (fun p => p.map Prod.fst)

private theorem untouched [DecidableEq I] (ps : List (Pin I)) (x : Input I) (i : I)
    (free : i ∉ indices ps) : cube ps x i = x i := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | none => exact ih free
    | some t =>
      obtain ⟨j, b⟩ := t
      change i ∉ j :: indices ps at free
      simp only [List.mem_cons, not_or] at free
      exact (ite_eq_right free.1).trans (ih free.2)

private theorem at_coordinate [DecidableEq I] (ps : List (Pin I)) (x y : Input I) (i : I)
    (same : x i = y i) : cube ps x i = cube ps y i := by
  induction ps with
  | nil => exact same
  | cons p ps ih =>
    cases p with
    | none => exact ih
    | some t => obtain ⟨j,b⟩ := t; by_cases h : i=j <;> simp [cube, restrict, h, ih]

private theorem missing (xs : List (Fin l)) (h : xs.length < l) : ∃ i, i ∉ xs := by
  apply Classical.byContradiction
  intro none
  have sub : List.finRange l ⊆ xs := fun i _ => Classical.byContradiction (fun hi => none ⟨i,hi⟩)
  have le := (List.nodup_finRange l).length_le_of_subset sub
  simp at le
  omega

def oneCycle3 (x : Input (Fin l)) := decide (((List.finRange l).countP x)%3 ≠ 0)

private theorem not_unary_two_left (ps : List (Pin (Fin l))) (small : ps.length+1 < l) :
    ¬ Unary (fun x => oneCycle3 (cube ps x)) := by
  have len : (indices ps).length ≤ ps.length := List.length_filterMap_le _ _
  obtain ⟨i, fi⟩ := missing (indices ps) (by omega)
  obtain ⟨j, fj⟩ := missing (i::indices ps) (by simp; omega)
  simp only [List.mem_cons, not_or] at fj
  let all := List.finRange l
  let rest := (all.erase i).erase j
  have putFirst := List.perm_cons_erase (List.mem_finRange i)
  have putSecond := List.perm_cons_erase ((List.mem_erase_of_ne fj.1).mpr (List.mem_finRange j))
  have perm : all.Perm (i::j::rest) := putFirst.trans (putSecond.cons i)
  have nr := perm.nodup_iff.mp (List.nodup_finRange l)
  simp only [List.nodup_cons, List.mem_cons, not_or] at nr
  let grid (a b : Bool) (v : Fin l) := if v=i then a else if v=j then b else false
  let base := cube ps (fun _ => false)
  let shift : Fin 3 := ⟨(rest.countP base)%3, Nat.mod_lt _ (by decide)⟩
  have table (a b : Bool) : oneCycle3 (cube ps (grid a b)) = output3 shift a b := by
    have tail : rest.countP (cube ps (grid a b)) = rest.countP base := by
      apply List.countP_congr
      intro v hv
      have vi : v ≠ i := fun eq => nr.1.2 (eq ▸ hv)
      have vj : v ≠ j := fun eq => nr.2.1 (eq ▸ hv)
      rw [at_coordinate ps (grid a b) (fun _ => false) v (by simp [grid, vi, vj])]
    have readI : cube ps (grid a b) i = a := by rw [untouched ps _ _ fi]; simp [grid]
    have readJ : cube ps (grid a b) j = b := by rw [untouched ps _ _ fj.2]; simp [grid, fj.1]
    unfold oneCycle3 output3
    rw [perm.countP_eq, List.countP_cons, List.countP_cons, tail, readI, readJ]
    dsimp [shift]
    apply decide_eq_decide.mpr
    cases a <;> cases b <;> simp <;> omega
  obtain ⟨⟨a, variesB⟩, ⟨b, variesA⟩⟩ := two_free shift
  rintro (⟨v, constant⟩ | ⟨k, f, depends⟩)
  · exact variesB ((table a false).symm.trans ((constant _).trans ((constant _).symm.trans (table a true))))
  · by_cases h : k=i
    · exact variesB (by simp only [← table, depends]; simp [grid, h])
    · exact variesA (by simp only [← table, depends]; simp [grid, h])

/-- With all raw switches already available, any correct real-run bound
for the three-track single-cycle predicate is at least l-1 instructions. -/
theorem three_track_time (c : Code R n) (bank : Input (Fin l) → Bank R) (answer : R → Bool)
    (initial : ∀ j, Unary (fun x => bank x j))
    (correct : ∀ x, answer (run c (bank x)) = oneCycle3 x) : l ≤ n+1 := by
  apply Nat.le_of_not_gt
  intro short
  obtain ⟨ps, len, finalReg⟩ := leave_unary c bank initial
  have finalBit := map_unary finalReg answer
  simp only [correct] at finalBit
  exact not_unary_two_left ps (by omega) finalBit

end Mobius.PostRead
