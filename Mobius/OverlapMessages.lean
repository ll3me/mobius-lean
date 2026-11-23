import Mobius.RigidityEnumeration
import Mobius.Bounded

/-! One-way exact memoization for optimal four-bit boards with an actual
shared line. Every board is a full four-space in the same vector space.
Any two distinct boards share four coordinate pairs, hence eight tagged
table entries. In particular the parity on the common direction is visible
at every board. Scores sum *indexed* occurrences: testing a face again
as a selector gives it additional weight. -/
namespace Mobius.OverlapMessages
open Mobius.SignObstruction (B)
open Mobius.Rigidity (DirectionPattern optimal_direction optimal_of_direction)
open Mobius.TwoPhases (score failures failures_lower)

abbrev Phase := B → B → Bool
abbrev Coord (n : Nat) := Bool × (Fin n → BitVec 3)
abbrev GlobalPhase (n : Nat) := Coord n → Coord n → Bool

structure Tables (n : Nat) where
  row : GlobalPhase n
  col : GlobalPhase n

private def top (x : B) : BitVec 3 := x.extractLsb' 1 3

def place (i : Fin n) (x : B) : Coord n :=
  (x.getLsbD 0, fun j => if j=i then top x else 0)

def axis (p : Bool) : Coord n := (p,fun _ => 0)

def axisBit (p : Bool) : B := if p then 1 else 0

theorem place_axis (i : Fin n) (p : Bool) : place i (axisBit p) = axis p := by
  cases p <;> apply Prod.ext
  · rfl
  · funext j; simp [place,top,axisBit,axis]
  · rfl
  · funext j; simp [place,top,axisBit,axis]

def coordXor (x y : Coord n) : Coord n := (x.1 ^^ y.1,fun i => x.2 i ^^^ y.2 i)

theorem place_xor (i : Fin n) (x y : B) : place i (x ^^^ y) = coordXor (place i x) (place i y) := by
  apply Prod.ext
  · exact BitVec.getLsbD_xor
  · funext j
    by_cases h : j=i <;> simp [place,coordXor,top,h,BitVec.extractLsb'_xor]

private def unpack (i : Fin n) (a : Coord n) : B := a.2 i ++ BitVec.ofBool a.1

private theorem unpack_place (i : Fin n) (x : B) : unpack i (place i x) = x := by
  have hi (v : B) : top v ++ BitVec.ofBool (v.getLsbD 0) = v := by revert v; decide
  simpa [unpack,place] using hi x

theorem place_injective (i : Fin n) {x y : B} (h : place i x = place i y) : x=y := by
  simpa only [unpack_place] using congrArg (unpack i) h

/-- Thus the only shared coordinates of two distinct four-spaces are
    zero and the same nonzero generator, with no abstract identifications. -/
theorem board_intersection {i j : Fin n} (ij : i≠j) {x y : B} (h : place i x=place j y) :
    ∃ p : Bool, x=axisBit p ∧ y=axisBit p := by
  have l := congrArg (fun a : Coord n => a.2 i) h
  have r := congrArg (fun a : Coord n => a.2 j) h
  simp only [place, ite_eq_right ij, ite_eq_right (Ne.symm ij)] at l r
  have tiny (v : B) : top v=0 → v=axisBit (v.getLsbD 0) := by revert v; decide
  have same := congrArg Prod.fst h
  change x.getLsbD 0 = y.getLsbD 0 at same
  exact ⟨_,tiny x l,same.symm ▸ tiny y r.symm⟩

def pull (p : GlobalPhase n) (i : Fin n) : Phase := fun x y => p (place i x) (place i y)

def boardCost (t : Tables n) (i : Fin n) := failures (pull t.row i) (pull t.col i)

def rep (t : Tables n) (i : Fin n) (d : B) : Bool := score (pull t.row i) (pull t.col i) (0,0,d)

theorem common_face (t : Tables n) (i j : Fin n) : rep t i 1 = rep t j 1 := by
  have z : place i 0 = place j 0 := (place_axis i false).trans (place_axis j false).symm
  have g : place i 1 = place j 1 := (place_axis i true).trans (place_axis j true).symm
  change (t.row (place i 0) (place i 0) ^^ (t.row (place i 1) (place i 1) ^^
      (t.col (place i 0) (place i 1) ^^ (t.col (place i 1) (place i 0) ^^ false)))) = _
  rw [z,g]
  rfl

theorem shared_direction_lock (t : Tables n) (i j : Fin n) {a b : B}
    (ha : DirectionPattern (pull t.row i) (pull t.col i) a)
    (hb : DirectionPattern (pull t.row j) (pull t.col j) b) : a=1 ↔ b=1 := by
  have shared := common_face t i j
  change score _ _ _ = score _ _ _ at shared
  rw [ha.2 0 0 1 (by decide),hb.2 0 0 1 (by decide)] at shared
  have fact (u v : B) (h : decide ((1 : B) ≠ u) = decide ((1 : B) ≠ v)) (hu : u=1) : v=1 := by
    subst u
    by_cases hv : v=1
    · exact hv
    · rw [decide_eq_true (Ne.symm hv)] at h
      contradiction
  exact ⟨fact _ _ shared, fact _ _ shared.symm⟩

private def localGround (d x y : B) : Bool :=
  Mobius.EightSquare.phase (Mobius.SignObstruction.quotient d x) (Mobius.SignObstruction.quotient d y)

private theorem ground_law {d : B} (nz : d≠0) : DirectionPattern (localGround d) (localGround d) d :=
  Mobius.Rigidity.Enumeration.ground_pattern ⟨d,nz⟩

private theorem ground_line : ∀ d : B, d≠0 → ∀ x y : B, top x=0 → top y=0 →
    localGround d x y = (!(d == 1) && x.getLsbD 0 && y.getLsbD 0) := by decide

private def owner (x y : Coord n) : Option (Fin n) :=
  (List.finRange n).find? (fun i => x.2 i != 0 || y.2 i != 0)

private def assembled (ds : Fin n → B) (common : Bool) (x y : Coord n) : Bool :=
  match owner x y with
  | some i => localGround (ds i) (unpack i x) (unpack i y)
  | none => !common && x.1 && y.1

private theorem assembled_pull (ds : Fin n → B) (common : Bool) (nz : ∀ i, ds i≠0)
    (coherent : ∀ i, (ds i == 1) = common) (i : Fin n) :
    pull (assembled ds common) i = localGround (ds i) := by
  funext x y
  unfold pull assembled
  cases h : owner (place i x) (place i y) with
  | none =>
    have idle := List.find?_eq_none.mp h i (by simp)
    simp [place] at idle
    rw [ground_line (ds i) (nz i) x y idle.1 idle.2,coherent]
    rfl
  | some j =>
    have active := List.find?_some h
    have same : j=i := by
      by_cases eq : j=i
      · exact eq
      · simp [place,eq] at active
    subst j
    change localGround (ds i) (unpack i (place i x)) (unpack i (place i y)) = _
    rw [unpack_place,unpack_place]

/-- Full classification of feasible exceptional directions across the
    shared line: either every board fails on it or none does. The proof
    assembles real row and column tables on the whole ambient space. -/
theorem joint_patterns_iff (ds : Fin n → B) (nz : ∀ i, ds i ≠ 0) :
    (∃ t : Tables n, ∀ i, DirectionPattern (pull t.row i) (pull t.col i) (ds i)) ↔
    ∀ i j, (ds i = 1 ↔ ds j = 1) := by
  constructor
  · rintro ⟨t,ht⟩ i j
    exact shared_direction_lock t i j (ht i) (ht j)
  · intro compatible
    let common := decide (∃ i, ds i=1)
    have coherent (i : Fin n) : (ds i == 1) = common := by
      by_cases eq : ds i=1
      · have ex : ∃ j, ds j=1 := ⟨i,eq⟩
        unfold common
        rw [beq_iff_eq.mpr eq,decide_eq_true ex]
      · have no : ¬∃ j, ds j=1 := fun ⟨j,hj⟩ => eq ((compatible j i).mp hj)
        unfold common
        rw [beq_eq_false_iff_ne.mpr eq,decide_eq_false no]
    let p := assembled ds common
    refine ⟨⟨p,p⟩,fun i => ?_⟩
    change DirectionPattern (pull (assembled ds common) i) (pull (assembled ds common) i) (ds i)
    rw [assembled_pull ds common nz coherent]
    exact ground_law (nz i)

abbrev Slot := Fin 14
/-- All nonempty subsets of the fourteen directions 2,...,15. -/
abbrev Mask := Fin 16383
abbrev Profile (n : Nat) := Fin n → Mask

def direction (d : Slot) : B := BitVec.ofNat 4 (d.val+2)
private theorem direction_good (d : Slot) : direction d ≠ 0 ∧ direction d ≠ 1 := by revert d; decide
private theorem direction_inj (d e : Slot) : direction d = direction e → d=e := by revert d e; decide

private def maskBits (m : Mask) : BitVec 14 := BitVec.ofNat 14 (m.val+1)
def allowed (m : Mask) (d : Slot) : Bool := (maskBits m).getLsbD d.val

private theorem mask_nat (m : Mask) : (maskBits m).toNat = m.val+1 := by
  change (m.val+1)%16384=m.val+1
  exact Nat.mod_eq_of_lt (by omega)

private theorem has_slot (m : Mask) : ∃ k : Slot, allowed m k=true := by
  apply Classical.byContradiction
  intro no
  have all : maskBits m = 0 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    have h := fun pos => no (Exists.intro (⟨i,hi⟩ : Slot) pos)
    change (maskBits m).getLsbD i ≠ true at h
    cases hp : (maskBits m).getLsbD i <;> simp_all
  have n := mask_nat m
  rw [all] at n
  change 0=m.val+1 at n
  omega

private theorem mask_ext {m q : Mask} (same : ∀ k, allowed m k = allowed q k) : m=q := by
  have eq := BitVec.eq_of_getLsbD_eq_iff.mpr (fun i hi => same ⟨i,hi⟩)
  have vals := congrArg BitVec.toNat (show maskBits m = maskBits q from eq)
  rw [mask_nat,mask_nat] at vals
  exact Fin.ext (Nat.succ.inj vals)

/-- Each forbidden local direction contributes its genuine anchored
    square (0,0,d) to the left objective. The suffix watches every nonzero
    direction except the queried one at its specified board. -/
def leftFaces (m : Mask) : List B :=
  ((List.finRange 14).filter (fun k => !(allowed m k))).map direction

def rightFaces (k : Slot) : List B :=
  Mobius.SignObstruction.directions.filter (fun d => d != direction k)

def extra (t : Tables n) (i : Fin n) (ds : List B) : Nat := ds.countP (fun d => !(rep t i d))

def combined (t : Tables n) (A : Profile n) (i : Fin n) (k : Slot) :=
  ((List.finRange n).map (fun j => boardCost t j + extra t j (leftFaces (A j)))).sum +
    extra t i (rightFaces k)

def AtBaseline (A : Profile n) (i : Fin n) (k : Slot) : Prop :=
  ∃ t : Tables n, combined t A i k = 256*n

private theorem extra_zero (t : Tables n) (i : Fin n) (ds : List B) :
    extra t i ds = 0 ↔ ∀ d ∈ ds, rep t i d = true := by
  rw [extra,List.countP_eq_zero]
  simp only [Bool.not_eq_true',Bool.not_eq_false]

private theorem left_mem (m : Mask) (k : Slot) :
    direction k ∈ leftFaces m ↔ allowed m k=false := by
  constructor
  · intro h
    obtain ⟨j,mem,eq⟩ := List.mem_map.mp h
    obtain rfl := direction_inj _ _ eq
    simpa only [Bool.not_eq_true'] using (List.mem_filter.mp mem).2
  · intro h
    exact List.mem_map.mpr ⟨k,List.mem_filter.mpr ⟨by simp,by simp [h]⟩,rfl⟩

private theorem right_mem (d : B) (k : Slot) : d∈rightFaces k ↔ d≠0 ∧ d≠direction k := by
  have dmem : ∀ u : B, u∈Mobius.SignObstruction.directions ↔ u≠0 := by decide
  simp only [rightFaces,List.mem_filter,dmem,bne_iff_ne]

private theorem sum_min (xs : List α) (f : α→Nat) (b : Nat) (h : ∀ x ∈ xs, b≤f x) :
    b*xs.length ≤ (xs.map f).sum ∧
    ((xs.map f).sum = b*xs.length ↔ ∀ x ∈ xs, f x=b) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    obtain ⟨low,sharp⟩ := ih (fun u hu => h u (by simp [hu]))
    simp only [List.length_cons,Nat.mul_succ,List.map_cons,List.sum_cons,List.forall_mem_cons]
    constructor
    · omega
    · constructor
      · intro eq
        exact ⟨by omega,sharp.mp (by omega)⟩
      · rintro ⟨eq,tail⟩
        rw [eq,sharp.mpr tail,Nat.add_comm]

/-- All the terms are ordinary failure counts. A strict deviation
    from optimality of a full board cannot be hidden by a negative weight. -/
theorem baseline_spec (t : Tables n) (A : Profile n) (i : Fin n) (k : Slot) :
    combined t A i k = 256*n ↔
      (∀ j, boardCost t j = 256 ∧ ∀ d∈leftFaces (A j), rep t j d=true) ∧
      (∀ d∈rightFaces k, rep t i d=true) := by
  let f j := boardCost t j + extra t j (leftFaces (A j))
  have low j : 256 ≤ boardCost t j := failures_lower ..
  obtain ⟨sumLow,sharp⟩ := sum_min (List.finRange n) f 256 (fun j _ => by dsimp [f]; have := low j; omega)
  rw [List.length_finRange] at sumLow sharp
  change (List.map f (List.finRange n)).sum + extra t i (rightFaces k) = _ ↔ _
  constructor
  · intro equal
    have all := sharp.mp (by omega)
    refine ⟨fun j => ?_,(extra_zero ..).mp (by omega)⟩
    have localEq := all j (by simp)
    change boardCost t j + extra t j (leftFaces (A j)) = 256 at localEq
    have := low j
    exact ⟨by omega,(extra_zero ..).mp (by omega)⟩
  · rintro ⟨boards,probe⟩
    have each (j : Fin n) : f j = 256 := by
      dsimp [f]
      rw [(boards j).1,(extra_zero ..).mpr (boards j).2,Nat.add_zero]
    rw [sharp.mpr (fun j _ => each j),(extra_zero ..).mpr probe,Nat.add_zero]

theorem joint_threshold_iff (A : Profile n) (i : Fin n) (k : Slot) :
    AtBaseline A i k ↔ allowed (A i) k = true := by
  constructor
  · rintro ⟨t,cost⟩
    obtain ⟨boards,watch⟩ := (baseline_spec t A i k).mp cost
    obtain ⟨d,pat,_⟩ := optimal_direction _ _ (boards i).1
    have bad : rep t i d = false := by exact (pat.2 0 0 d pat.1).trans (decide_eq_false (not_not_intro rfl))
    have forced : d = direction k := by
      by_cases eq : d=direction k
      · exact eq
      · have good := watch d ((right_mem d k).mpr ⟨pat.1,eq⟩)
        rw [bad] at good
        contradiction
    subst d
    cases status : allowed (A i) k
    · have good := (boards i).2 (direction k) ((left_mem _ _).mpr status)
      rw [bad] at good
      contradiction
    · rfl
  · intro yes
    let choice (j : Fin n) := if j=i then k else Classical.choose (has_slot (A j))
    have admissible (j : Fin n) : allowed (A j) (choice j) = true := by
      by_cases same : j=i
      · subst j; simpa [choice] using yes
      · simpa [choice,same] using Classical.choose_spec (has_slot (A j))
    let ds j := direction (choice j)
    have good j := direction_good (choice j)
    obtain ⟨t,pattern⟩ := (joint_patterns_iff ds (fun j => (good j).1)).mpr (by
      intro a b
      exact iff_of_false (good a).2 (good b).2)
    refine ⟨t,(baseline_spec t A i k).mpr ⟨fun j => ?_,?_⟩⟩
    · refine ⟨optimal_of_direction (pattern j),?_⟩
      intro d mem
      obtain ⟨v,forbidden,rfl⟩ := List.mem_map.mp mem
      have off := (List.mem_filter.mp forbidden).2
      have ne : direction v ≠ ds j := by
        intro eq
        have same := direction_inj v (choice j) eq
        rw [same,admissible] at off
        contradiction
      exact ((pattern j).2 0 0 _ (direction_good v).1).trans (decide_eq_true ne)
    · intro d mem
      have valid := (right_mem d k).mp mem
      have dk : ds i = direction k := by simp [ds,choice]
      exact ((pattern i).2 0 0 d valid.1).trans (decide_eq_true (dk.symm ▸ valid.2))

private def radix : (n : Nat) → Fin (16383^n) → Profile n
  | 0, _ => Fin.elim0
  | n+1, z => Fin.cases ⟨z.val % 16383,Nat.mod_lt _ (by decide)⟩
      (radix n ⟨z.val/16383, (Nat.div_lt_iff_lt_mul (by decide : 0<16383)).mpr
        (by simpa only [Nat.pow_succ] using z.isLt)⟩)

private theorem radix_inj (n : Nat) {x y : Fin (16383^n)} (h : radix n x = radix n y) : x=y := by
  induction n with
  | zero =>
    apply Fin.ext
    have hx : x.val < 1 := x.isLt
    have hy : y.val < 1 := y.isLt
    omega
  | succ n ih =>
    have low := congrArg Fin.val (congrFun h 0)
    change x.val%16383 = y.val%16383 at low
    have highEq := ih (funext (fun i => congrFun h i.succ))
    have high := congrArg Fin.val highEq
    change x.val/16383 = y.val/16383 at high
    apply Fin.ext
    have xparts := Nat.mod_add_div x.val 16383
    have yparts := Nat.mod_add_div y.val 16383
    omega

/-- One message is computed before the query is revealed. The receiver
    may perform arbitrary deterministic computation, including lookup of
    precomputed common data. -/
theorem memo_state_lower (send : Profile n → Fin s) (readout : Fin s → Fin n → Slot → Bool)
    (correct : ∀ A i k, readout (send A) i k = true ↔ AtBaseline A i k) : 16383^n ≤ s := by
  have distinct {A P : Profile n} (same : send A=send P) : A=P := by
    funext i
    apply mask_ext
    intro k
    have ha := ((correct A i k).trans (joint_threshold_iff A i k)).symm
    rw [same] at ha
    have eq : allowed (A i) k = true ↔ allowed (P i) k = true :=
      ha.trans ((correct P i k).trans (joint_threshold_iff P i k))
    have bools (a b : Bool) (h : a=true ↔ b=true) : a=b := by cases a <;> cases b <;> simp_all
    exact bools _ _ eq
  apply Bounded.fin_size_le (fun i : Fin (16383^n) => send (radix n i))
  intro i j eq
  exact radix_inj n (distinct eq)

private def pack : (n : Nat) → Profile n → Fin (16383^n)
  | 0, _ => ⟨0,by decide⟩
  | n+1, A =>
    let rest := pack n (fun i => A i.succ)
    ⟨rest.val * 16383 + (A 0).val, by
      rw [Nat.pow_succ]
      have hr := rest.isLt
      have hd := (A 0).isLt
      omega⟩

private theorem radix_pack (n : Nat) (A : Profile n) : radix n (pack n A) = A := by
  induction n with
  | zero => exact funext fun j => Fin.elim0 j
  | succ n ih =>
    let rest := pack n (fun i => A i.succ)
    let d := (A 0).val
    have hd : d < 16383 := (A 0).isLt
    have lo : (rest.val*16383+d)%16383=d := by omega
    have hi : (rest.val*16383+d)/16383=rest.val := by omega
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Fin.ext lo
    · have eq : (⟨(rest.val*16383+d)/16383, (Nat.div_lt_iff_lt_mul (by decide : 0<16383)).mpr
          (by have hr := rest.isLt; omega)⟩ : Fin (16383^n)) = rest := Fin.ext hi
      exact (congrArg (fun v => radix n v j) eq).trans (congrFun (ih (fun j => A j.succ)) j)

/-- Storing the base-16383 packed profile attains the state bound. -/
theorem memo_state_upper (n : Nat) : ∃ (send : Profile n → Fin (16383^n))
    (readout : Fin (16383^n) → Fin n → Slot → Bool),
    ∀ A i k, readout (send A) i k = true ↔ AtBaseline A i k := by
  refine ⟨pack n,fun z i k => allowed (radix n z i) k,?_⟩
  intro A i k
  simpa only [radix_pack] using (joint_threshold_iff A i k).symm

/-- An exact fixed-width message exists precisely when its alphabet fits the packed states. -/
theorem memo_bits_iff (n b : Nat) :
    (∃ (send : Profile n → BitVec b) (readout : BitVec b → Fin n → Slot → Bool),
      ∀ A i k, readout (send A) i k = true ↔ AtBaseline A i k) ↔ 16383^n ≤ 2^b := by
  constructor
  · rintro ⟨send,readout,correct⟩
    exact memo_state_lower (fun A => (send A).toFin) (fun s => readout (BitVec.ofFin s)) correct
  · intro fits
    obtain ⟨send,readout,ok⟩ := memo_state_upper n
    let wire (A : Profile n) : BitVec b := BitVec.ofFin ⟨(send A).val,Nat.lt_of_lt_of_le (send A).isLt fits⟩
    let receive (v : BitVec b) (i : Fin n) (k : Slot) :=
      if h : v.toNat < 16383^n then readout ⟨v.toNat,h⟩ i k else false
    refine ⟨wire,receive,fun A i k => ?_⟩
    have valid : (wire A).toNat < 16383^n := (send A).isLt
    have back : (⟨(wire A).toNat, valid⟩ : Fin (16383^n)) = send A := Fin.ext rfl
    simpa only [receive,dite_eq_left valid,back] using ok A i k

theorem memo_bit_lower (send : Profile n → BitVec b) (readout : BitVec b → Fin n → Slot → Bool)
    (correct : ∀ A i k, readout (send A) i k = true ↔ AtBaseline A i k) : 13*n ≤ b := by
  have lower := memo_state_lower (fun A => (send A).toFin)
    (fun s => readout (BitVec.ofFin s)) correct
  have base : 2^(13*n) ≤ 16383^n := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by decide : 2^13≤16383) _
  exact Nat.le_of_not_lt (fun h => Nat.not_lt_of_ge (Nat.le_trans base lower)
    (Nat.pow_lt_pow_right (by decide : 1<2) h))

end Mobius.OverlapMessages
