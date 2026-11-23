import Mobius.Rigidity
import Mobius.OptimalCertificate

/-! Four-dimensional boards sharing their three-dimensional coordinate
hyperplane. A location contains three common bits and one independent bit
per board. The global phase below is a single ordinary table on these
locations, not separate tables with consistency asserted as a hypothesis. -/
namespace Mobius.OverlapBoards

open Mobius.SignObstruction (B)
open Mobius.TwoPhases (score failures)
open Mobius.Rigidity (DirectionPattern)

abbrev H := BitVec 3
abbrev V (n : Nat) := H × (Fin n → Bool)
abbrev World (n : Nat) := V n → V n → Bool
abbrev Phase := B → B → Bool

def low (x : B) : H := x.setWidth 3
def high (x : B) : Bool := x.getLsbD 3
def inner (x : H) : B := x.setWidth 4
def outer (x : H) : B := 8 ^^^ inner x

def embed (i : Fin n) (x : B) : V n := (low x,fun j => decide (j=i) && high x)
def shared (x : H) : V n := (x,fun _ => false)
def restrict (g : World n) (i : Fin n) : Phase := fun x y => g (embed i x) (embed i y)

/-- None records an external bad direction; some h names its shared direction. -/
def kind (d : B) : Option H := if high d then none else some (low d)

private theorem low_inner : ∀ x : H, low (inner x) = x ∧ high (inner x)=false := by decide
private theorem split_bits : ∀ x y : B, low x = low y → high x = high y → x=y := by decide

@[simp] theorem embed_inner (i : Fin n) (x : H) : embed i (inner x) = shared x := by
  simp [embed,shared,(low_inner x).1,(low_inner x).2]

@[simp] theorem embed_zero (i : Fin n) : embed i 0 = shared 0 := embed_inner i 0

theorem embed_injective (i : Fin n) {x y : B} (eq : embed i x = embed i y) : x=y := by
  apply split_bits _ _ (congrArg (fun p : V n => p.1) eq)
  simpa [embed] using congrArg (fun p : V n => p.2 i) eq

/-- The physical overlap of distinct boards is exactly H. -/
theorem distinct_intersection (i j : Fin n) (ne : i≠j) (x y : B) :
    embed i x = embed j y ↔ x=y ∧ high x=false := by
  constructor
  · intro eq
    have l : low x=low y := congrArg (fun p : V n => p.1) eq
    have a := congrArg (fun p : V n => p.2 i) eq
    have b := congrArg (fun p : V n => p.2 j) eq
    simp [embed,ne,Ne.symm ne] at a b
    exact ⟨split_bits x y l (a.trans b.symm),a⟩
  · rintro ⟨rfl,h⟩
    simp [embed,h]

theorem shared_score (r c : World n) (i j : Fin n) (x y h : H) :
    score (restrict r i) (restrict c i) (inner x,inner y,inner h) =
    score (restrict r j) (restrict c j) (inner x,inner y,inner h) := by
  have lin : ∀ a b : H, inner a ^^^ inner b = inner (a ^^^ b) := by decide
  simp [score,TwoPhases.corners,SignObstruction.total,restrict,lin]

private theorem kind_test : ∀ d e : B, d ≠ 0 → e ≠ 0 →
    (∀ h : H, h≠0 → decide (inner h≠d) = decide (inner h≠e)) → kind d=kind e := by decide

theorem necessary (r c : World n) (ds : Fin n → B)
    (profile : ∀ i, DirectionPattern (restrict r i) (restrict c i) (ds i))
    (i j : Fin n) : kind (ds i) = kind (ds j) := by
  apply kind_test _ _ (profile i).1 (profile j).1
  intro h hn
  have nonzero : ∀ z : H, z ≠ 0 → inner z ≠ 0 := by decide
  have hnz := nonzero h hn
  exact (((profile i).2 (inner 0) (inner 0) (inner h) hnz).symm.trans
    (shared_score r c i j 0 0 h)).trans ((profile j).2 _ _ _ hnz)

theorem optimal_directions (r c : World n)
    (opt : ∀ i, failures (restrict r i) (restrict c i) = 256) :
    ∃ ds : Fin n → B,
      (∀ i, DirectionPattern (restrict r i) (restrict c i) (ds i)) ∧
      ∀ i j, kind (ds i)=kind (ds j) := by
  have each i := Rigidity.optimal_direction _ _ (opt i)
  let ds i := Classical.choose (each i)
  have profiles i := (Classical.choose_spec (each i)).1
  exact ⟨ds,profiles,necessary r c ds profiles⟩

/-- This particular external quotient keeps the shared hyperplane literally
fixed for every one of its eight possible kernels. -/
def q (d x : B) : H :=
  if high d then low x ^^^ (if high x then low d else 0)
  else SignObstruction.quotient d x

private theorem q_add : ∀ d x y : B, q d (x ^^^ y) = (q d x ^^^ q d y) := by decide
private theorem q_kernel : ∀ d x : B, d≠0 → (q d x = 0 ↔ x=0 ∨ x=d) := by decide

def coreMap (typ : Option H) (x : H) : H :=
  match typ with
  | none => x
  | some a => SignObstruction.quotient (inner a) (inner x)

private theorem q_split : ∀ d x : B,
    coreMap (kind d) (low x) ^^^ (if high x then q d 8 else 0) = q d x := by decide

def privateSum (ds : Fin n → B) (flags : Fin n → Bool) : H :=
  (List.finRange n).foldr (fun i acc => if flags i then q (ds i) 8 ^^^ acc else acc) 0

def project (typ : Option H) (ds : Fin n → B) (x : V n) : H :=
  coreMap typ x.1 ^^^ privateSum ds x.2

private theorem singleton_sum [DecidableEq α] (xs : List α) (nd : xs.Nodup) (k : α)
    (b : Bool) (f : α → H) :
    xs.foldr (fun i acc => if decide (i=k) && b then f i ^^^ acc else acc) 0 =
    (if k∈xs ∧ b=true then f k else 0) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    rw [List.foldr_cons,ih tail]
    by_cases eq : x=k
    · subst x; cases b <;> simp [fresh]
    · cases b <;> simp [eq,Ne.symm eq]

theorem project_embed (typ : Option H) (ds : Fin n → B) (i : Fin n)
    (same : kind (ds i)=typ) (x : B) : project typ ds (embed i x) = q (ds i) x := by
  unfold project embed privateSum
  rw [singleton_sum (List.finRange n) (List.nodup_finRange n) i (high x) (fun j => q (ds j) 8)]
  simpa only [List.mem_finRange,true_and,←same] using q_split (ds i) x

def global (typ : Option H) (ds : Fin n → B) : World n := fun x y =>
  EightSquare.phase (project typ ds x) (project typ ds y)

def quotientPhase (d : B) : Phase := fun x y => EightSquare.phase (q d x) (q d y)

theorem global_restrict (typ : Option H) (ds : Fin n → B) (i : Fin n)
    (same : kind (ds i)=typ) : restrict (global typ ds) i = quotientPhase (ds i) := by
  funext x y
  simp [restrict,global,project_embed _ _ i same,quotientPhase]

private theorem three_score : ∀ a b h : H,
    (EightSquare.phase a b ^^
      (EightSquare.phase (a^^^h) (b^^^h) ^^
      (EightSquare.phase a (b^^^h) ^^ (EightSquare.phase (a^^^h) b ^^ false)))) = decide (h≠0) := by decide

theorem quotient_pattern (d : B) (hn : d≠0) :
    DirectionPattern (quotientPhase d) (quotientPhase d) d := by
  refine ⟨hn,?_⟩
  intro x y e he
  have law := three_score (q d x) (q d y) (q d e)
  have scorelaw : score (quotientPhase d) (quotientPhase d) (x,y,e) = decide (q d e≠0) := by
    simpa [score,TwoPhases.corners,SignObstruction.total,quotientPhase,q_add] using law
  rw [scorelaw]
  by_cases h : e=d
  · have hz := (q_kernel d e hn).2 (Or.inr h)
    exact (decide_eq_false (fun nz => nz hz)).trans (decide_eq_false (fun ne => ne h)).symm
  · have hz : q d e ≠ 0 := fun eq => ((q_kernel _ _ hn).1 eq).elim he h
    exact (decide_eq_true hz).trans (decide_eq_true h).symm

/-- The same global table can be used for both row and column phases.
No consistency or extension axiom on separate local tables is required. -/
theorem realizes (typ : Option H) (ds : Fin n → B) (hn : ∀ i, ds i≠0)
    (compat : ∀ i, kind (ds i)=typ) (i : Fin n) :
    let p := restrict (global typ ds) i
    DirectionPattern p p (ds i) ∧ failures p p = 256 := by
  dsimp only
  rw [global_restrict typ ds i (compat i)]
  have pat := quotient_pattern _ (hn i)
  exact ⟨pat,Rigidity.optimal_of_direction pat⟩

/-- Exact realizability of a vector of requested directions. The left side
allows arbitrary independent global row/column tables; sufficiency already
holds with those two tables equal. This includes zero or one board. -/
theorem profile_iff (ds : Fin n → B) :
    (∃ r c : World n, ∀ i, DirectionPattern (restrict r i) (restrict c i) (ds i)) ↔
    (∀ i, ds i≠0) ∧ ∀ i j, kind (ds i)=kind (ds j) := by
  constructor
  · rintro ⟨r,c,pat⟩
    exact ⟨fun i => (pat i).1,necessary r c ds pat⟩
  · rintro ⟨hn,compat⟩
    cases n with
    | zero => exact ⟨fun _ _ => false,fun _ _ => false,fun i => Fin.elim0 i⟩
    | succ n =>
      let typ := kind (ds 0)
      exact ⟨global typ ds,global typ ds,fun i => (realizes typ ds hn (fun j => compat j 0) i).1⟩

theorem arbitrary_outer (labels : Fin n → H) :
    ∃ p : World n, ∀ i, DirectionPattern (restrict p i) (restrict p i) (outer (labels i)) ∧
      failures (restrict p i) (restrict p i) = 256 := by
  have basic : ∀ a : H, outer a≠0 ∧ kind (outer a)=none := by decide
  exact ⟨global none (fun i => outer (labels i)),
    realizes none _ (fun i => (basic _).1) (fun i => (basic _).2)⟩


/-- Directed tests are indexed by their two anchors and their step. -/
abbrev Rect := SignObstruction.Rectangle
def placed (i : Fin n) (r : Rect) := (embed i r.1,embed i r.2.1,embed i r.2.2)
def outside (r : Rect) := high r.1 || high r.2.1 || high r.2.2

theorem same_test (i j : Fin n) (ne : i≠j) (r t : Rect) :
    placed i r = placed j t ↔ r=t ∧ outside r=false := by
  obtain ⟨x,y,d⟩ := r
  obtain ⟨a,b,e⟩ := t
  simp only [placed,Prod.mk.injEq,distinct_intersection _ _ ne,outside,Bool.or_eq_false_iff]
  grind

theorem placed_injective (i : Fin n) {r t : Rect} (h : placed i r = placed i t) : r=t := by
  obtain ⟨x,y,d⟩ := r; obtain ⟨a,b,e⟩ := t
  simp only [placed,Prod.mk.injEq] at h ⊢
  exact ⟨embed_injective i h.1,embed_injective i h.2.1,embed_injective i h.2.2⟩

def shellCost (r c : Phase) : Nat :=
  Rigidity.totalDefects (fun t => outside t && Rigidity.twoBad r c t)

private theorem certificate_good : Rigidity.IsTemplate TwoPhases.certificate := by unfold Rigidity.IsTemplate; decide
private theorem certificate_nz : ∀ t∈TwoPhases.certificate, t.2.2 ≠ 0 := by decide

private def externalShift (s : SignObstruction.Cell) := high s.1 || high s.2
private theorem certified_shell : ∀ s∈SignObstruction.shifts, externalShift s=true →
    ∀ t∈TwoPhases.certificate, outside (SignObstruction.translate s t) = true := by decide +kernel

private theorem some_bad (r c : Phase) (s : SignObstruction.Cell) :
    ∃ t∈TwoPhases.certificate, score r c (SignObstruction.translate s t) = false := by
  apply Classical.byContradiction
  intro none
  apply TwoPhases.fifteen_inconsistent
  refine ⟨SignObstruction.shiftedPhase r s,SignObstruction.shiftedPhase c s,fun t ht => ?_⟩
  rw [←TwoPhases.score_translate]
  cases hv : score r c (SignObstruction.translate s t) with
  | false => exact False.elim (none ⟨t,ht,hv⟩)
  | true => rfl

private theorem sum_le {α} (xs : List α) (f g : α → Nat) (le : ∀ x∈xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (le _ (by simp)) (ih (fun x hx => le x (by simp [hx])))

/-- 192 of the actual odd translated certificates avoid all shared tests.
This lower bound applies even when the complete board is not locally optimal. -/
theorem shell_lower (r c : Phase) : 192 ≤ shellCost r c := by
  let bad := fun t => outside t && Rigidity.twoBad r c t
  have sz : (SignObstruction.shifts.map (fun s => (externalShift s).toNat)).sum = 192 := by decide +kernel
  rw [shellCost,←Rigidity.total_of_template _ _ certificate_good,←sz]
  apply sum_le; intro s hs
  cases out : externalShift s with
  | false => exact Nat.zero_le _
  | true =>
    obtain ⟨t,ht,hb⟩ := some_bad r c s
    apply List.length_pos_of_mem (a:=t)
    exact List.mem_filter.mpr ⟨ht,by simp [certified_shell s hs out t ht,Rigidity.twoBad,hb]⟩

private theorem shell_size : ∀ d : B, d≠0 →
    Rigidity.totalDefects (fun t => outside t && (t.2.2 == d)) = if high d then 256 else 192 := by
  decide +kernel

theorem shell_pattern {r c : Phase} {d : B} (pat : DirectionPattern r c d) :
    shellCost r c = if high d then 256 else 192 := by
  rw [← shell_size d pat.1,shellCost]
  rw [←Rigidity.total_of_template _ _ certificate_good,←Rigidity.total_of_template _ _ certificate_good]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  unfold Rigidity.hits
  apply congrArg List.length
  apply List.filter_congr
  intro t ht
  obtain ⟨x,y,e⟩ := t
  change (outside _ && !(score r c (s.1^^^x,s.2^^^y,e))) = (outside _ && (e==d))
  rw [pat.2 _ _ _ (certificate_nz _ ht)]
  by_cases h : e=d <;> simp [h]

/-- Count each distinct directed test exactly once: retain all of board zero
and only the private shells of subsequent boards (see same_test). -/
def unionCost (r c : World (n+1)) :=
  failures (restrict r 0) (restrict c 0) +
    ((List.finRange n).map fun i => shellCost (restrict r i.succ) (restrict c i.succ)).sum

private theorem sum_const_nat (xs : List α) (k : Nat) : (xs.map (fun _ => k)).sum = xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.succ_mul]
    omega

theorem union_lower (r c : World (n+1)) : 256 + n*192 ≤ unionCost r c := by
  have shell := sum_le (List.finRange n) (fun _ => 192)
    (fun i => shellCost (restrict r i.succ) (restrict c i.succ)) (fun _ _ => shell_lower _ _)
  rw [sum_const_nat,List.length_finRange] at shell
  exact Nat.add_le_add (TwoPhases.failures_lower _ _) shell

theorem union_exact (n : Nat) :
    (∀ r c : World (n+1), 256+n*192 ≤ unionCost r c) ∧
    ∃ p : World (n+1), unionCost p p = 256+n*192 := by
  let ds : Fin (n+1) → B := fun _ => 1
  let p := global (some 1) ds
  have info (i : Fin (n+1)) : DirectionPattern (restrict p i) (restrict p i) 1 ∧
      failures (restrict p i) (restrict p i) = 256 :=
    realizes (some 1) ds (fun _ => by decide) (fun _ => by decide) i
  have she (i : Fin n) : shellCost (restrict p i.succ) (restrict p i.succ) = 192 := by
    exact shell_pattern (info i.succ).1
  refine ⟨union_lower, p,?_⟩
  unfold unionCost
  rw [(info 0).2,List.map_congr_left (fun i _ => she i),sum_const_nat,List.length_finRange]

theorem outer_union (labels : Fin (n+1) → H) :
    ∃ p : World (n+1), (∀ i, DirectionPattern (restrict p i) (restrict p i) (outer (labels i))) ∧
      unionCost p p = 256+n*256 := by
  obtain ⟨p,h⟩ := arbitrary_outer labels
  have ho : ∀ a : H, high (outer a)=true := by decide
  have she (i : Fin n) : shellCost (restrict p i.succ) (restrict p i.succ) = 256 := by
    rw [shell_pattern (h i.succ).1,ho]; rfl
  refine ⟨p,fun i => (h i).1,?_⟩
  unfold unionCost
  rw [(h 0).2,List.map_congr_left (fun i _ => she i),sum_const_nat,List.length_finRange]

end Mobius.OverlapBoards
