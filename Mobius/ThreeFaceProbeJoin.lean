import Mobius.ThreeFaceAttachment
import Mobius.ThreeFaceMemory

/-! Full-board implementation of the two-station query. A displayed ambient
point is a linear functional on its coordinate coefficients. Station
coordinates and the private neutral, dummy, and Fano probe coordinates
are distinct fields. Each main line consists of two independent points
and their XOR, with one common two-dimensional core. -/
namespace Mobius.ThreeFaceProbeJoin
open Mobius.ThreeFaceMemory (Query Graph adjacent)
open Mobius.ThreeFaceBoards (fano)
abbrev Triple := BitVec 3

structure Coeffs (k : Nat) where
  site : Fin k → Bool
  neutral : Fin k → Bool
  dummyA : Query k → Bool
  dummyB : Query k → Bool
  probeA : Fin k → Bool
  probeB : Fin k → Bool

abbrev Point (k : Nat) := Coeffs k → Bool
def origin : Point k := fun _ => false

def picked (q : Query k) (v : Fin k) : Bool := decide (v=q.lo ∨ v=q.hi)
def omitted (q : Query k) (v : Fin k) : Fin 7 := if picked q v then 0 else 3

inductive Page (q : Query k) where
  | neutral (v : Fin k)
  | left (e : Query k)
  | probe (v : Fin k) (l : Fin 7) (present : l≠omitted q v)

def dot3 (t : Triple) (s a b : Bool) :=
  (t.getLsbD 0 && s) ^^ (t.getLsbD 1 && a) ^^ (t.getLsbD 2 && b)

def station (v : Fin k) : Point k := fun c => c.site v
def localPoint (v : Fin k) (t : Triple) : Point k := fun c => dot3 t (c.site v) (c.probeA v) (c.probeB v)

def endpoints (g : Graph k) (q : Query k) : Page q → Point k × Point k
  | .neutral v => (station v,fun c => c.neutral v)
  | .left e => if adjacent g e then (station e.lo,station e.hi) else (fun c => c.dummyA e,fun c => c.dummyB e)
  | .probe v l _ => (localPoint v (fano l).a,localPoint v (fano l).b)

def index (s : Fin 3) (a b : Bool) := if s=0 then a else if s=1 then b else a^^b
def lines (g : Graph k) (q : Query k) (page : Page q) (s : Fin 3) : Point k := fun c =>
  index s ((endpoints g q page).1 c) ((endpoints g q page).2 c)

/-- A left page is fixed before the query arrives. All right pages and
the attached seven-page device are independent of the graph mask. -/
theorem left_query_independent (g : Graph k) (q q' e : Query k) (s : Fin 3) :
    lines g q (.left e) s=lines g q' (.left e) s := rfl

theorem neutral_query_independent (g g' : Graph k) (q q' : Query k) (v : Fin k) (s : Fin 3) :
    lines g q (.neutral v) s=lines g' q' (.neutral v) s := rfl

theorem right_graph_independent (g g' : Graph k) (q : Query k) (v : Fin k) (l : Fin 7)
    (keep : l≠omitted q v) (s : Fin 3) :
    lines g q (.probe v l keep) s=lines g' q (.probe v l keep) s := rfl

private def uniform (s a b : Bool) : Coeffs k := ⟨fun _ => s,fun _ => b,fun _ => a,fun _ => b,fun _ => a,fun _ => b⟩

/-- The two generating points of each chart have rank two: all four pairs
of outputs can be attained by a coordinate functional. -/
theorem independent (g : Graph k) (q : Query k) (p : Page q) (a b : Bool) :
    ∃ env : Coeffs k, (endpoints g q p).1 env=a ∧ (endpoints g q p).2 env=b := by
  cases p with
  | neutral v => exact ⟨uniform a false b,rfl,rfl⟩
  | left e =>
    cases h : adjacent g e with
    | false => exact ⟨uniform false a b,by simp [endpoints,h,uniform],by simp [endpoints,h,uniform]⟩
    | true =>
      have ne : e.hi≠e.lo := by intro eq; have lt:=e.ordered; rw [eq] at lt; omega
      exact ⟨{uniform false a b with site := fun u => if u=e.lo then a else b},
        by simp [endpoints,h,station],by simp [endpoints,h,station,ne]⟩
  | probe v l _ =>
    have span : ∀ (u : Fin 7) (a b : Bool), ∃ s₀ s₁ s₂ : Bool,
        dot3 (fano u).a s₀ s₁ s₂=a ∧ dot3 (fano u).b s₀ s₁ s₂=b := by decide +kernel
    obtain ⟨s₀,s₁,s₂,ha,hb⟩:=span l a b
    exact ⟨uniform s₀ s₁ s₂,ha,hb⟩

theorem nonzero (g : Graph k) (q : Query k) (p : Page q) (s : Fin 3) :
    lines g q p s≠origin := by
  have test : ∀ s : Fin 3, ∃ a b : Bool, index s a b=true := by decide
  obtain ⟨a,b,yes⟩:=test s
  obtain ⟨env,ha,hb⟩:=independent g q p a b
  intro eq
  have h:=congrFun eq env
  change index s ((endpoints g q p).1 env) ((endpoints g q p).2 env)=false at h
  rw [ha,hb,yes] at h
  contradiction

private def flag (q : Query k) : Coeffs k :=
  ⟨fun v => !(picked q v),fun _ => true,fun _ => true,fun _ => false,fun _ => false,fun v => picked q v⟩

private theorem pair_unique (q e : Query k) (a : picked q e.lo=true) (b : picked q e.hi=true) : e=q := by
  have ha := of_decide_eq_true a
  have hb := of_decide_eq_true b
  obtain ⟨u,v,uv⟩:=q
  obtain ⟨r,s,rs⟩:=e
  change r=u ∨ r=v at ha
  change s=u ∨ s=v at hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> first | rfl | omega

private theorem forward (g : Graph k) (q : Query k) (absent : adjacent g q=false) :
    CommonCore.OneOn (lines g q) (fun p => !(p (flag q))) := by
  intro page
  have table : ∀ a b : Bool, (a=true ∨ b=true) →
      ∃ j : Fin 3, ∀ s : Fin 3, (!(index s a b))=decide (s=j) := by decide
  apply table
  cases page with
  | neutral v => right; rfl
  | left e =>
    cases edge : adjacent g e with
    | false => left; simp [endpoints,edge,flag]
    | true =>
      by_cases lo : picked q e.lo=true
      · have hi : picked q e.hi=false := by
          cases h : picked q e.hi
          · rfl
          · have eq:=pair_unique q e lo h
            rw [eq,absent] at edge
            contradiction
        right; simp [endpoints,edge,station,flag,hi]
      · left; simp [endpoints,edge,station,flag,lo]
  | probe v l keep =>
    have finite : ∀ (s : Bool) (l : Fin 7), l≠(if s then 0 else 3) →
        dot3 (fano l).a (!s) false s=true ∨ dot3 (fano l).b (!s) false s=true := by decide +kernel
    exact finite (picked q v) l keep

private def pointWord (l : Fin 7) (s : Fin 3) : Triple :=
  if s=0 then (fano l).a else if s=1 then (fano l).b else (fano l).a^^^(fano l).b

private theorem at_probe (g : Graph k) (q : Query k) (v : Fin k) (l : Fin 7)
    (present : l≠omitted q v) (s : Fin 3) :
    lines g q (.probe v l present) s=localPoint v (pointWord l s) := by
  funext env
  have linear : ∀ (i : Fin 7) (j : Fin 3) (x a b : Bool),
      index j (dot3 (fano i).a x a b) (dot3 (fano i).b x a b) =
      dot3 (pointWord i j) x a b := by decide +kernel
  exact linear l s _ _ _

private theorem weight (y : Fin 3 → Bool) (h : ∃ i, ∀ s, y s=decide (s=i)) :
    (y 0).toNat+(y 1).toNat+(y 2).toNat=1 := by
  obtain ⟨i,spec⟩:=h
  rw [spec 0,spec 1,spec 2]
  have test : ∀ i : Fin 3, (decide (0=i)).toNat+(decide (1=i)).toNat+(decide (2=i)).toNat=1 := by decide
  exact test i

private def total (a b c : Bool) := a.toNat+b.toNat+c.toNat

/-- Omitting the line {1,2,3} forces station 1 to be the selected value.
The finite checks concern seven Boolean values, independently of k. -/
private theorem six_lines (z : Triple → Bool)
    (h : ∀ l : Fin 7, l≠0 → ∃ a, ∀ s, z (pointWord l s)=decide (s=a)) : z 1=true := by
  have rows (l : Fin 7) (keep : l≠0) := weight _ (h l keep)
  have t : ∀ a b c d e f g : Bool, total a d e=1 → total a f g=1 →
      total b d f=1 → total b e g=1 → total c d g=1 → total c e f=1 → a=true := by decide
  exact t (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7)
    (rows 1 (by decide)) (rows 2 (by decide)) (rows 3 (by decide))
    (rows 4 (by decide)) (rows 5 (by decide)) (rows 6 (by decide))

private theorem queried (g : Graph k) (q : Query k) (z : Point k → Bool)
    (ok : CommonCore.OneOn (lines g q) z) (v : Fin k) (sel : picked q v=true) : z (station v)=true := by
  have zOne : localPoint v 1=station v := by funext env; simp [localPoint,station,dot3]
  rw [←zOne]
  apply six_lines (fun u => z (localPoint v u))
  intro l hn
  have present : l≠omitted q v := by simpa [omitted,sel] using hn
  obtain ⟨j,h⟩:=ok (.probe v l present)
  refine ⟨j,fun s => ?_⟩
  rw [←at_probe g q v l present]
  exact h s

theorem choices_iff (g : Graph k) (q : Query k) :
    (∃ z, CommonCore.OneOn (lines g q) z) ↔ adjacent g q=false := by
  constructor
  · rintro ⟨z,ok⟩
    cases edge : adjacent g q with
    | false => rfl
    | true =>
      have lo := queried _ _ _ ok q.lo (by simp [picked])
      have hi := queried _ _ _ ok q.hi (by simp [picked])
      have rows := weight _ (ok (.left q))
      have left : lines g q (.left q) 0=station q.lo := by funext e; simp [lines,endpoints,edge,index]
      have right : lines g q (.left q) 1=station q.hi := by funext e; simp [lines,endpoints,edge,index]
      rw [left,right,lo,hi] at rows
      simp at rows
      omega
  · intro h; exact ⟨_,forward g q h⟩

/-- Each main chart and all seven attachment charts are complete physical
boards. No direction or cell value is prescribed in the instance. -/
theorem boards_iff (g : Graph k) (q : Query k) :
    ThreeFaceAttachment.Feasible origin (lines g q) ↔ ThreeFaceMemory.Join g q :=
  (ThreeFaceAttachment.attached_iff _ _ (nonzero g q)).trans
    ((choices_iff g q).trans (ThreeFaceMemory.join_iff g q).symm)

theorem memo_exact (k states : Nat) :
    (∃ (send : Graph k → Fin states) (answer : Fin states → Query k → Bool),
      ∀ g q, answer (send g) q=true ↔ ThreeFaceAttachment.Feasible origin (lines g q)) ↔
    2^(ThreeFaceMemory.slots k)≤states := by
  simpa only [boards_iff] using ThreeFaceMemory.exact_states k states

end Mobius.ThreeFaceProbeJoin
