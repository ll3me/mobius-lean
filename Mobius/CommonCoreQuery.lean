import Mobius.CommonCoreSignature
import Mobius.Bounded

/-! An indexed extension problem on a connected family. Three distinct
    3D stations of each central board are shared with other full boards
    for n≥2. Inputs pin just eight actual tagged cells per exposed station. -/
namespace Mobius.CommonCoreQuery
open CommonCore (Table Addr Profiles)
open CommonCoreSignature (signature rowBit colBit toggleRow toggleCol)
open SignObstruction (B)

inductive Point (n : Nat) where
  | origin | hub
  | marked (i : Fin n) | clear (i : Fin n)
  | a (i : Fin n) | sa (i : Fin n)
  | b (i : Fin n) | ub (i : Fin n)
  deriving DecidableEq

inductive Board (n : Nat) where
  | center (i : Fin n) | left (i : Fin n) | right (i : Fin n)

def triple (a b c : α) (j : Fin 3) := if j=0 then a else if j=1 then b else c

def line : Board n → Fin 3 → Point n
  | .center i => triple .hub (.marked i) (.clear i)
  | .left i => triple (.marked i) (.a i) (.sa i)
  | .right i => triple (.clear i) (.b i) (.ub i)

def mark : Point n → Bool
  | .marked _ | .b _ => true
  | _ => false

def shift (x : BitVec n) : Point n → Bool
  | .marked i | .clear i | .sa i | .ub i => x.getLsbD i.val
  | _ => false

private theorem three (s : Fin 3) : s=0 ∨ s=1 ∨ s=2 := by omega

private theorem off (i : Board n) (j : Fin 3) : line i j ≠ .origin := by
  rcases three j with rfl|rfl|rfl <;> cases i <;> simp [line,triple]

private theorem one (n : Nat) : CommonCore.OneOn (@line n) mark := by
  intro b
  cases b with
  | center i => refine ⟨1,fun j => ?_⟩; rcases three j with rfl|rfl|rfl <;> rfl
  | left i => refine ⟨0,fun j => ?_⟩; rcases three j with rfl|rfl|rfl <;> rfl
  | right i => refine ⟨1,fun j => ?_⟩; rcases three j with rfl|rfl|rfl <;> rfl

private theorem even (x : BitVec n) (b : Board n) :
    (shift x (line b 0) ^^ shift x (line b 1) ^^ shift x (line b 2))=false := by
  cases b with
  | center i | left i | right i => simp [line,triple,shift]

def pointAt (o p : P) (bit : Bool) : Addr P := (0,if bit then p else o)
def tileVal (marked v side x y : Bool) := (!marked && x && y) ^^ (v && x && (y ^^ side))

/-- All eight values of the two named physical 2×2 tables. -/
def Tile (o p : P) (marked v : Bool) (r c : Table P) := ∀ x y : Bool,
  r (pointAt o p x) (pointAt o p y)=tileVal marked v false x y ∧
  c (pointAt o p x) (pointAt o p y)=tileVal marked v true x y

private theorem tile_sig (o p : P) (m v : Bool) (r c : Table P) (h : Tile o p m v r c) :
    signature o p r=(!m ^^ v) := by
  unfold signature
  change (r (pointAt o p false) (pointAt o p false) ^^ r (pointAt o p false) (pointAt o p true) ^^
     r (pointAt o p true) (pointAt o p false) ^^ r (pointAt o p true) (pointAt o p true)) = _
  rw [(h false false).1,(h false true).1,(h true false).1,(h true true).1]
  cases m <;> cases v <;> rfl

private theorem tile_bad (o p : P) (v : Bool) (r c : Table P) (h : Tile o p true v r c) :
    CommonCore.probe o p r c 0=false := by
  change (r (pointAt o p false) (pointAt o p false) ^^ (r (pointAt o p true) (pointAt o p true) ^^
     (c (pointAt o p false) (pointAt o p true) ^^ c (pointAt o p true) (pointAt o p false))))=false
  rw [(h false false).1,(h true true).1,(h false true).2,(h true false).2]
  cases v <;> rfl

private def refTable (n : Nat) : Table (Point n) := CommonCore.world .origin mark
private def witnessR (x : BitVec n) := toggleRow (refTable n) (shift x)
private def witnessC (x : BitVec n) := toggleCol (refTable n) (shift x)

private theorem witness_tile (x : BitVec n) (p : Point n) (ne : p≠.origin) :
    Tile .origin p (mark p) (shift x p) (witnessR x) (witnessC x) := by
  have so : shift x .origin=false := rfl
  intro u v
  cases u <;> cases v <;> cases marked : mark p <;> cases val : shift x p <;>
    simp [witnessR,witnessC,refTable,toggleRow,toggleCol,CommonCore.world,CommonCore.image,
      pointAt,tileVal,rowBit,colBit,marked,val,ne,so] <;> rfl

private theorem witnesses (x : BitVec n) : Profiles Point.origin line (witnessR x) (witnessC x) := by
  intro b
  obtain ⟨a,_,base⟩ := CommonCore.realize_choice Point.origin line off mark (one n) b
  have outside : ∀ s : Fin 3, 4≤(CommonCore.lift s 0).toNat := by decide
  refine ⟨CommonCore.lift a 0,outside a,base.1,fun i j e he => ?_⟩
  rw [witnessR,witnessC,CommonCoreSignature.toggle_score _ _ _ _ (shift x) rfl (even x b)]
  exact base.2 i j e he

/-- Each board is locally optimal, with its bad direction existentially
    quantified. The observer knows the index and pins the output tile. -/
def Fits (x : BitVec n) (q : Fin n) (wanted : Bool) (r c : Table (Point n)) :=
    (∀ b, ∃ d : B, Rigidity.DirectionPattern (CommonCore.restrict r .origin (line b))
      (CommonCore.restrict c .origin (line b)) d) ∧
    Tile .origin .hub false false r c ∧
    (∀ i, Tile .origin (.marked i) true (x.getLsbD i.val) r c) ∧
    Tile .origin (.clear q) false wanted r c

def Extends (x : BitVec n) (q : Fin n) (wanted : Bool) :=
  ∃ r c : Table (Point n), Fits x q wanted r c

theorem query_iff (x : BitVec n) (q : Fin n) (wanted : Bool) :
    Extends x q wanted ↔ x.getLsbD q.val=wanted := by
  constructor
  · rintro ⟨r,c,boards,hub,marks,out⟩
    obtain ⟨d,h⟩ := boards (.center q)
    have pin := tile_bad _ _ _ _ _ (marks q)
    have read := CommonCore.read_probe Point.origin (line (.center q)) r c 1 0
    change TwoPhases.score _ _ (0,0,8)=CommonCore.probe Point.origin (.marked q) r c 0 at read
    have atEight := (h.2 0 0 8 (by decide)).symm.trans (read.trans pin)
    have eq : (8:B)=d := by simpa using atEight
    have obs := CommonCoreSignature.station_law Point.origin (line (.center q)) r c d h
    change (signature Point.origin .hub r ^^ signature Point.origin (.marked q) r ^^
      signature Point.origin (.clear q) r)=_ at obs
    rw [←eq,tile_sig _ _ _ _ _ _ hub,tile_sig _ _ _ _ _ _ (marks q),tile_sig _ _ _ _ _ _ out] at obs
    cases bit : x.getLsbD q.val <;> cases wanted <;> simp_all
  · intro yes
    refine ⟨witnessR x,witnessC x,fun b => ?_,witness_tile x .hub (by intro h; contradiction),fun i => ?_,?_⟩
    · obtain ⟨d,_,h⟩ := witnesses x b; exact ⟨d,h⟩
    · exact witness_tile x (.marked i) (by intro h; contradiction)
    · rw [←yes]; exact witness_tile x (.clear q) (by intro h; contradiction)

theorem states_lower (send : BitVec n → Fin states) (readout : Fin states → Fin n → Bool)
    (ok : ∀ x q, readout (send x) q=true ↔ Extends x q true) : 2^n≤states := by
  apply Bounded.fin_size_le (fun z : Fin (2^n) => send (.ofFin z))
  intro a b eq
  apply congrArg BitVec.toFin
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  apply Bool.eq_iff_iff.mpr
  have l := ((ok (.ofFin a) ⟨i,hi⟩).trans (query_iff ..)).symm
  rw [eq] at l
  exact l.trans ((ok (.ofFin b) ⟨i,hi⟩).trans (query_iff ..))

theorem bits_exact (n : Nat) :
    (∃ send : BitVec n → BitVec n, ∃ readout : BitVec n → Fin n → Bool,
      ∀ x q, readout (send x) q=true ↔ Extends x q true) ∧
    (∀ b (send : BitVec n → BitVec b) (readout : BitVec b → Fin n → Bool),
      (∀ x q, readout (send x) q=true ↔ Extends x q true) → n≤b) := by
  refine ⟨⟨id,fun x q => x.getLsbD q.val,fun x q => (query_iff x q true).symm⟩,?_⟩
  intro b send readout ok
  have cap := states_lower (fun x => (send x).toFin) (fun u => readout (.ofFin u)) ok
  exact Nat.le_of_not_lt (fun h => Nat.not_lt_of_ge cap (Nat.pow_lt_pow_right (by decide : 1<2) h))

/-- A concrete binary ambient realization. The hub uses one independent
    bit. At index i the marked point and two private leaf points use the
    three independent axes 1,2,4 in a private BitVec 3 block. -/
abbrev Carrier (n : Nat) := Bool × (Fin n → BitVec 3)
def spike (i : Fin n) (a : BitVec 3) : Fin n → BitVec 3 := fun j => if j=i then a else 0
def coords : Point n → Carrier n
  | .origin => (false,fun _ => 0)
  | .hub => (true,fun _ => 0)
  | .marked i => (false,spike i 1)
  | .clear i => (true,spike i 1)
  | .a i => (false,spike i 2)
  | .sa i => (false,spike i 3)
  | .b i => (false,spike i 4)
  | .ub i => (true,spike i 5)

private theorem spike_eq {i j : Fin n} {a b : BitVec 3} (nz : a≠0) :
    spike i a=spike j b ↔ i=j ∧ a=b := by
  constructor
  · intro eq
    have v := congrFun eq i
    by_cases same : i=j
    · subst j; exact ⟨rfl,by simpa [spike] using v⟩
    · simp [spike,same] at v; contradiction
  · rintro ⟨rfl,rfl⟩; rfl

private theorem spike_ne_zero (i : Fin n) {a : BitVec 3} (nz : a≠0) : spike i a ≠ fun _ => 0 := by
  intro eq; have v := congrFun eq i; simp [spike] at v; contradiction

theorem coords_injective {p q : Point n} (eq : coords p=coords q) : p=q := by
  have nonzero : ∀ a : BitVec 3, a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 → a≠0 := by decide
  have h1 := nonzero 1 (by decide)
  have h2 := nonzero 2 (by decide)
  have h3 := nonzero 3 (by decide)
  have h4 := nonzero 4 (by decide)
  have h5 := nonzero 5 (by decide)
  cases p <;> cases q <;>
    simp_all [coords,spike_eq]
  all_goals first | exact spike_ne_zero _ (by decide) eq | exact spike_ne_zero _ (by decide) eq.symm

def addCoord (a b : Carrier n) : Carrier n := (a.1 ^^ b.1,fun j => a.2 j ^^^ b.2 j)

theorem quotient_line (b : Board n) :
    addCoord (coords (line b 0)) (coords (line b 1))=coords (line b 2) := by
  cases b with
  | center i | left i | right i =>
    apply Prod.ext
    · rfl
    · funext j; by_cases same : j=i <;> simp [coords,line,triple,spike,addCoord,same]

theorem distinct_points (b : Board n) (u v : Fin 3) (diff : u≠v) : line b u ≠ line b v := by
  rcases three u with rfl|rfl|rfl <;> rcases three v with rfl|rfl|rfl <;> cases b <;> simp_all [line,triple]

theorem all_three_shared (enough : 2≤n) (i : Fin n) (s : Fin 3) :
    ∃ b : Board n, b≠.center i ∧ ∃ j, line (.center i) s=line b j := by
  rcases three s with rfl|rfl|rfl
  · have other : ∃ j : Fin n, j≠i := by
      let z : Fin n := ⟨0,by omega⟩
      by_cases eq : i=z
      · exact ⟨⟨1,by omega⟩,fun h => by have v := congrArg Fin.val (h.trans eq); contradiction⟩
      · exact ⟨z,Ne.symm eq⟩
    obtain ⟨j,ne⟩ := other
    exact ⟨.center j,fun h => ne (Board.center.inj h),0,rfl⟩
  · exact ⟨.left i,by intro h; contradiction,0,rfl⟩
  · exact ⟨.right i,by intro h; contradiction,0,rfl⟩

/-- Tables here are defined on every vector in the binary ambient space,
    including all unqueried points outside the listed boards. -/
def pullAmbient (r : Table (Carrier n)) : Table (Point n) :=
  fun x y => r (x.1,coords x.2) (y.1,coords y.2)

def PhysicalExtends (x : BitVec n) (q : Fin n) (wanted : Bool) :=
  ∃ r c : Table (Carrier n), Fits x q wanted (pullAmbient r) (pullAmbient c)

private noncomputable def unplace (z : Carrier n) : Point n := by
  classical
  exact if h : ∃ p, coords p=z then Classical.choose h else .origin

private theorem unplace_coords (p : Point n) : unplace (coords p)=p := by
  classical
  have yes : ∃ q, coords q=coords p := ⟨p,rfl⟩
  simpa only [unplace,dite_eq_left yes] using coords_injective (Classical.choose_spec yes)

theorem physical_query_iff (x : BitVec n) (q : Fin n) (wanted : Bool) :
    PhysicalExtends x q wanted ↔ x.getLsbD q.val=wanted := by
  rw [←query_iff]
  constructor
  · rintro ⟨r,c,h⟩; exact ⟨_,_,h⟩
  · rintro ⟨r,c,h⟩
    let extend (t : Table (Point n)) : Table (Carrier n) :=
      fun a b => t (a.1,unplace a.2) (b.1,unplace b.2)
    have back (t : Table (Point n)) : pullAmbient (extend t)=t := by
      funext a b; simp [pullAmbient,extend,unplace_coords]
    exact ⟨extend r,extend c,by simpa only [back] using h⟩

theorem physical_bits_exact (n : Nat) :
    (∃ send : BitVec n → BitVec n, ∃ readout : BitVec n → Fin n → Bool,
      ∀ x q, readout (send x) q=true ↔ PhysicalExtends x q true) ∧
    (∀ b (send : BitVec n → BitVec b) (readout : BitVec b → Fin n → Bool),
      (∀ x q, readout (send x) q=true ↔ PhysicalExtends x q true) → n≤b) := by
  simpa only [physical_query_iff,query_iff] using bits_exact n

end Mobius.CommonCoreQuery
