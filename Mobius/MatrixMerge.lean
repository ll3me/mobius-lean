import Mobius.OverlapProtocols
import Mobius.AxisCompiler

/-! Two matrix descriptions attach to the same row and column ports.
    All per-cell witnesses and chain carries belong to their own side. -/
namespace Mobius.MatrixMerge

open Mobius.OverlapProtocols

abbrev Mask (k : Nat) := BitVec (k*k)
abbrev Ports (k : Nat) := Fin k → Bool
abbrev Cells (k : Nat) := Fin k → Fin k → Bool

def entry (a : Mask k) (i j : Fin k) := a.getLsbD (i.val*k+j.val)

def indicator (i : Fin k) : Ports k := fun j => decide (j=i)

def One (x y z : Bool) : Prop := x.toNat + y.toNat + z.toNat = 1

/-- An allowed cell disconnects the column wire and uses a private dummy.
    Every cell gets its own last, or slack, port. -/
def Side (a : Mask k) (row col : Ports k) : Prop :=
  ∃ dummy slack : Cells k, ∀ i j, One (row i) (if entry a i j then dummy i j else col j) (slack i j)

theorem side_iff (a : Mask k) (r c : Fin k) :
    Side a (indicator r) (indicator c) ↔ entry a r c = true := by
  constructor
  · rintro ⟨dummy,slack,w⟩
    cases e : entry a r c
    · have bad := w r c
      cases t : slack r c <;> simp [One,e,indicator,t] at bad
    · rfl
  · intro allowed
    let second (i j : Fin k) := if entry a i j then false else indicator c j
    refine ⟨fun _ _ => false,fun i j => !(indicator r i || second i j),fun i j => ?_⟩
    change One (indicator r i) (second i j) (!(indicator r i || second i j))
    have dis : ¬(indicator r i=true ∧ second i j=true) := by
      rintro ⟨row,col⟩
      have ie : i=r := of_decide_eq_true row
      subst i
      cases e : entry a r j
      · have je : j=c := of_decide_eq_true (by simpa [second,e,indicator] using col)
        subst j; simp [allowed] at e
      · simp [second,e] at col
    cases u : indicator r i <;> cases v : second i j <;> simp_all [One]

/-- The two descriptions share precisely the row and column bits in this formula. -/
def Merge (a b : Mask k) : Prop :=
  ∃ row col : Ports k, (∃ r, row=indicator r) ∧ (∃ c, col=indicator c) ∧
    Side a row col ∧ Side b row col

theorem merge_cells (a b : Mask k) :
    Merge a b ↔ ∃ i j : Fin k, entry a i j=true ∧ entry b i j=true := by
  constructor
  · rintro ⟨row,col,⟨i,rfl⟩,⟨j,rfl⟩,left,right⟩
    exact ⟨i,j,(side_iff a i j).mp left,(side_iff b i j).mp right⟩
  · rintro ⟨i,j,left,right⟩
    exact ⟨indicator i,indicator j,⟨i,rfl⟩,⟨j,rfl⟩,(side_iff a i j).mpr left,(side_iff b i j).mpr right⟩

theorem merge_iff (a b : Mask k) : Merge a b ↔ intersects a b := by
  rw [merge_cells]
  constructor
  · rintro ⟨i,j,ha,hb⟩
    have cap := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at cap
    have hj := j.isLt
    exact ⟨⟨i.val*k+j.val,by omega⟩,ha,hb⟩
  · rintro ⟨t,ha,hb⟩
    have hk : 0<k := by
      cases k with
      | zero => exact Fin.elim0 t
      | succ => exact Nat.zero_lt_succ _
    let i : Fin k := ⟨t.val/k,(Nat.div_lt_iff_lt_mul hk).mpr t.isLt⟩
    let j : Fin k := ⟨t.val%k,Nat.mod_lt _ hk⟩
    have ij : i.val*k+j.val=t.val := by
      simpa only [i,j,Nat.add_comm,Nat.mul_comm] using Nat.mod_add_div t.val k
    exact ⟨i,j,by simpa only [entry,ij] using ha,by simpa only [entry,ij] using hb⟩

/-- A positive exact-one pair enforces one step of a one-hot scan.
    The terminal carry is pinned true and the initial carry is pinned false. -/
def Chain (p : α → Bool) : List α → Bool → Prop
  | [], used => used=true
  | i::is, used => ∃ shadow next : Bool, One used (p i) shadow ∧ One shadow next false ∧ Chain p is next

theorem chain_count (p : α → Bool) (xs : List α) (used : Bool) :
    Chain p xs used ↔ used.toNat+(xs.filter p).length=1 := by
  induction xs generalizing used with
  | nil => cases used <;> simp [Chain]
  | cons i is ih =>
    simp only [Chain,Bool.exists_bool,ih]
    cases used <;> cases e : p i <;> simp [List.filter,e,One] <;> omega

theorem chain_indicator (p : Ports k) :
    Chain p (List.finRange k) false ↔ ∃ i, p=indicator i := by
  rw [chain_count]
  simp only [Bool.toNat_false,Nat.zero_add,List.length_eq_one_iff]
  constructor
  · rintro ⟨i,one⟩
    refine ⟨i,funext fun j => Bool.eq_iff_iff.mpr ?_⟩
    have mem : j∈(List.finRange k).filter p ↔ j=i := by rw [one]; simp
    simpa only [List.mem_filter,List.mem_finRange,true_and,indicator,decide_eq_true_eq] using mem
  · rintro ⟨i,rfl⟩
    refine ⟨i,?_⟩
    have hx : ((List.finRange k).filter (indicator i)).Nodup :=
      (List.nodup_finRange k).filter _
    have hi : i ∈ (List.finRange k).filter (indicator i) := by simp [indicator]
    have hs (j) (h : j∈(List.finRange k).filter (indicator i)) : j=i :=
      of_decide_eq_true (List.mem_filter.mp h).2
    generalize eq : (List.finRange k).filter (indicator i) = ys at hx hi hs ⊢
    cases ys with
    | nil => contradiction
    | cons a as =>
      have ae := hs a (by simp)
      subst a
      have tail : as=[] := List.eq_nil_iff_forall_not_mem.mpr (fun v hv =>
        (List.nodup_cons.mp hx).1 ((hs v (by simp [hv])) ▸ hv))
      simp [tail]

def ChainMerge (a b : Mask k) : Prop :=
  ∃ row col : Ports k, Chain row (List.finRange k) false ∧ Chain col (List.finRange k) false ∧
    Side a row col ∧ Side b row col

theorem chain_merge_iff (a b : Mask k) : ChainMerge a b ↔ Merge a b := by
  simp only [ChainMerge,Merge,chain_indicator]

theorem threshold_cost_lower (t : Tree (k*k))
    (correct : ∀ a b, t.run a b=true ↔ ChainMerge a b) :
    ∃ a b, k*k ≤ t.cost a b :=
  matrix_cost_lower k t fun a b => ((correct a b).trans (chain_merge_iff a b)).trans (merge_iff a b)

/-- Alice reveals her bits in the public order. Bob accumulates the
    intersections privately and returns the answer at the leaf. -/
private def reveal (xs : List (Fin n)) (old : BitVec n → Bool) : Tree n :=
  match xs with
  | [] => .halt old
  | i::is => .left (fun x => x.getLsbD i.val) (reveal is old)
      (reveal is (fun y => old y || y.getLsbD i.val))

private theorem reveal_run (xs : List (Fin n)) (old : BitVec n → Bool) (x y : BitVec n) :
    (reveal xs old).run x y = true ↔
      old y=true ∨ ∃ i ∈ xs, x.getLsbD i.val=true ∧ y.getLsbD i.val=true := by
  induction xs generalizing old with
  | nil => simp [reveal,Tree.run]
  | cons i is ih =>
    cases e : x.getLsbD i.val <;> simp only [reveal,Tree.run,e,Bool.false_eq_true,ite_false,ite_true,
      ih,List.mem_cons,Bool.or_eq_true] <;> grind

private theorem reveal_cost (xs : List (Fin n)) (old : BitVec n → Bool) (x y : BitVec n) :
    (reveal xs old).cost x y = xs.length := by
  induction xs generalizing old with
  | nil => rfl
  | cons i is ih => cases e : x.getLsbD i.val <;> simp [reveal,Tree.cost,e,ih]

def thresholdProtocol (k : Nat) : Tree (k*k) := reveal (List.finRange (k*k)) (fun _ => false)

theorem threshold_protocol (k : Nat) (a b : Mask k) :
    ((thresholdProtocol k).run a b=true ↔ ChainMerge a b) ∧ (thresholdProtocol k).cost a b = k*k := by
  constructor
  · rw [chain_merge_iff,merge_iff]
    simpa only [thresholdProtocol,Bool.false_eq_true,false_or,List.mem_finRange,true_and,intersects]
      using reveal_run (List.finRange (k*k)) (fun _ => false) a b
  · simpa only [List.length_finRange,thresholdProtocol] using reveal_cost (List.finRange (k*k)) (fun _ => false) a b

private theorem chain_map (p : β → Bool) (f : α → β) (xs : List α) (u : Bool) :
    Chain p (xs.map f) u ↔ Chain (fun i => p (f i)) xs u := by
  induction xs generalizing u with
  | nil => rfl
  | cons i is ih => simp [Chain,ih]

def Steps (p : Ports k) (carry : Fin (k+1) → Bool) (shadow : Ports k) :=
  ∀ i, One (carry i.castSucc) (p i) (shadow i) ∧ One (shadow i) (carry i.succ) false

private theorem steps_chain {k : Nat} (p : Ports k) (carry : Fin (k+1) → Bool) (shadow : Ports k)
    (rows : Steps p carry shadow) (last : carry (Fin.last k)=true) :
    Chain p (List.finRange k) (carry 0) := by
  induction k with
  | zero => exact last
  | succ k ih =>
    rw [List.finRange_succ]
    refine ⟨shadow 0,carry (0 : Fin (k+1)).succ,(rows 0).1,(rows 0).2,(chain_map ..).mpr ?_⟩
    exact ih (fun i => p i.succ) (fun i => carry i.succ) (fun i => shadow i.succ)
      (fun i => rows i.succ) last

private def carryAt (r : Fin k) (i : Fin (k+1)) := decide (r.val<i.val)
private def shadowAt (r i : Fin k) := decide (i.val<r.val)

private theorem indicator_steps (r : Fin k) : Steps (indicator r) (carryAt r) (shadowAt r) := by
  intro i
  have hi := i.isLt
  rcases Nat.lt_trichotomy i.val r.val with l | e | g
  · have a : ¬r.val<i.val := by omega
    have b : ¬r.val<i.val+1 := by omega
    have c : i≠r := fun h => Nat.ne_of_lt l (congrArg Fin.val h)
    simp [One,indicator,carryAt,shadowAt,Fin.val_succ,c,l,a,b]
  · have same := Fin.ext e
    subst i
    simp [One,indicator,carryAt,shadowAt]
  · have a : ¬i.val<r.val := by omega
    have b : r.val<i.val+1 := by omega
    have c : i≠r := fun h => Nat.ne_of_gt g (congrArg Fin.val h)
    simp [One,indicator,carryAt,shadowAt,Fin.val_succ,c,g,a,b]

/-- A fixed alphabet of physical signal names independent of both private matrices. -/
inductive Wire (k : Nat) where
  | fixed (b : Bool)
  | port (column : Bool) (i : Fin k)
  | carry (column : Bool) (i : Fin (k+1))
  | shadow (column : Bool) (i : Fin k)
  | dummy (right : Bool) (i j : Fin k)
  | slack (right : Bool) (i j : Fin k)
  deriving DecidableEq

abbrev Gate (k : Nat) := Wire k × Wire k × Wire k
def gateSat (v : Wire k → Bool) (g : Gate k) := One (v g.1) (v g.2.1) (v g.2.2)
def satisfy (v : Wire k → Bool) (gates : List (Gate k)) := ∀ g ∈ gates, gateSat v g

private def chainRows (k : Nat) (c : Bool) : List (Gate k) :=
  [(Wire.carry c 0,Wire.carry c 0,Wire.fixed true),
   (Wire.carry c (Fin.last k),Wire.fixed false,Wire.fixed false)] ++
  (List.finRange k).flatMap fun i =>
    [(Wire.carry c i.castSucc,Wire.port c i,Wire.shadow c i),
     (Wire.shadow c i,Wire.carry c i.succ,Wire.fixed false)]

private def cellRows (a : Mask k) (s : Bool) : List (Gate k) :=
  (List.finRange k).flatMap fun i => (List.finRange k).map fun j =>
    (Wire.port false i,if entry a i j then Wire.dummy s i j else Wire.port true j,Wire.slack s i j)

/-- A complete positive three-literal row table. Only the cell rows on
    their own side vary with the two players' inputs. -/
def sourceRows (a b : Mask k) : List (Gate k) :=
  [(Wire.fixed false,Wire.fixed false,Wire.fixed true)] ++
  chainRows k false ++ chainRows k true ++ cellRows a false ++ cellRows b true

private theorem sat_append (v : Wire k → Bool) (l m : List (Gate k)) :
    satisfy v (l++m) ↔ satisfy v l ∧ satisfy v m := by simp [satisfy,List.mem_append,or_imp,forall_and]

private theorem sat_cons (v : Wire k → Bool) (g : Gate k) (l : List (Gate k)) :
    satisfy v (g::l) ↔ gateSat v g ∧ satisfy v l := by simp [satisfy,List.mem_cons,or_imp,forall_and]
private theorem sat_nil (v : Wire k → Bool) : satisfy v [] := by simp [satisfy]
private theorem sat_flat (v : Wire k → Bool) (xs : List α) (f : α → List (Gate k)) :
    satisfy v (xs.flatMap f) ↔ ∀ x∈xs, satisfy v (f x) := by
  constructor
  · exact fun h x hx y hy => h y (List.mem_flatMap.mpr ⟨x,hx,hy⟩)
  · intro h y hy; obtain ⟨x,hx,e⟩ := List.mem_flatMap.mp hy; exact h x hx y e
private theorem sat_map (v : Wire k → Bool) (xs : List α) (f : α → Gate k) :
    satisfy v (xs.map f) ↔ ∀ x∈xs, gateSat v (f x) := by
  constructor
  · exact fun h x hx => h _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
  · intro h y hy; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy; exact h x hx

private theorem sat_chain (v : Wire k → Bool) (c : Bool) (fixed : ∀ b, v (.fixed b)=b) :
    satisfy v (chainRows k c) ↔ v (.carry c 0)=false ∧ v (.carry c (Fin.last k))=true ∧
        Steps (fun i => v (.port c i)) (fun i => v (.carry c i)) (fun i => v (.shadow c i)) := by
  have fst (b : Bool) : One b b true ↔ b=false := by cases b <;> simp [One]
  have lst (b : Bool) : One b false false ↔ b=true := by cases b <;> simp [One]
  simp only [chainRows,sat_append,sat_cons,sat_nil,and_true,sat_flat,List.mem_finRange,true_implies,gateSat,fixed,fst,lst,Steps,and_assoc]

private theorem sat_cells (v : Wire k → Bool) (a : Mask k) (s : Bool) :
    satisfy v (cellRows a s) ↔ ∀ i j, One (v (.port false i))
      (if entry a i j then v (.dummy s i j) else v (.port true j)) (v (.slack s i j)) := by
  simp only [cellRows,sat_flat,sat_map,List.mem_finRange,true_implies,gateSat,apply_ite v]

private theorem pins (f t : Bool) : One f f t ↔ f=false ∧ t=true := by cases f <;> cases t <;> simp [One]

theorem source_iff (a b : Mask k) : (∃ v, satisfy v (sourceRows a b)) ↔ Merge a b := by
  constructor
  · rintro ⟨v,h⟩
    simp only [sourceRows,sat_append] at h
    obtain ⟨⟨⟨⟨pin,r⟩,c⟩,left⟩,right⟩ := h
    have cp := (pins ..).mp (pin (.fixed false,.fixed false,.fixed true) (by simp))
    have fixed (t : Bool) : v (.fixed t)=t := by cases t <;> simp [cp]
    have hot (s : Bool) (g : satisfy v (chainRows k s)) :
        ∃ i, (fun j => v (.port s j))=indicator i := by
      obtain ⟨start,ends,step⟩ := (sat_chain v s fixed).mp g
      apply (chain_indicator _).mp
      simpa only [start] using steps_chain _ _ _ step ends
    exact ⟨_,_,hot false r,hot true c,
      ⟨_,_,(sat_cells ..).mp left⟩,⟨_,_,(sat_cells ..).mp right⟩⟩
  · rintro ⟨row,col,⟨i,rfl⟩,⟨j,rfl⟩,⟨ld,ls,lh⟩,⟨rd,rs,rh⟩⟩
    let pick (c : Bool) := if c then j else i
    let v : Wire k → Bool
      | .fixed t => t
      | .port c t => indicator (pick c) t
      | .carry c t => carryAt (pick c) t
      | .shadow c t => shadowAt (pick c) t
      | .dummy s x y => if s then rd x y else ld x y
      | .slack s x y => if s then rs x y else ls x y
    have chain (c : Bool) : satisfy v (chainRows k c) := by
      apply (sat_chain v c (fun _ => rfl)).mpr
      exact ⟨by simp [v,carryAt],by simp [v,carryAt],indicator_steps _⟩
    refine ⟨v,?_⟩
    simp only [sourceRows,sat_append]
    refine ⟨⟨⟨⟨?_,chain false⟩,chain true⟩,(sat_cells ..).mpr lh⟩,(sat_cells ..).mpr rh⟩
    simp [satisfy,gateSat,v,One]

def rowCount (k : Nat) := 5+4*k+2*(k*k)

theorem source_size (a b : Mask k) : (sourceRows a b).length = rowCount k := by
  simp [sourceRows,chainRows,cellRows,List.length_flatMap,List.map_const',List.sum_replicate_nat,rowCount]
  omega

private def sideWires (k : Nat) (s : Bool) : List (Wire k) :=
  (List.finRange k).map (.port s) ++ (List.finRange (k+1)).map (.carry s) ++
  (List.finRange k).map (.shadow s) ++
  (List.finRange k).flatMap (fun i => (List.finRange k).map (.dummy s i)) ++
  (List.finRange k).flatMap (fun i => (List.finRange k).map (.slack s i))

def wires (k : Nat) : List (Wire k) := [.fixed false,.fixed true] ++ sideWires k false ++ sideWires k true

private theorem wire_mem (w : Wire k) : w ∈ wires k := by
  cases w with
  | fixed b => cases b <;> simp [wires]
  | port b i | carry b i | shadow b i => cases b <;> simp [wires,sideWires]
  | dummy b i j | slack b i j => cases b <;> simp [wires,sideWires]

def varCount (k : Nat) := (wires k).length

theorem var_count (k : Nat) : varCount k = 4+6*k+4*(k*k) := by
  simp [varCount,wires,sideWires,List.length_flatMap,List.map_const',List.sum_replicate_nat]
  omega

def code (w : Wire k) : Fin (varCount k) :=
  ⟨(wires k).idxOf w,List.idxOf_lt_length_of_mem (wire_mem w)⟩

private def literal (g : Gate k) (j : Fin 3) : Wire k :=
  if j.val=0 then g.1 else if j.val=1 then g.2.1 else g.2.2

def src (a b : Mask k) (i : Fin (rowCount k)) (j : Fin 3) : Fin (varCount k) :=
  code (literal ((sourceRows a b)[i.val]'((source_size a b).symm ▸ i.isLt)) j)

theorem src_iff (a b : Mask k) :
    (∃ z : Fin (varCount k) → Bool, ∀ i,
      One (z (src a b i 0)) (z (src a b i 1)) (z (src a b i 2))) ↔ Merge a b := by
  rw [← source_iff]
  constructor
  · rintro ⟨z,all⟩
    refine ⟨fun w => z (code w),fun g hg => ?_⟩
    obtain ⟨u,hu,rfl⟩ := List.mem_iff_getElem.mp hg
    exact all ⟨u,(source_size a b) ▸ hu⟩
  · rintro ⟨v,h⟩
    let z (u : Fin (varCount k)) := v ((wires k).get u)
    have readCode (w : Wire k) : z (code w)=v w :=
      congrArg v (List.getElem_idxOf (List.idxOf_lt_length_of_mem (wire_mem w)))
    refine ⟨z,fun i => ?_⟩
    let g := (sourceRows a b)[i.val]'((source_size a b).symm ▸ i.isLt)
    have hg : g ∈ sourceRows a b := List.getElem_mem _
    change One (z (code g.1)) (z (code g.2.1)) (z (code g.2.2))
    simpa only [readCode,gateSat] using h g hg

/-- The total weighted cost is measured on one pair of actual ambient
    tables, using the concrete compiled row list. -/
def WeightedMerge (a b : Mask k) : Prop :=
  ∃ r c : AxisGlue.World (varCount k+19*rowCount k),
    AxisNetwork.cost (AxisCompiler.atlas (src a b)) (AxisCompiler.ports (rowCount k))
      AxisPortCost.weighted r c ≤ (7*rowCount k)*2300

theorem weighted_merge_iff (a b : Mask k) : WeightedMerge a b ↔ Merge a b :=
  (AxisCompiler.weighted_iff (src a b)).trans (src_iff a b)

theorem weighted_cost_lower (t : Tree (k*k))
    (correct : ∀ a b, t.run a b=true ↔ WeightedMerge a b) :
    ∃ a b, k*k ≤ t.cost a b :=
  matrix_cost_lower k t fun a b => ((correct a b).trans (weighted_merge_iff a b)).trans (merge_iff a b)

theorem weighted_protocol (a b : Mask k) :
    ((thresholdProtocol k).run a b=true ↔ WeightedMerge a b) ∧ (thresholdProtocol k).cost a b=k*k :=
  ⟨(((threshold_protocol k a b).1.trans (chain_merge_iff a b)).trans (weighted_merge_iff a b).symm),
    (threshold_protocol k a b).2⟩

def UnweightedMerge (a b : Mask k) : Prop :=
  ∃ r c : AxisGlue.World (varCount k+19*rowCount k),
    AxisNetwork.cost (AxisCompiler.atlas (src a b)) (AxisCompiler.ports (rowCount k))
      AxisPortCost.geometricRetained r c ≤ (7*rowCount k)*126

theorem unweighted_merge_iff (gap : AxisPortCost.Gap282) (a b : Mask k) :
    UnweightedMerge a b ↔ Merge a b :=
  (AxisCompiler.geometric_iff gap (src a b)).trans (src_iff a b)

theorem unweighted_cost_lower (gap : AxisPortCost.Gap282) (t : Tree (k*k))
    (correct : ∀ a b, t.run a b=true ↔ UnweightedMerge a b) :
    ∃ a b, k*k ≤ t.cost a b :=
  matrix_cost_lower k t fun a b => ((correct a b).trans (unweighted_merge_iff gap a b)).trans (merge_iff a b)

theorem unweighted_protocol (gap : AxisPortCost.Gap282) (a b : Mask k) :
    ((thresholdProtocol k).run a b=true ↔ UnweightedMerge a b) ∧ (thresholdProtocol k).cost a b=k*k :=
  ⟨(((threshold_protocol k a b).1.trans (chain_merge_iff a b)).trans (unweighted_merge_iff gap a b).symm),
    (threshold_protocol k a b).2⟩

def leftRows (a : Mask k) : List (Gate k) :=
  [(Wire.fixed false,Wire.fixed false,Wire.fixed true)] ++
  chainRows k false ++ chainRows k true ++ cellRows a false

def rightRows (b : Mask k) : List (Gate k) := cellRows b true

theorem source_split (a b : Mask k) : sourceRows a b = leftRows a ++ rightRows b := rfl

private def belongs (s : Bool) : Wire k → Bool
  | .fixed _ | .carry _ _ | .shadow _ _ => !s
  | .port _ _ => true
  | .dummy t _ _ | .slack t _ _ => s==t

private def gateLocal (s : Bool) (g : Gate k) :=
  belongs s g.1=true ∧ belongs s g.2.1=true ∧ belongs s g.2.2=true

private theorem local_chain (c : Bool) : ∀ g∈chainRows k c, gateLocal false g := by
  simp only [chainRows,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_flatMap,
    List.not_mem_nil,false_implies,gateLocal,belongs,Bool.not_false,true_and,implies_true]

private theorem local_cells (a : Mask k) (s : Bool) : ∀ g∈cellRows a s, gateLocal s g := by
  simp only [cellRows,List.forall_mem_flatMap,List.forall_mem_map,gateLocal]
  intro i _ j _
  cases e : entry a i j <;> simp [belongs]

private theorem halves_local (a b : Mask k) :
    (∀ g∈leftRows a, gateLocal false g) ∧ (∀ g∈rightRows b, gateLocal true g) := by
  refine ⟨?_,local_cells b true⟩
  simp only [leftRows,List.forall_mem_append]
  refine ⟨⟨⟨?_,local_chain false⟩,local_chain true⟩,local_cells a false⟩
  intro g hg; obtain rfl := List.mem_singleton.mp hg; exact ⟨rfl,rfl,rfl⟩

def Occurs (w : Wire k) (l : List (Gate k)) := ∃ g ∈ l, w=g.1 ∨ w=g.2.1 ∨ w=g.2.2

private theorem wire_local {s : Bool} {w : Wire k} {l : List (Gate k)}
    (all : ∀ g∈l, gateLocal s g) (mem : Occurs w l) : belongs s w=true := by
  obtain ⟨g,h,rfl|rfl|rfl⟩ := mem
  · exact (all _ h).1
  · exact (all _ h).2.1
  · exact (all _ h).2.2

theorem common_wire {a b : Mask k} {w : Wire k} (left : Occurs w (leftRows a))
    (right : Occurs w (rightRows b)) : ∃ c i, w=Wire.port c i := by
  have hl := wire_local (halves_local a b).1 left
  have hr := wire_local (halves_local a b).2 right
  cases w with
  | port c i => exact ⟨c,i,rfl⟩
  | fixed | carry | shadow => contradiction
  | dummy s i j | slack s i j => cases s <;> contradiction

/-- A fixed list of the at most 2k original variable indices shared by the
    two compiled descriptions. The tests still act on full world tables. -/
def publicPorts (k : Nat) :=
  ((List.finRange k).map fun i => code (Wire.port false i)) ++
  ((List.finRange k).map fun i => code (Wire.port true i))

theorem public_size (k : Nat) : (publicPorts k).length = 2*k := by simp [publicPorts,Nat.two_mul]

private theorem code_inj {w t : Wire k} (h : code w=code t) : w=t := by
  have read (u : Wire k) : (wires k).get (code u)=u := List.getElem_idxOf (List.idxOf_lt_length_of_mem (wire_mem u))
  exact (read w).symm.trans ((congrArg (wires k).get h).trans (read t))

theorem public_separator {a b : Mask k} {u w : Wire k} (hl : Occurs u (leftRows a))
    (hr : Occurs w (rightRows b)) (same : code u=code w) : code u∈publicPorts k := by
  have eq := code_inj same
  subst w
  obtain ⟨s,i,rfl⟩ := common_wire hl hr
  cases s <;> simp [publicPorts]

def leftCount (k : Nat) := 5+4*k+k*k

theorem left_size (a : Mask k) : (leftRows a).length=leftCount k := by
  simp [leftRows,chainRows,cellRows,List.length_flatMap,List.map_const',List.sum_replicate_nat,leftCount]
  omega

theorem src_left_local (a b b' : Mask k) (i : Fin (rowCount k)) (j : Fin 3)
    (hi : i.val<leftCount k) : src a b i j = src a b' i j := by
  have h : i.val<(leftRows a).length := (left_size a).symm ▸ hi
  simp only [src,source_split,List.getElem_append_left h]

theorem src_right_local (a a' b : Mask k) (i : Fin (rowCount k)) (j : Fin 3)
    (hi : leftCount k≤i.val) : src a b i j = src a' b i j := by
  have h : (leftRows a).length≤i.val := (left_size a).symm ▸ hi
  have h' : (leftRows a').length≤i.val := (left_size a').symm ▸ hi
  simp only [src,source_split,List.getElem_append_right h,List.getElem_append_right h',left_size]

end Mobius.MatrixMerge
