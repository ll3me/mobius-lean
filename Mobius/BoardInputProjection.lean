import Mobius.GraphCoverSource
import Mobius.ReadRestriction

/-! Literal serialization of the capped atlas: board order, four axes in
order, and little-endian coordinate fields. A proposed vertex-cover bit
appears at one distinct coordinate least-significant bit. -/
namespace Mobius.BoardInputProjection
open Mobius.AxisGlue (Axis)
open Mobius.AxisCompiler (Source)
open Mobius.GraphCoverSource (Edges source rows vars inputRow)

def boards (r v : Nat) := 7*r+(v+6*r)
def dimension (r v : Nat) := (v+19*r)+3*(v+6*r)
def width (r v : Nat) := (dimension r v-1).log2+1
abbrev Location (r v : Nat) := Fin (boards r v) × Axis

def address (f : Source r v) (p : Location r v) : Nat := ((CapAtlas.compiled f).loc p.1 p.2).val

theorem address_fits (f : Source r v) (p : Location r v) : address f p < 2^width r v := by
  have h : address f p < dimension r v := ((CapAtlas.compiled f).loc p.1 p.2).isLt
  have maxV := Nat.lt_log2_self (n:=dimension r v-1)
  unfold width; omega

private def terminal (j : Fin 3) : AxisCompiler.Tag := ⟨4+j.val,by omega⟩

def occurrence (v : Nat) (i : Fin r) (j : Fin 3) : Location r v :=
  ((AxisCompiler.board i (terminal j)).castAdd (v+6*r),1)

private theorem ends : ∀ j, AxisCompiler.shape (terminal j) 1=0 ∧ AxisCompiler.sourceSlot (terminal j)=j := by decide
private theorem only_ends : ∀ s a, AxisCompiler.shape s a=0 → terminal (AxisCompiler.sourceSlot s)=s ∧ a=1 := by decide

theorem occurrence_address (f : Source r v) (i : Fin r) (j : Fin 3) :
    address f (occurrence v i j) = (f i j).val := by
  unfold address occurrence CapAtlas.compiled
  rw [CapAtlas.core_loc]
  simp only [CapAtlas.coreCoord,Fin.val_castAdd,AxisCompiler.atlas,AxisCompiler.row_board,AxisCompiler.tag_board,
    AxisCompiler.locate,(ends j).1,(ends j).2,ite_true,AxisCompiler.original]

theorem occurrence_injective {i i' : Fin r} {j j' : Fin 3}
    (eq : occurrence v i j=occurrence v i' j') : i=i' ∧ j=j' := by
  have h := congrArg (fun p : Location r v => p.1.val) eq
  change 7*i.val+(4+j.val)=7*i'.val+(4+j'.val) at h
  exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩

/-- Every coordinate which can change between two compiled descriptions is
the unique terminal occurrence assigned to the changing source address. -/
theorem changed_location (f g : Source r v) (p : Location r v)
    (different : address f p≠address g p) :
    ∃ i j, p=occurrence v i j ∧ f i j≠g i j := by
  rcases p with ⟨b,a⟩
  change Fin (7*r+(v+6*r)) at b
  induction b using Fin.addCases with
  | right cap =>
    exfalso; apply different
    simp only [address,CapAtlas.compiled,CapAtlas.cap_loc]
  | left core =>
    let i := AxisCompiler.row core
    let s := AxisCompiler.tag core
    by_cases on : AxisCompiler.shape s a=0
    · obtain ⟨tag,slot⟩ := only_ends _ _ on
      have loc : (core.castAdd (v+6*r),a)=occurrence v i (AxisCompiler.sourceSlot s) := by
        unfold occurrence
        rw [tag,slot,show AxisCompiler.board i s=core from AxisCompiler.board_row_tag core]
        rfl
      refine ⟨i,AxisCompiler.sourceSlot s,loc,fun same => different ?_⟩
      exact (congrArg (address f) loc).trans ((occurrence_address f _ _).trans
        ((congrArg Fin.val same).trans ((occurrence_address g _ _).symm.trans (congrArg (address g) loc).symm)))
    · exfalso; apply different
      simp only [address,CapAtlas.compiled,CapAtlas.core_loc,CapAtlas.coreCoord,Fin.val_castAdd,
        AxisCompiler.atlas,AxisCompiler.locate,show AxisCompiler.shape (AxisCompiler.tag core) a≠0 from on,ite_false]

/-- Mixed-radix indexing for a row-major serialized bit vector. -/
def pack (i : Fin n) (j : Fin w) : Fin (n*w) := ⟨i.val*w+j.val,by
  have first := Nat.add_lt_add_left j.isLt (i.val*w)
  have endRow := Nat.mul_le_mul_right w i.isLt
  rw [Nat.succ_mul] at endRow; omega⟩

private def group (i : Fin (n*w)) (pos : 0<w) : Fin n := ⟨i.val/w,(Nat.div_lt_iff_lt_mul pos).mpr i.isLt⟩
private def lane (i : Fin (n*w)) (pos : 0<w) : Fin w := ⟨i.val%w,Nat.mod_lt _ pos⟩

private theorem group_pack (i : Fin n) (j : Fin w) (pos) : group (pack i j) pos=i := by
  apply Fin.ext; change (i.val*w+j.val)/w=i.val
  rw [Nat.mul_comm i.val w,Nat.mul_add_div pos,Nat.div_eq_of_lt j.isLt,Nat.add_zero]

private theorem lane_pack (i : Fin n) (j : Fin w) (pos) : lane (pack i j) pos=j :=
  Fin.ext (Nat.mul_add_mod_of_lt j.isLt)

private theorem pack_group (i : Fin (n*w)) (pos) : pack (group i pos) (lane i pos)=i :=
  Fin.ext (Nat.div_add_mod' _ _)

def bitCount (r v : Nat) := (boards r v*4)*width r v
def index (p : Location r v) (b : Fin (width r v)) : Fin (bitCount r v) := pack (pack p.1 p.2) b

private theorem width_pos (r v : Nat) : 0<width r v := Nat.zero_lt_succ _

def whereBit (q : Fin (bitCount r v)) : Location r v × Fin (width r v) :=
  let a := group q (width_pos r v)
  ((group a (by decide),lane a (by decide)),lane q (width_pos r v))

theorem where_index (p : Location r v) (b : Fin (width r v)) : whereBit (index p b)=(p,b) := by
  simp only [whereBit,index,group_pack,lane_pack]

theorem index_where (q : Fin (bitCount r v)) : index (whereBit q).1 (whereBit q).2=q := by
  simp only [whereBit,index,pack_group]
  exact pack_group q (width_pos r v)

def encodedBit (f : Source r v) (q : Fin (bitCount r v)) : Bool :=
  (address f (whereBit q).1).testBit (whereBit q).2.val

def encode (f : Source r v) : List Bool := List.ofFn (encodedBit f)

theorem encode_length (f : Source r v) : (encode f).length=bitCount r v := List.length_ofFn

theorem encode_at (f : Source r v) (q : Fin (bitCount r v)) :
    (encode f)[q.val]'(by rw [encode_length]; exact q.isLt)=encodedBit f q := by simp [encode]

theorem read_index (f : Source r v) (p : Location r v) (b : Fin (width r v)) :
    encodedBit f (index p b) = (address f p).testBit b.val := by simp only [encodedBit,where_index]

def cell (m : Nat) (u : Fin n) : Location (rows n m) (vars n m) :=
  occurrence (vars n m) (inputRow u) 0

def offset (m : Nat) (u : Fin n) : Fin (bitCount (rows n m) (vars n m)) :=
  index (cell m u) ⟨0,width_pos _ _⟩

theorem offset_value (m : Nat) (u : Fin n) :
    (offset m u).val=(4*(7*(1+m+u.val)+4)+1)*width (rows n m) (vars n m) := by
  change ((7*(1+m+u.val)+(4+0))*4+1)*_+0 = _
  rw [Nat.add_zero,Nat.add_zero,Nat.mul_comm _ 4]

theorem offset_injective (m : Nat) {u t : Fin n} (h : offset m u=offset m t) : u=t := by
  have p := congrArg (fun q : Fin (bitCount (rows n m) (vars n m)) => (whereBit q).1) h
  simp only [offset,where_index] at p
  have atRow := (occurrence_injective p).1
  have val := congrArg Fin.val atRow
  change 1+m+u.val=1+m+t.val at val
  exact Fin.ext (by omega)

theorem cell_bits (g : Edges n m) (x : Fin n → Bool) (u : Fin n) (b : Nat) :
    (address (source g x) (cell m u)).testBit b =
      if b=0 then x u else (2*u.val).testBit b := by
  rw [cell,occurrence_address,GraphCoverSource.source_input]
  exact GraphCoverSource.query_bit x u b

theorem source_bit_once (g : Edges n m) (x : Fin n → Bool) (u : Fin n) :
    encodedBit (source g x) (offset m u)=x u := by
  rw [offset,read_index,cell_bits]
  rfl

private theorem fixed_location (g : Edges n m) (x y : Fin n → Bool)
    (p : Location (rows n m) (vars n m)) (off : ∀ u, p≠cell m u) :
    address (source g x) p=address (source g y) p := by
  apply Classical.byContradiction
  intro diff
  obtain ⟨i,j,h,ds⟩ := changed_location _ _ _ diff
  apply ds
  apply GraphCoverSource.source_static
  intro u
  by_cases r : i=inputRow u
  · right
    intro zero
    exact off u (by simpa only [r,zero,cell] using h)
  · exact Or.inl r

/-- At every other serialized bit position the value is constant as the
input cover varies. Fixed bits may depend on the graph and its public size. -/
theorem other_bits_constant (g : Edges n m) (x y : Fin n → Bool)
    (q : Fin (bitCount (rows n m) (vars n m))) (off : ∀ u, q≠offset m u) :
    encodedBit (source g x) q=encodedBit (source g y) q := by
  let p := (whereBit q).1
  let b := (whereBit q).2
  have pos : index p b=q := index_where q
  rw [←pos,read_index,read_index]
  by_cases hit : ∃ u, p=cell m u
  · obtain ⟨u,eq⟩ := hit
    have hn : b.val≠0 := by
      intro zero
      have fb : b=⟨0,width_pos _ _⟩ := Fin.ext zero
      exact off u (by rw [←pos,eq,fb]; rfl)
    rw [eq,cell_bits,cell_bits,ite_eq_right hn,ite_eq_right hn]
  · rw [fixed_location g x y p (fun u e => hit ⟨u,e⟩)]


abbrev Flat (n m : Nat) := Fin (bitCount (rows n m) (vars n m))

theorem graph_sizes (n m : Nat) :
    boards (rows n m) (vars n m) = 15*n+14*m+15 ∧
    dimension (rows n m) (vars n m) = 45*n+41*m+45 := by
  unfold boards dimension GraphCoverSource.rows GraphCoverSource.vars
  omega

theorem graph_length (g : Edges n m) (x : Fin n → Bool) :
    (encode (source g x)).length =
      ((15*n+14*m+15)*4)*((45*n+41*m+44).log2+1) := by
  rw [encode_length,bitCount,width,(graph_sizes n m).1,(graph_sizes n m).2]
  have e : 45*n+41*m+45-1 = 45*n+41*m+44 := by omega
  rw [e]

/-- A computable single-use substitution on any finite input alphabet. -/
def labelBy (loc : Fin a → Fin b) (baseline : Fin b → Bool) (q : Fin b) : ReadRestriction.Field (Fin a) :=
  match (List.finRange a).find? (fun u => q == loc u) with
  | some u => .input u
  | none => .fixed (baseline q)

theorem labelBy_input_iff (loc : Fin a → Fin b) (inj : ∀ u v, loc u=loc v → u=v)
    (baseline : Fin b → Bool) (u : Fin a) (q : Fin b) :
    labelBy loc baseline q = .input u ↔ q=loc u := by
  unfold labelBy
  cases h : (List.finRange a).find? (fun j => q == loc j) with
  | none =>
    have miss := List.find?_eq_none.mp h u (List.mem_finRange _)
    simp only [beq_iff_eq] at miss
    simp [miss]
  | some j =>
    have hj : q=loc j := beq_iff_eq.mp (List.find?_some (p:=fun j => q == loc j) h)
    constructor
    · intro e; cases e; exact hj
    · intro e
      exact congrArg ReadRestriction.Field.input (inj _ _ (hj.symm.trans e))

private theorem read_labelBy (loc : Fin a → Fin b) (baseline : Fin b → Bool) (z : Fin a → Bool)
    (actual : Fin b → Bool) (on : ∀ u, actual (loc u)=z u)
    (off : ∀ q, (∀ u, q≠loc u) → actual q=baseline q) (q : Fin b) :
    (labelBy loc baseline q).read z = actual q := by
  unfold labelBy
  cases h : (List.finRange a).find? (fun j => q == loc j) with
  | some u =>
    have eq : q=loc u := beq_iff_eq.mp (List.find?_some (p:=fun j => q == loc j) h)
    exact (eq ▸ on u).symm
  | none => exact (off q (fun u e => List.find?_eq_none.mp h u (List.mem_finRange _) (beq_iff_eq.mpr e))).symm

def field (g : Edges n m) : Flat n m → ReadRestriction.Field (Fin n) :=
  labelBy (offset m) (encodedBit (source g (fun _ => false)))

theorem field_input_iff (g : Edges n m) (u : Fin n) (q : Flat n m) :
    field g q = .input u ↔ q=offset m u :=
  labelBy_input_iff _ (fun _ _ => offset_injective m) _ _ _

theorem field_read (g : Edges n m) (x : Fin n → Bool) (q : Flat n m) :
    (field g q).read x = encodedBit (source g x) q :=
  read_labelBy _ _ x _ (source_bit_once g x) (other_bits_constant g x (fun _ => false)) q

theorem field_word (g : Edges n m) (x : Fin n → Bool) :
    List.ofFn (fun q : Flat n m => (field g q).read x) = encode (source g x) := by
  simp only [field_read,encode]

/-- A family of arbitrary exact-one sources whose independent data occur
in distinct address slots, each selecting one of the consecutive values
2·base and 2·base+1. Graph-cover structure is not used below. -/
structure Switches (F : (Fin s → Bool) → Source r v) where
  site : Fin s → Fin r × Fin 3
  unique_site : ∀ u t, site u=site t → u=t
  base : Fin s → Nat
  chosen_value : ∀ x u, (F x (site u).1 (site u).2).val=2*base u+(x u).toNat
  fixed_value : ∀ x y i a, (∀ u, (i,a)≠site u) → F x i a=F y i a

namespace Switches

def location {F : (Fin s → Bool) → Source r v} (S : Switches F) (u : Fin s) :=
  index (occurrence v (S.site u).1 (S.site u).2) ⟨0,width_pos _ _⟩

theorem unique {F : (Fin s → Bool) → Source r v} (S : Switches F) (u t : Fin s)
    (h : S.location u=S.location t) : u=t := by
  have loc := congrArg (fun q : Fin (bitCount r v) => (whereBit q).1) h
  simp only [location,where_index] at loc
  have pair := occurrence_injective loc
  exact S.unique_site u t (Prod.ext pair.1 pair.2)

private theorem parityBit (a : Nat) (b : Bool) (j : Nat) :
    (2*a+b.toNat).testBit j = if j=0 then b else (2*a).testBit j := by
  cases j with
  | zero => cases b <;> simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_succ,ite_eq_right (Nat.succ_ne_zero _),Nat.testBit_succ]
    have val : (2*a+b.toNat)/2=(2*a)/2 := by cases b <;> simp <;> omega
    rw [val]

theorem on_location {F : (Fin s → Bool) → Source r v} (S : Switches F) (x : Fin s → Bool) (u : Fin s) :
    encodedBit (F x) (S.location u) = x u := by
  rw [location,read_index,occurrence_address,S.chosen_value,parityBit]
  rfl

theorem elsewhere {F : (Fin s → Bool) → Source r v} (S : Switches F) (x y : Fin s → Bool)
    (q : Fin (bitCount r v)) (off : ∀u, q≠S.location u) : encodedBit (F x) q=encodedBit (F y) q := by
  let p := (whereBit q).1
  let b := (whereBit q).2
  have pos : index p b=q := index_where q
  rw [←pos,read_index,read_index]
  by_cases hit : ∃ u, p=occurrence v (S.site u).1 (S.site u).2
  · obtain ⟨u,hu⟩ := hit
    have hn : b.val≠0 := by
      intro zero
      have fb : b=⟨0,width_pos _ _⟩ := Fin.ext zero
      exact off u (by rw [←pos,hu,fb]; rfl)
    rw [hu,occurrence_address,occurrence_address,S.chosen_value,S.chosen_value,
      parityBit,parityBit,ite_eq_right hn,ite_eq_right hn]
  · have same : address (F x) p=address (F y) p := by
      apply Classical.byContradiction; intro h
      obtain ⟨i,a,hp,neq⟩ := changed_location _ _ _ h
      apply neq
      apply S.fixed_value
      intro u pair
      have swap : occurrence v i a=occurrence v (S.site u).1 (S.site u).2 :=
        congrArg (fun z : Fin r × Fin 3 => occurrence v z.1 z.2) pair
      exact hit ⟨u,hp.trans swap⟩
    rw [same]

def field {F : (Fin s → Bool) → Source r v} (S : Switches F) :=
  labelBy S.location (encodedBit (F (fun _ => false)))

theorem field_input_iff {F : (Fin s → Bool) → Source r v} (S : Switches F) (u : Fin s)
    (q : Fin (bitCount r v)) : S.field q = .input u ↔ q=S.location u :=
  labelBy_input_iff _ S.unique _ _ _

theorem field_read {F : (Fin s → Bool) → Source r v} (S : Switches F) (x : Fin s → Bool)
    (q : Fin (bitCount r v)) : (S.field q).read x = encodedBit (F x) q :=
  read_labelBy _ _ x _ (S.on_location x) (S.elsewhere x (fun _ => false)) q

end Switches


/-- The same serializer on every atlas of the public dimensions. It reads
only integer axis coordinates, with no port designations or source witness. -/
def rawBit (r v : Nat) (T : AxisGlue.Atlas (boards r v) (dimension r v))
    (q : Fin (bitCount r v)) : Bool :=
  (T.loc (whereBit q).1.1 (whereBit q).1.2).val.testBit (whereBit q).2.val

def rawWord (r v : Nat) (T : AxisGlue.Atlas (boards r v) (dimension r v)) : List Bool :=
  List.ofFn (rawBit r v T)

theorem compiled_raw (f : Source r v) : rawWord r v (CapAtlas.compiled f)=encode f := rfl

theorem raw_word_injective (r v : Nat) {T U : AxisGlue.Atlas (boards r v) (dimension r v)}
    (same : rawWord r v T=rawWord r v U) : T=U := by
  have point (q : Fin (bitCount r v)) : rawBit r v T q=rawBit r v U q := by
    have hk := congrArg (fun w : List Bool => w[q.val]?) same
    simpa [rawWord,List.getElem?_ofFn,q.isLt] using hk
  have maxV := Nat.lt_log2_self (n:=dimension r v-1)
  have fit (a : Fin (dimension r v)) : a.val<2^width r v := by
    have bound := a.isLt; unfold width; omega
  have locs : T.loc=U.loc := by
    funext i a
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases low : j<width r v
    · have h := point (index (i,a) ⟨j,low⟩)
      simpa only [rawBit,where_index] using h
    · have pow := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_lt low)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (fit (T.loc i a)) pow),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (fit (U.loc i a)) pow)]
  cases T; cases U; cases locs; rfl

end Mobius.BoardInputProjection
