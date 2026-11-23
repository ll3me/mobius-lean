import Mobius.TwoPhases

/-! Three exposed squares in the 15-square two-table parity certificate.
The port numbers 1, 3, 6 are one-based positions in the certificate list.
All twelve tagged port corners may be prescribed individually. -/
namespace Mobius.OneInThree

open Mobius.SignObstruction (B Rectangle total total_append total_perm total_paired)
open Mobius.TwoPhases (TaggedCell certificate corners score)

abbrev Phase := B → B → Bool

structure Quad where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  deriving DecidableEq, Repr

structure Boundary where
  first : Quad
  third : Quad
  sixth : Quad
  deriving DecidableEq, Repr

def port₁ : Rectangle := (0,5,2)
def port₃ : Rectangle := (0,8,8)
def port₆ : Rectangle := (2,3,7)

def internal : List Rectangle :=
  [(0,5,5),(0,8,15),(2,3,6),(2,7,4),(2,14,10),(2,14,13),
   (4,5,1),(4,8,11),(4,8,12),(5,0,3),(6,14,9),(6,14,14)]

theorem partition : certificate.Perm ([port₁, port₃, port₆] ++ internal) := by decide
theorem sizes : internal.length = 12 ∧
    ([port₁,port₃,port₆].flatMap corners).eraseDups.length = 12 := by decide

def readQuad (row col : Phase) (r : Rectangle) : Quad :=
  let (x,y,d) := r
  ⟨row x y, row (x ^^^ d) (y ^^^ d), col x (y ^^^ d), col (x ^^^ d) y⟩

def readBoundary (row col : Phase) : Boundary :=
  ⟨readQuad row col port₁, readQuad row col port₃, readQuad row col port₆⟩

def Quad.parity (s : Quad) : Bool := s.a ^^ (s.b ^^ (s.c ^^ (s.d ^^ false)))
def Quad.defect (s : Quad) : Bool := !s.parity

/-- A common change of row and column signs in both tables preserves the
observable defect. Each coordinate sign occurs twice around the square. -/
theorem defect_gauge (r c : Phase) (a b : B → Bool) (q : Rectangle) :
    (readQuad (fun x y => r x y ^^ (a x ^^ b y))
      (fun x y => c x y ^^ (a x ^^ b y)) q).defect = (readQuad r c q).defect := by
  obtain ⟨x,y,d⟩ := q
  simp only [Quad.defect, Quad.parity, readQuad]
  congr 1
  generalize r x y = u
  generalize r (x ^^^ d) (y ^^^ d) = v
  generalize c x (y ^^^ d) = w
  generalize c (x ^^^ d) y = z
  generalize a x = p
  generalize a (x ^^^ d) = s
  generalize b y = t
  generalize b (y ^^^ d) = h
  revert u v w z p s t h
  decide

def Boundary.oddDefects (p : Boundary) : Prop :=
  (p.first.defect ^^ (p.third.defect ^^ p.sixth.defect)) = true

def Boundary.cost (p : Boundary) : Nat :=
  p.first.defect.toNat + p.third.defect.toNat + p.sixth.defect.toNat

def Boundary.exactlyOne (p : Boundary) : Prop := p.cost = 1

def Hard (row col : Phase) : Prop := ∀ r ∈ internal, score row col r = true

def defects (row col : Phase) := certificate.countP (fun r => !(score row col r))

private theorem read_score (row col : Phase) (r : Rectangle) :
    (readQuad row col r).parity = score row col r := by obtain ⟨x,y,d⟩ := r; rfl

private theorem zero_total (row col : Phase) : total (score row col) certificate = false := by
  let f : TaggedCell → Bool := fun (tag,x,y) => if tag then col x y else row x y
  have flatten (rs : List Rectangle) : total (score row col) rs = total f (rs.flatMap corners) := by
    induction rs with
    | nil => rfl
    | cons r rs ih => rw [List.flatMap_cons,total_append,← ih]; rfl
  exact (flatten certificate).trans ((total_perm f Mobius.TwoPhases.paired_cells).trans
    (total_paired f Mobius.TwoPhases.halfCells))

private theorem total_on {f g : α → Bool} (xs : List α) (h : ∀ x ∈ xs, f x = g x) :
    total f xs = total g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [show total f (x::xs) = (f x ^^ total f xs) by rfl,
      show total g (x::xs) = (g x ^^ total g xs) by rfl, h x (by simp),
      ih (fun y hy => h y (by simp [hy]))]

private theorem parity_rule (a b c : Bool) :
    ((!a ^^ (!b ^^ !c)) = true) ↔ (a ^^ (b ^^ c)) = false := by
  cases a <;> cases b <;> cases c <;> decide

theorem hard_requires_odd (row col : Phase) (hard : Hard row col) :
    (readBoundary row col).oddDefects := by
  have h := (total_perm (score row col) partition).symm.trans (zero_total row col)
  have changed := total_on (g := fun _ => true) internal hard
  have even : total (fun _ : Rectangle => true) internal = false := by decide
  rw [total_append, changed, even] at h
  unfold Boundary.oddDefects Quad.defect
  apply (parity_rule ..).2
  simpa only [readBoundary,read_score,total,Bool.xor_false] using h

/-- A mask encodes an affine combination of the twelve boundary bits.
    Bit 12 is the constant one. -/
private abbrev Mask := BitVec 13

private def data (p : Boundary) : List Bool :=
  [p.first.a,p.first.b,p.first.c,p.first.d,p.third.a,p.third.b,p.third.c,p.third.d,
   p.sixth.a,p.sixth.b,p.sixth.c,p.sixth.d,true]

private def indices : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12]
private def eval (p : Boundary) (m : Mask) :=
  total (fun i => m.getLsbD i && (data p).getD i false) indices

private theorem linear (p : Boundary) (m n : Mask) :
    eval p (m ^^^ n) = (eval p m ^^ eval p n) := by
  have aux (xs : List Nat) :
      total (fun i => (m ^^^ n).getLsbD i && (data p).getD i false) xs =
      (total (fun i => m.getLsbD i && (data p).getD i false) xs ^^
       total (fun i => n.getLsbD i && (data p).getD i false) xs) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp only [total]
      rw [ih]
      simp only [BitVec.getLsbD_xor,Bool.and_xor_distrib_right]
      letI : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩
      letI : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
      ac_rfl
  exact aux indices

/-- The twelve port edges carry separate basis bits. Internal non-tree
    edges carry zero. Eliminating the eleven non-root vertices of an
    internal spanning tree gives the remaining masks, with root square 2. -/
private def wireMask (c : TaggedCell) : Mask :=
  match c.1, c.2.1.toNat, c.2.2.toNat with
  | false,0,5 => 1
  | false,0,8 => 16
  | false,2,3 => 256
  | false,2,7 => 2
  | false,4,5 => 4380
  | false,5,0 => 6178
  | false,5,4 => 512
  | false,6,3 => 4098
  | false,8,0 => 32
  | false,8,4 => 5120
  | true,0,0 => 64
  | true,0,7 => 4
  | true,2,3 => 4096
  | true,2,4 => 1024
  | true,2,5 => 8
  | true,4,3 => 20
  | true,4,4 => 1152
  | true,5,3 => 2048
  | true,5,5 => 1948
  | true,6,0 => 4128
  | true,6,7 => 4096
  | true,8,8 => 128
  | true,15,8 => 4116
  | _,_,_ => 0

def rowExtension (p : Boundary) (x y : B) := eval p (wireMask (false,x,y))
def colExtension (p : Boundary) (x y : B) := eval p (wireMask (true,x,y))

private def parityMask (wire : TaggedCell → Mask) : List TaggedCell → Mask
  | [] => 0
  | c :: cs => wire c ^^^ parityMask wire cs

private theorem eval_zero (p : Boundary) : eval p 0 = false := by
  simp [eval,indices,total]

private theorem eval_cells (wire : TaggedCell → Mask) (p : Boundary) (cs : List TaggedCell) :
    total (fun (tag,x,y) => if tag then eval p (wire (true,x,y)) else eval p (wire (false,x,y))) cs =
    eval p (parityMask wire cs) := by
  induction cs with
  | nil => exact (eval_zero p).symm
  | cons c cs ih =>
    obtain ⟨tag,x,y⟩ := c
    rw [parityMask,linear,show total _ ((tag,x,y)::cs) = (_ ^^ total _ cs) by rfl, ih]
    cases tag <;> rfl

private theorem internal_masks : ∀ r ∈ internal,
    parityMask wireMask (corners r) = 4096 ∨ parityMask wireMask (corners r) = 8191 := by decide

private theorem constant_mask (p : Boundary) : eval p 4096 = true := by
  simp [eval,indices,data,total]

private theorem root_mask (p : Boundary) : eval p 8191 = true ↔ p.oddDefects := by
  have bits (o : Boundary) : eval o 8191 =
      !(o.first.parity ^^ (o.third.parity ^^ o.sixth.parity)) := by
    simp [eval,indices,data,total,Quad.parity]
  rw [bits,Boundary.oddDefects,Quad.defect,Quad.defect,Quad.defect,parity_rule]
  simp

theorem extension_hard (p : Boundary) (h : p.oddDefects) :
    Hard (rowExtension p) (colExtension p) := by
  intro r hr
  change total _ (corners r) = true
  unfold rowExtension colExtension
  rw [eval_cells wireMask p]
  rcases internal_masks r hr with hc | hc
  · rw [hc,constant_mask]
  · rw [hc]; exact (root_mask p).mpr h

theorem extension_boundary (p : Boundary) : readBoundary (rowExtension p) (colExtension p) = p := by
  cases p with
  | mk a b c =>
    cases a; cases b; cases c
    simp [readBoundary,readQuad,port₁,port₃,port₆,rowExtension,colExtension,wireMask,
      eval,indices,data,total]

theorem extends_iff_odd (p : Boundary) :
    (∃ row col, Hard row col ∧ readBoundary row col = p) ↔ p.oddDefects := by
  constructor
  · rintro ⟨row,col,hard,rfl⟩; exact hard_requires_odd row col hard
  · intro odd; exact ⟨_,_,extension_hard p odd,extension_boundary p⟩

theorem hard_cost (row col : Phase) (hard : Hard row col) :
    defects row col = (readBoundary row col).cost := by
  have no : internal.countP (fun r => !score row col r) = 0 := by
    apply List.countP_eq_zero.mpr
    intro r hr
    simp [hard r hr]
  unfold defects
  rw [List.Perm.countP_eq _ partition, List.countP_append, no, Nat.add_zero]
  change [port₁,port₃,port₆].countP (fun r => !score row col r) =
    (!(score row col port₁)).toNat + (!(score row col port₃)).toNat + (!(score row col port₆)).toNat
  simp only [List.countP_cons,List.countP_nil]
  cases score row col port₁ <;> cases score row col port₃ <;> cases score row col port₆ <;> decide

private theorem one_odd (p : Boundary) (h : p.exactlyOne) : p.oddDefects := by
  unfold Boundary.exactlyOne Boundary.cost at h
  unfold Boundary.oddDefects
  cases h₁ : p.first.defect <;> cases h₂ : p.third.defect <;> cases h₃ : p.sixth.defect <;> simp_all

theorem minimum_one_iff_exactlyOne (p : Boundary) :
    (∃ row col, Hard row col ∧ readBoundary row col = p ∧ defects row col = 1) ↔ p.exactlyOne := by
  constructor
  · rintro ⟨row,col,h,rfl,cost⟩
    exact (hard_cost row col h).symm.trans cost
  · intro one
    have h := extension_hard p (one_odd p one)
    exact ⟨_,_,h,extension_boundary p,by rw [hard_cost _ _ h,extension_boundary]; exact one⟩

/-- A positive literal uses its truth value as its defect indicator. -/
def literal (truth : Bool) : Quad := ⟨!truth,false,false,false⟩

theorem positive_clause (a b c : Bool) :
    (∃ row col, Hard row col ∧ readBoundary row col = ⟨literal a,literal b,literal c⟩ ∧
      defects row col = 1) ↔ a.toNat+b.toNat+c.toNat = 1 := by
  rw [minimum_one_iff_exactlyOne]
  cases a <;> cases b <;> cases c <;> rfl

/-! A NOT wire in the same certificate, exposing squares 1 and 12. -/
def port₁₂ : Rectangle := (4,8,12)

structure NotBoundary where
  first : Quad
  twelfth : Quad
  deriving DecidableEq, Repr

def readNot (row col : Phase) : NotBoundary := ⟨readQuad row col port₁,readQuad row col port₁₂⟩

def internalNot : List Rectangle :=
  [(0,5,5),(0,8,8),(0,8,15),(2,3,6),(2,3,7),(2,7,4),(2,14,10),(2,14,13),
   (4,5,1),(4,8,11),(5,0,3),(6,14,9),(6,14,14)]

def HardNot (row col : Phase) : Prop := ∀ r ∈ internalNot, score row col r = true

theorem not_partition : certificate.Perm ([port₁,port₁₂] ++ internalNot) := by decide
theorem not_sizes : internalNot.length = 13 ∧
    ([port₁,port₁₂].flatMap corners).eraseDups.length = 8 := by decide

private def notSeed (p : NotBoundary) : Boundary := ⟨p.first,p.twelfth,⟨false,false,false,false⟩⟩

private def notMask (c : TaggedCell) : Mask :=
  match c.1, c.2.1.toNat, c.2.2.toNat with
  | false,0,5 => 1
  | false,0,8 => 4116
  | false,2,7 => 2
  | false,4,5 => 4104
  | false,4,8 => 16
  | false,5,0 => 4098
  | false,5,4 => 4096
  | false,6,3 => 2
  | false,8,0 => 32
  | false,8,4 => 32
  | false,15,7 => 4096
  | true,0,0 => 180
  | true,0,7 => 4
  | true,2,3 => 4096
  | true,2,5 => 8
  | true,4,4 => 64
  | true,5,5 => 4168
  | true,8,8 => 128
  | true,8,14 => 4128
  | true,15,8 => 4112
  | _,_,_ => 0

def notRow (p : NotBoundary) (x y : B) := eval (notSeed p) (notMask (false,x,y))
def notCol (p : NotBoundary) (x y : B) := eval (notSeed p) (notMask (true,x,y))

private theorem not_internal_masks : ∀ r ∈ internalNot,
    parityMask notMask (corners r) = 4096 ∨ parityMask notMask (corners r) = 255 := by decide

private theorem opposite_rule (a b : Bool) : (a ^^ b) = true ↔ (!a) ≠ (!b) := by
  cases a <;> cases b <;> decide

private theorem not_root (p : NotBoundary) : eval (notSeed p) 255 = true ↔
    p.first.defect ≠ p.twelfth.defect := by
  have expand : eval (notSeed p) 255 = (p.first.parity ^^ p.twelfth.parity) := by
    simp [eval,indices,data,notSeed,total,Quad.parity]
  rw [expand]
  exact opposite_rule _ _

theorem not_extension_hard (p : NotBoundary) (opposite : p.first.defect ≠ p.twelfth.defect) :
    HardNot (notRow p) (notCol p) := by
  intro r hr
  change total _ (corners r) = true
  unfold notRow notCol
  rw [eval_cells notMask (notSeed p)]
  rcases not_internal_masks r hr with hc | hc
  · rw [hc,constant_mask]
  · rw [hc]; exact (not_root p).mpr opposite

theorem not_extension_boundary (p : NotBoundary) : readNot (notRow p) (notCol p) = p := by
  cases p with
  | mk a b =>
    cases a; cases b
    simp [readNot,readQuad,port₁,port₁₂,notRow,notCol,notSeed,notMask,eval,indices,data,total]

theorem extends_not_iff (p : NotBoundary) :
    (∃ row col, HardNot row col ∧ readNot row col = p) ↔ p.first.defect ≠ p.twelfth.defect := by
  constructor
  · rintro ⟨row,col,hard,rfl⟩
    have h := (total_perm (score row col) not_partition).symm.trans (zero_total row col)
    have changed := total_on (g := fun _ => true) internalNot hard
    have odd : total (fun _ : Rectangle => true) internalNot = true := by decide
    rw [total_append, changed, odd] at h
    apply (opposite_rule ..).mp
    simpa [readNot,read_score,total] using h
  · intro opposite
    exact ⟨_,_,not_extension_hard p opposite,not_extension_boundary p⟩

/-- Both NOT ports are clean geometric 2×2 squares: within either coordinate
    tile, every tagged cell used anywhere in the certificate is one of its
    four designated corners. The tags are kept in this statement. -/
theorem not_tiles_clean : ∀ r ∈ [port₁,port₁₂], ∀ c ∈ Mobius.TwoPhases.halfCells,
    (c.2.1 = r.1 ∨ c.2.1 = r.1 ^^^ r.2.2) →
    (c.2.2 = r.2.1 ∨ c.2.2 = r.2.1 ^^^ r.2.2) → c ∈ corners r := by decide

/-- Coefficient bits, from low to high, select 2,12,4,13 in the shared
    four-bit ambient vector space of the NOT gadget. -/
def notBasis (w : B) : B :=
  (if w.getLsbD 0 then (2 : B) else 0) ^^^
  (if w.getLsbD 1 then (12 : B) else 0) ^^^
  (if w.getLsbD 2 then (4 : B) else 0) ^^^
  (if w.getLsbD 3 then (13 : B) else 0)

theorem not_basis_coordinates (p : B) :
    ∃ w : B, notBasis w = p ∧ ∀ v : B, notBasis v = p → v = w := by
  revert p; decide

theorem not_basis_linear (u v : B) : notBasis (u ^^^ v) = notBasis u ^^^ notBasis v := by
  revert u v; decide

def HardPin (row col : Phase) : Prop := ∀ r ∈ certificate, r ≠ port₁ → score row col r = true

/-- Pin square 1 to one defect. Every particular choice of its four
    corner signs realizing that defect extends; all fourteen other
    squares, including square 12, are then required to succeed. -/
theorem extends_pin_iff (p : Quad) :
    (∃ row col, HardPin row col ∧ readQuad row col port₁ = p) ↔ p.defect = true := by
  constructor
  · rintro ⟨row,col,h,rfl⟩
    have notGood : score row col port₁ ≠ true := by
      intro first
      apply Mobius.TwoPhases.fifteen_inconsistent
      refine ⟨row,col,fun r hr => ?_⟩
      by_cases eq : r = port₁
      · exact eq ▸ first
      · exact h r hr eq
    unfold Quad.defect
    rw [read_score]
    cases hv : score row col port₁ <;> simp_all
  · intro pin
    let good : Quad := ⟨true,false,false,false⟩
    have opposite : p.defect ≠ good.defect := by rw [pin]; decide
    obtain ⟨row,col,hard,reads⟩ := (extends_not_iff ⟨p,good⟩).mpr opposite
    have first := congrArg NotBoundary.first reads
    have last := congrArg NotBoundary.twelfth reads
    change readQuad row col port₁₂ = good at last
    refine ⟨row,col,?_,first⟩
    intro r hr ne
    by_cases h12 : r = port₁₂
    · subst r
      rw [← read_score,last]
      rfl
    · apply hard r
      have mem := not_partition.mem_iff.mp hr
      simpa [ne, h12] using mem

/-- One-based square 2 is the exceptional internal square of the NOT extension. -/
def port₂ : Rectangle := (0,5,5)

private theorem not_mask_exact : ∀ r ∈ internalNot,
    parityMask notMask (corners r) = if r = port₂ then 255 else 4096 := by decide

theorem not_extension_score (p : NotBoundary) (r : Rectangle) (hr : r ∈ internalNot) :
    score (notRow p) (notCol p) r =
      (if r = port₂ then decide (p.first.defect ≠ p.twelfth.defect) else true) := by
  unfold score notRow notCol
  rw [eval_cells notMask (notSeed p),not_mask_exact r hr]
  by_cases atRoot : r = port₂
  · simp only [atRoot, ↓reduceIte]
    have iff := not_root p
    cases actual : eval (notSeed p) 255 <;> simp_all
  · simp only [atRoot, ↓reduceIte,constant_mask]

def notInternalCost (row col : Phase) : Nat := internalNot.countP (fun r => !score row col r)

theorem not_extension_cost (p : NotBoundary) :
    notInternalCost (notRow p) (notCol p) = if p.first.defect = p.twelfth.defect then 1 else 0 := by
  unfold notInternalCost
  by_cases same : p.first.defect = p.twelfth.defect
  · rw [ite_eq_left same]
    have h : internalNot.countP (fun r => !score (notRow p) (notCol p) r) =
        internalNot.countP (fun r => decide (r = port₂)) := by
      apply List.countP_congr
      intro r hr
      rw [not_extension_score _ _ hr]
      by_cases isRoot : r = port₂ <;> simp [same,isRoot]
    rw [h]; decide
  · rw [ite_eq_right same]
    apply List.countP_eq_zero.mpr
    intro r hr
    rw [not_extension_score _ _ hr]
    simp [same]

theorem not_cost_lower (p : NotBoundary) (row col : Phase) (reads : readNot row col = p) :
    (if p.first.defect = p.twelfth.defect then 1 else 0) ≤ notInternalCost row col := by
  by_cases same : p.first.defect = p.twelfth.defect
  · rw [ite_eq_left same]
    apply Nat.zero_lt_of_ne_zero
    intro zero
    have hard : HardNot row col := by
      intro r hr
      have val := List.countP_eq_zero.mp zero r hr
      cases hs : score row col r <;> simp_all
    exact (extends_not_iff p).mp ⟨row,col,hard,reads⟩ same
  · rw [ite_eq_right same]; exact Nat.zero_le _

/-- The exact minimum over extensions is zero on opposite defect bits and
    one on equal defect bits. The explicit minimizer preserves all eight
    prescribed corner values, even in the latter case. -/
theorem not_minimum_cost (p : NotBoundary) :
    (∀ row col, readNot row col = p →
      (if p.first.defect = p.twelfth.defect then 1 else 0) ≤ notInternalCost row col) ∧
    (∃ row col, readNot row col = p ∧
      notInternalCost row col = if p.first.defect = p.twelfth.defect then 1 else 0) :=
  ⟨not_cost_lower p,_,_,not_extension_boundary p,not_extension_cost p⟩

end Mobius.OneInThree
