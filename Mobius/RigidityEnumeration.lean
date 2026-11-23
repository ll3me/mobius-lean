import Mobius.RigidityKernelData

/-! Exact cardinalities of optimal four-bit sign tables. The finite labels
are an exceptional direction and a packed word of independent sign bits. -/
namespace Mobius.Rigidity.Enumeration
open Mobius.SignObstruction (B Rectangle)
open Mobius.Rigidity.Kernel (Model Valid Good square key)
open Mobius.TwoPhases (score)

set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

structure Bijection (α β : Type) where
  encode : α → β
  decode : β → α
  decode_encode : ∀ x, decode (encode x) = x
  encode_decode : ∀ y, encode (decode y) = y

def Bijection.thenDo {α β γ : Type} (a : Bijection α β) (b : Bijection β γ) : Bijection α γ where
  encode x := b.encode (a.encode x)
  decode z := a.decode (b.decode z)
  decode_encode x := by rw [b.decode_encode, a.decode_encode]
  encode_decode z := by rw [a.encode_decode, b.encode_decode]

abbrev Phase := B → B → Bool
abbrev Pair := Phase × Phase

def Shared (two : Bool) (p : Pair) := two = false → p.2 = p.1

def lookup (p : Pair) (i : Nat) : Bool :=
  (if i < 256 then p.1 else p.2) (BitVec.ofNat 4 (i/16)) (BitVec.ofNat 4 i)

theorem lookup_key (p : Pair) (t : Bool) (x y : B) :
    lookup p (key t x y) = (if t then p.2 else p.1) x y := by
  have indices : ∀ (t : Bool) (x y : B),
      (decide (key t x y < 256)) = !t ∧ BitVec.ofNat 4 (key t x y / 16) = x ∧
      BitVec.ofNat 4 (key t x y) = y := by decide
  obtain ⟨ht,hx,hy⟩ := indices t x y
  simp only [lookup,hx,hy]
  cases t with
  | false => have lt := of_decide_eq_true ht; simp [lt]
  | true => have nlt := of_decide_eq_false ht; simp [nlt]

theorem eval_lookup (two : Bool) (p : Pair) (shared : Shared two p) (x y d : B) :
    (square two x y d).val (lookup p) = score p.1 p.2 (x,y,d) := by
  simp only [square,Kernel.Quad.val,lookup_key,score,Mobius.TwoPhases.corners,Mobius.SignObstruction.total]
  cases two
  · rw [shared rfl]
    simp [Bool.xor_comm,Bool.xor_left_comm]
  · simp [Bool.xor_comm]

def tabulate (two : Bool) (v : Nat → Bool) : Pair :=
  (fun x y => v (key false x y),fun x y => v (key two x y))

private theorem tabulate_shared (two : Bool) (v : Nat → Bool) : Shared two (tabulate two v) := by
  rintro rfl; rfl

private theorem key_reassemble (i : Nat) (hi : i < 512) :
    key (decide (256 ≤ i)) (BitVec.ofNat 4 (i/16)) (BitVec.ofNat 4 i) = i := by
  have valid : ∀ j : Fin 512, key (decide (256 ≤ j.val)) (BitVec.ofNat 4 (j.val/16)) (BitVec.ofNat 4 j.val) = j.val := by decide
  exact valid ⟨i,hi⟩

private theorem lookup_tabulate (m : Model) (v : Nat → Bool) (i : Nat) (hi : i < m.size) :
    lookup (tabulate m.two v) i = v i := by
  by_cases lt : i < 256
  · have h := key_reassemble i (by omega)
    simp [show ¬256 ≤ i by omega] at h
    simp only [lookup,lt,ite_true,tabulate]
    exact congrArg v h
  · have two : m.two = true := by cases h : m.two <;> simp_all [Model.size]
    have big : i < 512 := by simpa [Model.size,two] using hi
    have h := key_reassemble i big
    simp [show 256 ≤ i by omega] at h
    simp only [lookup,lt,ite_false,tabulate,two]
    exact congrArg v h

def ZeroPair (two : Bool) := {p : Pair // Shared two p ∧ ∀ x y d : B, d ≠ 0 → score p.1 p.2 (x,y,d) = false}

def kernelBijection (m : Model) (valid : Valid m)
    (pins : ∀ i : Fin m.k, m.pin i < m.size) : Bijection (BitVec m.k) (ZeroPair m.two) where
  encode bits := ⟨tabulate m.two (m.generate bits),tabulate_shared _ _,by
    intro x y d hd
    have h := Kernel.generate_good m valid bits x y d hd
    have shared := tabulate_shared m.two (m.generate bits)
    rw [← eval_lookup m.two _ shared]
    simp only [square,Kernel.Quad.val]
    have bound : ∀ (t : Bool) (x y : B), key t x y < (if t then 512 else 256) := by decide
    have first : ∀ a b, key false a b < m.size := by
      intro a b; have h : key false a b < 256 := bound false a b; cases e : m.two <;> simp [Model.size,e] <;> omega
    have last : ∀ a b, key m.two a b < m.size := by intro a b; exact bound m.two a b
    rw [lookup_tabulate m _ _ (first _ _), lookup_tabulate m _ _ (first _ _),
        lookup_tabulate m _ _ (last _ _), lookup_tabulate m _ _ (last _ _)]
    exact h⟩
  decode p := m.read (lookup p.val)
  decode_encode bits := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Kernel.read_bit _ _ hi, lookup_tabulate m _ _ (pins ⟨i,hi⟩)]
    have h := congrArg (fun v : BitVec m.k => v.getLsbD i) (Kernel.read_generate m valid bits)
    simpa only [Kernel.read_bit m _ hi] using h
  encode_decode p := by
    apply Subtype.ext
    have good : Good m.two (lookup p.val) := by
      intro x y d hd
      rw [eval_lookup m.two p.val p.property.1]
      exact p.property.2 x y d hd
    have bound : ∀ (t : Bool) (x y : B), key t x y < (if t then 512 else 256) := by decide
    apply Prod.ext
    · funext x y
      have h : key false x y < 256 := bound false x y
      have hi : key false x y < m.size := by cases he : m.two <;> simp [Model.size,he] <;> omega
      exact (Kernel.generate_read m valid _ good _ hi).trans (lookup_key _ false _ _)
    · funext x y
      change m.generate (m.read (lookup p.val)) (key m.two x y) = p.val.2 x y
      have h := Kernel.generate_read m valid _ good _ (bound m.two x y)
      rw [lookup_key] at h
      by_cases he : m.two = false
      · have sh := p.property.1 he
        simpa [tabulate,he,sh] using h
      · have on : m.two = true := by cases ht : m.two <;> simp_all
        simpa [tabulate,on] using h

noncomputable def ofBijective {α β : Type} (f : α → β)
    (inj : ∀ a b, f a = f b → a=b) (surj : ∀ b, ∃ a, f a = b) : Bijection α β where
  encode := f
  decode b := Classical.choose (surj b)
  decode_encode a := inj _ a (Classical.choose_spec (surj _))
  encode_decode b := Classical.choose_spec (surj b)

def plus (p q : Pair) : Pair :=
  (fun x y => p.1 x y ^^ q.1 x y,fun x y => p.2 x y ^^ q.2 x y)

theorem plus_twice (p q : Pair) : plus (plus p q) q = p := by
  apply Prod.ext <;> funext x y <;> simp [plus]

private theorem plus_shared {p q : Pair} {t : Bool} (hp : Shared t p) (hq : Shared t q) :
    Shared t (plus p q) := by
  intro ht
  simp [plus,hp ht,hq ht]

theorem score_plus (p q : Pair) (x y d : B) :
    score (plus p q).1 (plus p q).2 (x,y,d) = (score p.1 p.2 (x,y,d) ^^ score q.1 q.2 (x,y,d)) := by
  simp [plus,score,Mobius.TwoPhases.corners,Mobius.SignObstruction.total,
    Bool.xor_comm,Bool.xor_left_comm]

abbrev Direction := {d : B // d ≠ 0}

def ground (d : Direction) : Pair :=
  let q := Mobius.SignObstruction.quotient d.val
  let p := fun x y => Mobius.EightSquare.phase (q x) (q y)
  (p,p)

theorem ground_pattern (d : Direction) : DirectionPattern (ground d).1 (ground d).2 d.val := by
  refine ⟨d.property,?_⟩
  intro x y e he
  let q := Mobius.SignObstruction.quotient d.val
  let f := Mobius.EightSquare.phase
  have law (a b s : BitVec 3) : (f a b ^^ f (a ^^^ s) (b ^^^ s) ^^ f a (b ^^^ s) ^^ f (a ^^^ s) b) = decide (s ≠ 0) := by
    revert a b s
    decide
  have qlin (a b : B) : q (a ^^^ b) = q a ^^^ q b := Mobius.SignObstruction.quotient_linear _ _ _
  have mix : score (ground d).1 (ground d).2 (x,y,e) = decide (q e ≠ 0) := by
    have h := law (q x) (q y) (q e)
    unfold ground score Mobius.TwoPhases.corners Mobius.SignObstruction.total
    change (f (q x) (q y) ^^ (f (q (x ^^^ e)) (q (y ^^^ e)) ^^ (f (q x) (q (y ^^^ e)) ^^ (f (q (x ^^^ e)) (q y) ^^ false)))) = _
    simpa [qlin, Bool.xor_assoc] using h
  rw [mix]
  by_cases eqn : e = d.val
  · subst e
    have zero : ∀ a : B, Mobius.SignObstruction.quotient a a = 0 := by decide
    simp [q,zero]
  · have nz : q e ≠ 0 := Mobius.SignObstruction.quotient_nonzero _ _ d.property he eqn
    exact (decide_eq_true nz).trans (decide_eq_true eqn).symm

private theorem ground_shared (d : Direction) (two : Bool) : Shared two (ground d) := fun _ => rfl

def OptPairs (two : Bool) := {p : Pair // Shared two p ∧ Mobius.TwoPhases.failures p.1 p.2 = 256}

private def attach (t : Bool) (v : Direction × ZeroPair t) : OptPairs t :=
  let q := ground v.1
  let p := plus v.2.val q
  ⟨p,plus_shared v.2.property.1 (ground_shared _ _), optimal_of_direction (d := v.1.val) ⟨v.1.property,by
    intro x y e he
    rw [show score p.1 p.2 (x,y,e) = _ from score_plus _ _ _ _ _, v.2.property.2 x y e he]
    simpa [q] using (ground_pattern v.1).2 x y e he⟩⟩

private theorem attached_pattern (t : Bool) (v : Direction × ZeroPair t) :
    DirectionPattern (attach t v).val.1 (attach t v).val.2 v.1.val := by
  refine ⟨v.1.property,?_⟩
  intro x y e he
  change score (plus _ _).1 (plus _ _).2 (x,y,e) = _
  rw [score_plus,v.2.property.2 x y e he]
  simpa using (ground_pattern v.1).2 x y e he

noncomputable def optimumBijection (t : Bool) : Bijection (Direction × ZeroPair t) (OptPairs t) :=
  ofBijective (attach t) (by
    intro a b h
    have pa := attached_pattern t a
    have pb := attached_pattern t b
    rw [← h] at pb
    obtain ⟨d,_,uniq⟩ := optimal_direction _ _ (attach t a).property.2
    have eqd : a.1 = b.1 := Subtype.ext ((uniq _ pa).trans (uniq _ pb).symm)
    apply Prod.ext eqd (Subtype.ext ?_)
    have hp := congrArg Subtype.val h
    change plus a.2.val (ground a.1) = plus b.2.val (ground b.1) at hp
    rw [eqd] at hp
    simpa only [plus_twice] using congrArg (fun p => plus p (ground b.1)) hp) (by
    intro p
    obtain ⟨d,pat,_⟩ := optimal_direction _ _ p.property.2
    let label : Direction := ⟨d,pat.1⟩
    let q := ground label
    let z : ZeroPair t := ⟨plus p.val q, plus_shared p.property.1 (ground_shared _ _),by
      intro x y e he
      rw [score_plus,pat.2 x y e he,(ground_pattern label).2 x y e he]
      simp [label]⟩
    exact ⟨(label,z),Subtype.ext (plus_twice p.val q)⟩)

private def label (i : Fin 15) : Direction := ⟨BitVec.ofNat 4 (i.val+1),by revert i; decide⟩

noncomputable def labelBijection : Bijection (Fin 15) Direction := ofBijective label (by
  intro a b h
  have injective : ∀ a b : Fin 15, (label a).val = (label b).val → a=b := by decide
  exact injective a b (congrArg Subtype.val h)) (by
  rintro ⟨d,hd⟩
  have surjective : ∀ z : B, z ≠ 0 → ∃ a : Fin 15, (label a).val = z := by decide
  obtain ⟨a,h⟩ := surjective d hd
  exact ⟨a,Subtype.ext h⟩)

def product {α β γ δ : Type} (a : Bijection α β) (b : Bijection γ δ) : Bijection (α × γ) (β × δ) where
  encode v := (a.encode v.1,b.encode v.2)
  decode v := (a.decode v.1,b.decode v.2)
  decode_encode _ := Prod.ext (a.decode_encode _) (b.decode_encode _)
  encode_decode _ := Prod.ext (a.encode_decode _) (b.encode_decode _)

private def splitIndex (k : Nat) (i : Fin (15*2^k)) : Fin 15 × BitVec k :=
  (⟨i.val / 2^k,(Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr i.isLt⟩,BitVec.ofNat k i.val)

private def joinIndex (k : Nat) (p : Fin 15 × BitVec k) : Fin (15*2^k) :=
  ⟨2^k*p.1.val+p.2.toNat,by
    have small := p.2.isLt
    have le := Nat.mul_le_mul_left (2^k) (show p.1.val+1 ≤ 15 from p.1.isLt)
    rw [Nat.mul_succ,Nat.mul_comm (2^k) 15] at le
    omega⟩

def indexBijection (k : Nat) : Bijection (Fin (15*2^k)) (Fin 15 × BitVec k) where
  encode := splitIndex k
  decode := joinIndex k
  decode_encode i := Fin.ext (Nat.div_add_mod i.val (2^k))
  encode_decode v := by
    apply Prod.ext
    · apply Fin.ext
      change (2^k*v.1.val+v.2.toNat) / 2^k = v.1.val
      rw [Nat.mul_add_div (Nat.two_pow_pos k),Nat.div_eq_of_lt v.2.isLt,Nat.add_zero]
    · apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat k (2^k*v.1.val+v.2.toNat)).toNat = v.2.toNat
      rw [BitVec.toNat_ofNat,Nat.mul_add_mod,Nat.mod_eq_of_lt v.2.isLt]

private def forgetDouble : Bijection (OptPairs true) {p : Pair // Mobius.TwoPhases.failures p.1 p.2 = 256} where
  encode p := ⟨p.val,p.property.2⟩
  decode p := ⟨p.val,by intro h; contradiction,p.property⟩
  decode_encode _ := rfl
  encode_decode _ := rfl

private def forgetSingle : Bijection (OptPairs false) {p : Phase // Mobius.SignObstruction.failures p = 256} where
  encode p := ⟨p.val.1,by
    have sh := p.property.1 rfl
    have opt := p.property.2
    rw [sh,same_count] at opt
    exact opt⟩
  decode p := ⟨(p.val,p.val),fun _ => rfl,(same_count p.val).trans p.property⟩
  decode_encode p := Subtype.ext (Prod.ext rfl (p.property.1 rfl).symm)
  encode_decode _ := rfl

/-- The entire set of optimal single-phase tables, each with a distinct finite index. -/
noncomputable def count_single : Bijection (Fin (15*2^42))
    {p : Phase // Mobius.SignObstruction.failures p = 256} :=
  ((indexBijection 42).thenDo (product labelBijection
    (kernelBijection Kernel.single Kernel.single_valid (by decide)))).thenDo
    ((optimumBijection false).thenDo forgetSingle)

/-- The entire set of ordered optimal row/column phase pairs, each with a distinct finite index. -/
noncomputable def count_double : Bijection (Fin (15*2^62))
    {p : Pair // Mobius.TwoPhases.failures p.1 p.2 = 256} :=
  ((indexBijection 62).thenDo (product labelBijection
    (kernelBijection Kernel.double Kernel.double_valid (by decide)))).thenDo
    ((optimumBijection true).thenDo forgetDouble)

end Mobius.Rigidity.Enumeration
