import Complexity.SAT
import Std

/-! A one-way verifier for the upstream binary encoding of ordinary 3-CNF.
The assignment is a fixed read-only parameter. The parser stores counters
for unary fields, a literal sign, and one current-clause truth bit. -/
namespace Mobius.WitnessStream
open Complexity.SAT

inductive State where
  | header (seen : Nat)
  | width (laterClauses seen : Nat)
  | sign (laterClauses laterLits : Nat) (hit : Bool)
  | index (laterClauses laterLits seen : Nat) (hit polarity : Bool)
  | done
  | dead
  deriving DecidableEq, Repr

def nextClause : Nat → State
  | 0 => .done
  | n+1 => .width n 0

def nextLiteral (clauses : Nat) (hit : Bool) : Nat → State
  | 0 => if hit then nextClause clauses else .dead
  | n+1 => .sign clauses n hit

def step (T : Assignment) : State → Bool → State
  | .header n, true => .header (n+1)
  | .header n, false => nextClause n
  | .width c n, true => .width c (n+1)
  | .width c n, false => if n ≤ 3 then nextLiteral c false n else .dead
  | .sign c l h, b => .index c l 0 h b
  | .index c l n h b, true => .index c l (n+1) h b
  | .index c l n h b, false => nextLiteral c (h || evalLiteral T ⟨n,b⟩) l
  | .done, _ => .dead
  | .dead, _ => .dead

def accepts (T : Assignment) (w : Word) : Bool := decide (w.foldl (step T) (.header 0) = .done)

private def Unary (seen : Nat) (P : Nat → Word → Prop) (w : Word) : Prop :=
  ∃ d rest, writeNat d ++ rest = w ∧ P (seen+d) rest

private theorem unary_nil (n : Nat) (P : Nat → Word → Prop) : ¬Unary n P [] := by
  rintro ⟨d,rest,eq,_⟩
  cases d <;> simp [writeNat] at eq

private theorem unary_zero (n : Nat) (P : Nat → Word → Prop) (w : Word) :
    Unary n P (false::w) ↔ P n w := by
  constructor
  · rintro ⟨d,rest,eq,h⟩
    cases d with
    | zero => change false :: rest = false :: w at eq; exact (List.cons.inj eq).2 ▸ h
    | succ d => simp [writeNat] at eq
  · exact fun h => ⟨0,w,rfl,h⟩

private theorem unary_one (n : Nat) (P : Nat → Word → Prop) (w : Word) :
    Unary n P (true::w) ↔ Unary (n+1) P w := by
  constructor
  · rintro ⟨d,rest,eq,h⟩
    cases d with
    | zero => simp [writeNat] at eq
    | succ d =>
      change true :: (writeNat d ++ rest) = true :: w at eq
      exact ⟨d,rest,(List.cons.inj eq).2, by simpa only [Nat.add_succ,Nat.succ_add] using h⟩
  · rintro ⟨d,rest,eq,h⟩
    exact ⟨d+1,rest,congrArg (true::·) eq, by simpa only [Nat.add_succ,Nat.succ_add] using h⟩

/-- Specification-only suffix languages. The streaming state stores none
    of these lists. -/
private def Bodies (T : Assignment) (r : Nat) (w : Word) : Prop :=
  ∃ f : CNF, f.length = r ∧ writeValues encodeClause f = w ∧
    IsThreeCNF f ∧ evalCNF T f = true

private def Literals (T : Assignment) (r n : Nat) (hit : Bool) (w : Word) : Prop :=
  ∃ ls : Clause, ∃ tail : Word, ls.length = n ∧ writeValues encodeLiteral ls ++ tail = w ∧
    (hit || evalClause T ls) = true ∧ Bodies T r tail

private theorem bodies_nil (T : Assignment) (w : Word) : Bodies T 0 w ↔ w = [] := by
  constructor
  · rintro ⟨f,len,eq,_⟩
    have hf := List.length_eq_zero_iff.mp len
    subst f
    exact eq.symm
  · rintro rfl
    exact ⟨[],rfl,rfl,by intro c h; simp at h,rfl⟩

private theorem bodies_cons (T : Assignment) (r : Nat) (w : Word) : Bodies T (r+1) w ↔
    Unary 0 (fun n rest => n≤3 ∧ Literals T r n false rest) w := by
  constructor
  · rintro ⟨f,len,encoded,three,good⟩
    cases f with
    | nil => simp at len
    | cons c f =>
      have size := Nat.succ.inj len
      obtain ⟨cg,fg⟩ := Bool.and_eq_true_iff.mp good
      refine ⟨c.length,writeValues encodeLiteral c ++ writeValues encodeClause f, ?_, ?_⟩
      · simpa only [writeValues,encodeClause,writeList,List.append_assoc] using encoded
      · simp only [Nat.zero_add]
        exact ⟨three c (by simp),c,writeValues encodeClause f,rfl,rfl,cg,
          f,size,rfl,(fun d hd => three d (by simp [hd])),fg⟩
  · rintro ⟨n,rest,encoded,width,ls,tail,len,body,hit,f,size,eq,three,good⟩
    simp only [Nat.zero_add] at width len
    refine ⟨ls::f,by simp [size],?_,?_,?_⟩
    · rw [← encoded,← body,← eq,← len]
      simp only [writeValues, encodeClause, writeList, List.append_assoc]
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | inner
      · exact len ▸ width
      · exact three c inner
    · exact Bool.and_eq_true_iff.mpr ⟨hit,good⟩

private theorem lits_nil (T : Assignment) (r : Nat) (h : Bool) (w : Word) :
    Literals T r 0 h w ↔ h = true ∧ Bodies T r w := by
  constructor
  · rintro ⟨ls,tail,len,eq,hit,rest⟩
    have empty := List.length_eq_zero_iff.mp len
    subst ls
    change tail = w at eq
    subst tail
    exact ⟨by simpa using hit,rest⟩
  · rintro ⟨rfl,rest⟩
    exact ⟨[],w,rfl,rfl,rfl,rest⟩

private theorem lits_no_word (T : Assignment) (r l : Nat) (h : Bool) :
    ¬Literals T r (l+1) h [] := by
  rintro ⟨ls,tail,len,enc,_,_⟩
  cases ls with
  | nil => simp at len
  | cons x xs => simp [writeValues,encodeLiteral] at enc

private theorem lits_sign (T : Assignment) (r l : Nat) (h s : Bool) (w : Word) :
    Literals T r (l+1) h (s::w) ↔
    Unary 0 (fun i rest => Literals T r l (h || evalLiteral T ⟨i,s⟩) rest) w := by
  constructor
  · rintro ⟨ls,tail,len,enc,hit,rest⟩
    cases ls with
    | nil => simp at len
    | cons x ls =>
      obtain ⟨i,p⟩ := x
      simp only [writeValues,encodeLiteral,List.cons_append,List.append_assoc,List.cons.injEq] at enc
      obtain ⟨rfl,enc⟩ := enc
      refine ⟨i,writeValues encodeLiteral ls ++ tail,enc,?_⟩
      simp only [Nat.zero_add]
      exact ⟨ls,tail,Nat.succ.inj len,rfl,by simpa only [evalClause_cons,Bool.or_assoc] using hit,rest⟩
  · rintro ⟨i,w',enc,ls,tail,len,body,hit,rest⟩
    simp only [Nat.zero_add] at hit
    refine ⟨⟨i,s⟩::ls,tail,by simp [len],?_,?_,rest⟩
    · rw [← enc,← body]
      simp only [writeValues,encodeLiteral,List.cons_append,List.append_assoc]
    · simpa only [evalClause_cons,Bool.or_assoc] using hit

private def Valid (T : Assignment) : State → Word → Prop
  | .header n,w => Unary n (Bodies T) w
  | .width c n,w => Unary n (fun k rest => k≤3 ∧ Literals T c k false rest) w
  | .sign c l h,w => Literals T c (l+1) h w
  | .index c l n h b,w => Unary n (fun i rest => Literals T c l (h || evalLiteral T ⟨i,b⟩) rest) w
  | .done,w => w=[]
  | .dead,_ => False

private theorem next_clause (T : Assignment) (r : Nat) (w : Word) :
    Valid T (nextClause r) w ↔ Bodies T r w := by
  cases r with
  | zero => exact (bodies_nil ..).symm
  | succ r => exact (bodies_cons ..).symm

private theorem next_literal (T : Assignment) (r n : Nat) (h : Bool) (w : Word) :
    Valid T (nextLiteral r h n) w ↔ Literals T r n h w := by
  cases n with
  | zero =>
    rw [lits_nil]
    cases h <;> simp [nextLiteral,Valid]
    exact next_clause ..
  | succ n => rfl

private theorem derivative (T : Assignment) (s : State) (b : Bool) (w : Word) :
    Valid T s (b::w) ↔ Valid T (step T s b) w := by
  cases s with
  | header n =>
    cases b with
    | true => exact unary_one ..
    | false => exact (unary_zero ..).trans (next_clause ..).symm
  | width c n =>
    let P : Nat → Word → Prop := fun k rest => k≤3 ∧ Literals T c k false rest
    cases b with
    | true => exact unary_one n P w
    | false =>
      rw [step]
      change Unary n P (false::w) ↔ _
      rw [unary_zero]
      by_cases le : n≤3
      · rw [ite_eq_left le,next_literal]
        exact and_iff_right le
      · rw [ite_eq_right le]
        exact iff_of_false (fun h => le h.1) id
  | sign c l h => exact lits_sign ..
  | index c l n h polarity =>
    let P : Nat → Word → Prop := fun i rest => Literals T c l (h || evalLiteral T ⟨i,polarity⟩) rest
    cases b with
    | true => exact unary_one n P w
    | false => exact (unary_zero n P w).trans (next_literal T c l _ w).symm
  | done => simp [Valid,step]
  | dead => rfl

private theorem ending (T : Assignment) (s : State) : Valid T s [] ↔ s = .done := by
  cases s with
  | header n => exact iff_of_false (unary_nil n _) (by intro h; cases h)
  | width c n =>
    exact iff_of_false (unary_nil n (fun k rest => k≤3 ∧ Literals T c k false rest))
      (by intro h; cases h)
  | index c l n h b =>
    exact iff_of_false (unary_nil n (fun i rest => Literals T c l (h || evalLiteral T ⟨i,b⟩) rest))
      (by intro h; cases h)
  | sign c l h => exact iff_of_false (lits_no_word T c l h) (by intro e; cases e)
  | done => simp [Valid]
  | dead => simp [Valid]

private theorem fold_spec (T : Assignment) (s : State) (w : Word) :
    Valid T s w ↔ w.foldl (step T) s = .done := by
  induction w generalizing s with
  | nil => exact ending ..
  | cons b w ih => exact (derivative T s b w).trans (ih _)

theorem accept_iff_encoded (T : Assignment) (w : Word) : accepts T w = true ↔
    ∃ f : CNF, encode f = w ∧ IsThreeCNF f ∧ evalCNF T f = true := by
  rw [accepts,decide_eq_true_eq,← fold_spec]
  constructor
  · rintro ⟨n,tail,header,f,len,eq,three,good⟩
    refine ⟨f,?_,three,good⟩
    simpa only [encode,writeList,len,eq,Nat.zero_add] using header
  · rintro ⟨f,h,three,good⟩
    exact ⟨f.length,writeValues encodeClause f,h,f,by simp,rfl,three,good⟩

theorem encoded_correct (T : Assignment) (f : CNF) : accepts T (encode f) = true ↔
    IsThreeCNF f ∧ evalCNF T f = true := by
  rw [accept_iff_encoded]
  constructor
  · rintro ⟨g,eq,h⟩
    exact encode_injective g f eq ▸ h
  · exact fun h => ⟨f,rfl,h⟩

theorem accept_sound (T : Assignment) (w : Word) (accepted : accepts T w = true) : ThreeSAT w := by
  obtain ⟨f,eq,three,good⟩ := (accept_iff_encoded T w).mp accepted
  exact ⟨f,eq,three,T,good⟩

theorem exists_assignment (w : Word) : (∃ T, accepts T w = true) ↔ ThreeSAT w := by
  constructor
  · rintro ⟨T,h⟩; exact accept_sound T w h
  · rintro ⟨f,eq,three,T,good⟩
    exact ⟨T,(accept_iff_encoded T w).mpr ⟨f,eq,three,good⟩⟩

/-- A bound on each stored counter. T itself is a read-only parameter
    and is not a field of any streaming state. -/
def State.Bounded (N : Nat) : State → Prop
  | .header k => k≤N
  | .width c k => c≤N ∧ k≤N
  | .sign c l _ => c≤N ∧ l≤N
  | .index c l k _ _ => c≤N ∧ l≤N ∧ k≤N
  | .done | .dead => True

private theorem bounded_next_clause {N c : Nat} (h : c≤N) : State.Bounded N (nextClause c) := by
  cases c with
  | zero => trivial
  | succ c => exact ⟨by omega,Nat.zero_le _⟩

private theorem bounded_next_literal {N c n : Nat} (bc : c≤N) (bn : n≤N) (h : Bool) :
    State.Bounded N (nextLiteral c h n) := by
  cases n with
  | zero =>
    cases h
    · trivial
    · exact bounded_next_clause bc
  | succ n => exact ⟨bc,by omega⟩

theorem bounded_step (T : Assignment) (N : Nat) (s : State) (b : Bool) (hs : s.Bounded N) :
    (step T s b).Bounded (N+1) := by
  cases s with
  | header n =>
    cases b
    · exact bounded_next_clause (by exact Nat.le.step hs)
    · exact Nat.succ_le_succ hs
  | width c n =>
    obtain ⟨bc,bn⟩ := hs
    cases b
    · rw [step]
      split
      · exact bounded_next_literal (Nat.le.step bc) (Nat.le.step bn) false
      · trivial
    · exact ⟨Nat.le.step bc,Nat.succ_le_succ bn⟩
  | sign c l hit => exact ⟨Nat.le.step hs.1,Nat.le.step hs.2,Nat.zero_le _⟩
  | index c l n hit fg =>
    obtain ⟨bc,bl,bn⟩ := hs
    cases b
    · exact bounded_next_literal (Nat.le.step bc) (Nat.le.step bl) _
    · exact ⟨Nat.le.step bc,Nat.le.step bl,Nat.succ_le_succ bn⟩
  | done => trivial
  | dead => trivial

private theorem bounded_fold (T : Assignment) (w : Word) (s : State) (N : Nat) (hs : s.Bounded N) :
    (w.foldl (step T) s).Bounded (N+w.length) := by
  induction w generalizing s N with
  | nil => exact hs
  | cons b w ih =>
    have low := ih _ (N+1) (bounded_step T N s b hs)
    simpa only [List.foldl_cons,List.length_cons,Nat.succ_add,Nat.add_succ] using low

theorem prefix_bound (T : Assignment) (w : Word) :
    (w.foldl (step T) (.header 0)).Bounded w.length := by
  simpa only [Nat.zero_add] using bounded_fold T w (.header 0) 0 (Nat.le_refl 0)

private def indexStates (c l k : Nat) : List State :=
  [.index c l k false false,.index c l k false true,.index c l k true false,.index c l k true true]

private def group (N c l : Nat) : List State :=
  [.width c l,.sign c l false,.sign c l true] ++ (List.range (N+1)).flatMap (indexStates c l)

/-- A fixed polynomial-size list covering every state after a prefix of N bits. -/
def states (N : Nat) : List State :=
  [.done,.dead] ++ ((List.range (N+1)).map State.header ++
    (List.range (N+1)).flatMap (fun c => (List.range (N+1)).flatMap (group N c)))

theorem bounded_mem {N : Nat} {s : State} (h : s.Bounded N) : s ∈ states N := by
  have grouped {c l : Nat} (hc : c≤N) (hl : l≤N) {a : State} (ha : a ∈ group N c l) :
      a ∈ states N := by
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨c,List.mem_range.mpr (by omega),
      List.mem_flatMap.mpr ⟨l,List.mem_range.mpr (by omega),ha⟩⟩
  cases s with
  | done => simp [states]
  | dead => simp [states]
  | header n =>
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨n,List.mem_range.mpr (Nat.lt_succ_of_le h),rfl⟩
  | width c l => exact grouped h.1 h.2 (by simp [group])
  | sign c l hit => exact grouped h.1 h.2 (by cases hit <;> simp [group])
  | index c l k hit fg =>
    apply grouped h.1 h.2.1
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (Nat.lt_succ_of_le h.2.2),
      by cases hit <;> cases fg <;> simp [indexStates]⟩

theorem prefix_mem (T : Assignment) (w : Word) :
    w.foldl (step T) (.header 0) ∈ states w.length := bounded_mem (prefix_bound T w)

theorem prefix_mem_of_le (T : Assignment) (w : Word) {N : Nat} (len : w.length ≤ N) :
    w.foldl (step T) (.header 0) ∈ states N := by
  have mono {s : State} (h : s.Bounded w.length) : s.Bounded N := by
    cases s <;> simp_all [State.Bounded] <;> omega
  exact bounded_mem (mono (prefix_bound T w))

/-- One fixed assignment and matching parser states suffice across any
    cut, even when the mixed word was not assumed well-formed. -/
theorem mixed_sound (T : Assignment) (left other right : Word)
    (same : left.foldl (step T) (.header 0) = other.foldl (step T) (.header 0))
    (accepted : accepts T (other++right) = true) : ThreeSAT (left++right) := by
  apply accept_sound T
  unfold accepts at accepted ⊢
  simpa only [List.foldl_append,same] using accepted

private theorem length_flat (xs : List α) (f : α → List β) (n : Nat)
    (h : ∀ a, (f a).length=n) : (xs.flatMap f).length = xs.length*n := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,h,ih,Nat.succ_mul]; omega

theorem states_length (N : Nat) :
    (states N).length = 2 + (N+1) + 3*(N+1)^2 + 4*(N+1)^3 := by
  have groupLen (c l : Nat) : (group N c l).length = 3 + (N+1)*4 := by
    unfold group
    rw [List.length_append,length_flat _ _ 4 (fun _ => rfl),List.length_range]
    rfl
  have inner (c : Nat) : ((List.range (N+1)).flatMap (group N c)).length =
      (N+1)*(3+(N+1)*4) := by
    rw [length_flat _ _ _ (groupLen c),List.length_range]
  unfold states
  rw [List.length_append,List.length_append,List.length_map,length_flat _ _ _ inner,List.length_range]
  change 2+((N+1)+(N+1)*((N+1)*(3+(N+1)*4))) = _
  grind

end Mobius.WitnessStream
