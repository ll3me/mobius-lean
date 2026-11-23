import Mobius.BoundarySemantics

/-! Ordinary CNF contexts whose boundary multiset is empty, a singleton,
or an ordered pair (including a repeated key). All contexts use four
declared variables. Variables 0 and 1 supply the Boolean constants;
variables 2 and 3 carry the two opposite values of the branch selector. -/
namespace Mobius.BoundaryChoice

open Complexity.SAT Mobius.BoundarySemantics

structure Context where
  base : CNF
  ports : Ports
  base_three : IsThreeCNF base

def Context.score (c : Context) (t : Key → Int) : Int := contract 4 c.base c.ports t

def Context.word (c : Context) : Word := encode (glue c.base c.ports)

theorem Context.glue_three (c : Context) : IsThreeCNF (glue c.base c.ports) :=
  glue_threeCNF c.base c.ports c.base_three

private def pairBase : CNF :=
  [[⟨0,false⟩], [⟨1,true⟩], [⟨2,true⟩,⟨3,true⟩], [⟨2,false⟩,⟨3,false⟩]]

private def pointBase : CNF := [⟨3,false⟩] :: pairBase
private def emptyBase : CNF := [] :: pairBase

private def slot : Bool → Bool → Nat
  | false, false => 0
  | true, true => 1
  | true, false => 2
  | false, true => 3

private def choosePort (p q : B) : Port :=
  ⟨slot (p.getLsbD 0) (q.getLsbD 0), slot (p.getLsbD 1) (q.getLsbD 1),
   slot (p.getLsbD 2) (q.getLsbD 2), slot (p.getLsbD 3) (q.getLsbD 3)⟩

private def choosePorts (p q : Key) : Ports :=
  ⟨choosePort p.x q.x, choosePort p.y q.y, choosePort p.u q.u, choosePort p.v q.v⟩

private theorem base_three : IsThreeCNF pairBase := by
  intro c hc
  simp only [pairBase, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

private theorem cons_three (c : Clause) (h : c.length ≤ 3) : IsThreeCNF (c :: pairBase) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact h
  · exact base_three d hd

def empty : Context := ⟨emptyBase,choosePorts ⟨0,0,0,0⟩ ⟨0,0,0,0⟩,cons_three _ (by decide)⟩
def point (q : Key) : Context := ⟨pointBase,choosePorts q q,cons_three _ (by decide)⟩
def pair (q₀ q₁ : Key) : Context := ⟨pairBase,choosePorts q₀ q₁,base_three⟩

private theorem bound_append (f g : CNF) :
    variableBound (f ++ g) = max (variableBound f) (variableBound g) := by
  induction f with
  | nil => simp [variableBound]
  | cons c f ih => simp only [List.cons_append, variableBound, ih, Nat.max_assoc]

private theorem slot_bound (a b : Bool) : slot a b + 1 ≤ 4 := by
  cases a <;> cases b <;> decide

private theorem bounded_wire (p q r s : B) :
    variableBound (equalPorts (choosePort p q) (choosePort r s)) ≤ 4 := by
  simp only [equalPorts, bound_append, Nat.max_le, choosePort, equalBits, variableBound, clauseBound]
  simp [slot_bound]

private theorem glue_bound (f : CNF) (four : variableBound f = 4) (p q : Key) :
    variableBound (glue f (choosePorts p q)) = 4 := by
  simp only [glue, choosePorts, bound_append, four]
  rw [Nat.max_eq_left (bounded_wire ..), Nat.max_eq_left (bounded_wire ..)]

theorem empty_bound : variableBound (glue empty.base empty.ports) = 4 :=
  glue_bound emptyBase (by decide) _ _

theorem point_bound (q : Key) :
    variableBound (glue (point q).base (point q).ports) = 4 :=
  glue_bound pointBase (by decide) q q

theorem pair_bound (p q : Key) :
    variableBound (glue (pair p q).base (pair p q).ports) = 4 :=
  glue_bound pairBase (by decide) p q

private def branch (flag : Bool) : Finite 4 := fun i =>
  match i.val with
  | 0 => false
  | 1 => true
  | 2 => !flag
  | _ => flag

private def assignmentDecEq : DecidableEq (Finite 4) := fun f g =>
  decidable_of_iff (∀ i, f i = g i) ⟨funext, fun h i => congrFun h i⟩

private theorem model_pair : models 4 pairBase = [branch false,branch true] := by
  letI := assignmentDecEq
  decide

private theorem model_point : models 4 pointBase = [branch false] := by
  letI := assignmentDecEq
  decide

private theorem model_empty : models 4 emptyBase = [] := by rfl

private theorem read_slot (a : Assignment) (flag : Bool) (h₀ : a 0 = false) (h₁ : a 1 = true)
    (h₂ : a 2 = !flag) (h₃ : a 3 = flag) (p q : Bool) :
    a (slot p q) = if flag then q else p := by
  cases flag <;> cases p <;> cases q <;> simp_all [slot]

private theorem rebuild (x : B) : BitVec.ofBoolListLE
    [x.getLsbD 0,x.getLsbD 1,x.getLsbD 2,x.getLsbD 3] = x := by revert x; decide

private theorem read_port (a : Assignment) (flag : Bool) (h₀ : a 0 = false) (h₁ : a 1 = true)
    (h₂ : a 2 = !flag) (h₃ : a 3 = flag) (p q : B) :
    (choosePort p q).read a = if flag then q else p := by
  unfold choosePort Port.read
  rw [read_slot a flag h₀ h₁ h₂ h₃, read_slot a flag h₀ h₁ h₂ h₃,
    read_slot a flag h₀ h₁ h₂ h₃, read_slot a flag h₀ h₁ h₂ h₃]
  cases flag
  · exact rebuild p
  · exact rebuild q

private theorem read_ports (a : Assignment) (flag : Bool) (h₀ : a 0 = false) (h₁ : a 1 = true)
    (h₂ : a 2 = !flag) (h₃ : a 3 = flag) (p q : Key) :
    (choosePorts p q).read a = if flag then q else p := by
  cases flag <;> simp only [choosePorts, Ports.read, read_port a _ h₀ h₁ h₂ h₃,
    Bool.false_eq_true, ↓reduceIte]

private theorem branch_read (flag : Bool) (p q : Key) :
    (choosePorts p q).read (assignment (branch flag)) = if flag then q else p :=
  read_ports _ flag rfl rfl rfl rfl p q

theorem sample_empty : sample 4 empty.base empty.ports = [] := by
  change (models 4 emptyBase).map _ = []
  rw [model_empty]
  rfl

theorem sample_point (q : Key) : sample 4 (point q).base (point q).ports = [q] := by
  change (models 4 pointBase).map (fun w => (choosePorts q q).read (assignment w)) = [q]
  rw [model_point]
  simp [branch_read]

theorem sample_pair (q₀ q₁ : Key) : sample 4 (pair q₀ q₁).base (pair q₀ q₁).ports = [q₀,q₁] := by
  change (models 4 pairBase).map (fun w => (choosePorts q₀ q₁).read (assignment w)) = [q₀,q₁]
  rw [model_pair]
  simp [branch_read]

theorem score_empty (t : Key → Int) : empty.score t = 0 := by
  rw [Context.score,contract_unfold,sample_empty]
  rfl

theorem score_point (q : Key) (t : Key → Int) : (point q).score t = t q := by
  rw [Context.score,contract_unfold,sample_point]
  simp [sumI]

theorem score_pair (q₀ q₁ : Key) (t : Key → Int) : (pair q₀ q₁).score t = t q₀ + t q₁ := by
  rw [Context.score,contract_unfold,sample_pair]
  simp [sumI]

private theorem pair_eval (a : Assignment) : evalCNF a pairBase = true ↔
    a 0 = false ∧ a 1 = true ∧ a 2 = !(a 3) := by
  cases h₀ : a 0 <;> cases h₁ : a 1 <;> cases h₂ : a 2 <;> cases h₃ : a 3 <;>
    simp [pairBase, evalCNF, evalClause, evalLiteral, h₀, h₁, h₂, h₃]

private theorem test (c : Context) : ThreeSAT c.word ↔
    ∃ a, evalCNF a c.base = true ∧ closes (c.ports.read a) = true := by
  simp only [Context.word, ThreeSAT_encode_iff, c.glue_three, true_and, Satisfiable, glue_eval,
    Bool.and_eq_true]

theorem not_threeSAT_empty : ¬ThreeSAT empty.word := by
  rw [test]
  rintro ⟨a, h, _⟩
  change evalCNF a ([] :: pairBase) = true at h
  simp at h

theorem threeSAT_point (q : Key) : ThreeSAT (point q).word ↔ closes q = true := by
  rw [test]
  constructor
  · rintro ⟨a, h, hc⟩
    change evalCNF a ([⟨3,false⟩] :: pairBase) = true at h
    have p := (Bool.and_eq_true_iff.mp h).2
    obtain ⟨h₀,h₁,h₂⟩ := (pair_eval a).mp p
    simpa only [point, read_ports a (a 3) h₀ h₁ h₂ rfl, ite_self] using hc
  · intro yes
    refine ⟨assignment (branch false),rfl,?_⟩
    simpa only [point, branch_read, ite_self] using yes

theorem threeSAT_pair (q₀ q₁ : Key) : ThreeSAT (pair q₀ q₁).word ↔
    closes q₀ = true ∨ closes q₁ = true := by
  rw [test]
  constructor
  · rintro ⟨a, h, hc⟩
    obtain ⟨h₀,h₁,h₂⟩ := (pair_eval a).mp h
    change closes ((choosePorts q₀ q₁).read a) = true at hc
    rw [read_ports a (a 3) h₀ h₁ h₂ rfl] at hc
    cases h : a 3
    · exact Or.inl (by simpa [h] using hc)
    · exact Or.inr (by simpa [h] using hc)
  · rintro (h | h)
    · refine ⟨assignment (branch false),rfl,?_⟩
      simpa only [pair, branch_read, Bool.false_eq_true, ↓reduceIte] using h
    · refine ⟨assignment (branch true),rfl,?_⟩
      simpa only [pair, branch_read, ↓reduceIte] using h

end Mobius.BoundaryChoice
