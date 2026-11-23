import Mobius.RigidityEnumeration
import Mobius.RigidityBacktrackData

/-! In the directed two-sheeted cover of the bipartite row-column graph,
immediate reversal flips the sheet by R(x,y) xor C(x,y). At an optimal
signing such a voltage has only a freely chosen color component and one
linear character. -/
namespace Mobius.Rigidity.Backtracks
open Mobius.SignObstruction (B)
open Mobius.Rigidity.Enumeration (Phase Pair Direction ground plus ZeroPair OptPairs)
open Mobius.Rigidity.Kernel (key double dot dot_xor)
open Mobius.TwoPhases (score)

set_option maxRecDepth 16384
set_option maxHeartbeats 100000

def voltage (p : Pair) (x y : B) := p.1 x y ^^ p.2 x y

def Law (p : Pair) := ∃ (k l : B → Bool),
    (∀ x y, l (x ^^^ y) = (l x ^^ l y)) ∧ ∀ x y, voltage p x y = (k (x ^^^ y) ^^ l x)

private theorem zero_law (p : ZeroPair true) : Law p.val := by
  let v := Enumeration.lookup p.val
  let bits := double.read v
  have good : Kernel.Good true v := by
    intro a b d hd
    rw [Enumeration.eval_lookup true p.val p.property.1]
    exact p.property.2 _ _ _ hd
  have cell (tag : Bool) (x y : B) : (if tag then p.val.2 else p.val.1) x y =
      double.generate bits (key tag x y) := by
    have bound : ∀ (t : Bool) (a b : B), key t a b < 512 := by decide
    exact ((Kernel.generate_read double Kernel.double_valid v good _ (bound tag x y)).trans
      (Enumeration.lookup_key p.val tag x y)).symm
  let value := dot bits.getLsbD double.k
  refine ⟨fun z => value (mask 0 z), fun x => value (linMask x), ?_, ?_⟩
  · intro x y
    exact (congrArg value (mask_linear x y)).trans (dot_xor _ _ _ _)
  · intro x y
    have row : p.val.1 x y = double.generate bits (key false x y) := cell false x y
    have col : p.val.2 x y = double.generate bits (key true x y) := cell true x y
    unfold voltage
    rw [row,col]
    calc
      _ = value (mask x y) := (dot_xor _ _ _ _).symm
      _ = value (mask 0 (x ^^^ y) ^^^ linMask x) := congrArg value (mask_form x y)
      _ = _ := dot_xor _ _ _ _

private theorem shift_law (p : Pair) (d : Direction) (h : Law (plus p (ground d))) : Law p := by
  obtain ⟨k,l,hl,form⟩ := h
  refine ⟨k,l,hl,?_⟩
  intro x y
  have eqn := form x y
  have same : voltage (plus p (ground d)) x y = voltage p x y := by
    change ((p.1 x y ^^ (ground d).1 x y) ^^ (p.2 x y ^^ (ground d).1 x y)) = (p.1 x y ^^ p.2 x y)
    cases p.1 x y <;> cases p.2 x y <;> cases (ground d).1 x y <;> rfl
  exact same.symm.trans eqn

/-- Necessary form of immediate-backtrack voltages at every optimum. -/
theorem optimal_law (r c : Phase) (opt : Mobius.TwoPhases.failures r c = 256) : Law (r,c) := by
  obtain ⟨h,pat,_⟩ := optimal_direction r c opt
  let d : Direction := ⟨h,pat.1⟩
  apply shift_law _ d
  have zero (x y e : B) (he : e ≠ 0) :
      score (plus (r,c) (ground d)).1 (plus (r,c) (ground d)).2 (x,y,e) = false := by
    rw [Enumeration.score_plus]
    change (score r c _ ^^ score (ground d).1 (ground d).2 _) = false
    rw [pat.2 x y e he,(Enumeration.ground_pattern d).2 x y e he]
    exact Bool.xor_self _
  exact zero_law ⟨plus (r,c) (ground d), fun h => Bool.noConfusion h, zero⟩

end Mobius.Rigidity.Backtracks
