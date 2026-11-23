import Mobius.UnaryWitness
import Mobius.WitnessStream
import Mobius.Bounded

/-! Positive fooling families at arbitrary cuts of the actual unary-index
3-SAT language. The multiplicative support factor is an explicitly indexed
library of assignments that covers all sets within the unary price budget. -/
namespace Mobius.WitnessCut
open Complexity.SAT
open Mobius.WitnessStream (State step states)
open Mobius.UnaryWitness (price)

def Covers (N : Nat) (library : Fin K → Assignment) : Prop :=
  ∀ ids : List Nat, ids.Nodup → price ids ≤ N → ∃ j, library j = fun i => ids.contains i

def Positive (l r : Fin m → Word) : Prop :=
  (∀ i, ThreeSAT (l i ++ r i)) ∧
  ∀ i j, ThreeSAT (l i ++ r j) → ThreeSAT (l j ++ r i) → i=j

private theorem sparse_accept (N : Nat) (library : Fin K → Assignment) (covers : Covers N library)
    (w : Word) (len : w.length ≤ N) (yes : ThreeSAT w) :
    ∃ j, WitnessStream.accepts (library j) w = true := by
  obtain ⟨f,enc,three,sat⟩ := yes
  obtain ⟨ids,distinct,cheap,satisfies⟩ := UnaryWitness.sparse_witness f sat
  obtain ⟨j,hj⟩ := covers ids distinct (Nat.le_trans (enc ▸ cheap) len)
  exact ⟨j,(WitnessStream.accept_iff_encoded _ _).mpr ⟨f,enc,three,hj ▸ satisfies⟩⟩

private theorem pool_len (is : List α) (ss : List β) :
    (is.flatMap (fun i => ss.map (fun s => (i,s)))).length = is.length * ss.length := by
  induction is with
  | nil => simp
  | cons i is ih => simp [List.flatMap_cons, ih, Nat.succ_mul,Nat.add_comm]

/-- No correctness assumption on a proposed interface is supplied. Both
    parts of the interface come from the sparse-witness theorem and the
    streaming parser itself. The two cross words need not be well-formed. -/
theorem cover_bound {N K m : Nat} (library : Fin K → Assignment) (covers : Covers N library)
    (l r : Fin m → Word) (short : ∀ i, (l i ++ r i).length ≤ N) (fam : Positive l r) :
    m ≤ K * (states N).length := by
  classical
  let key (i : Fin m) := Classical.choose (sparse_accept N library covers _ (short i) (fam.1 i))
  have own (i : Fin m) : WitnessStream.accepts (library (key i)) (l i ++ r i) = true :=
    Classical.choose_spec (sparse_accept N library covers _ (short i) (fam.1 i))
  let st (i : Fin m) := (l i).foldl (step (library (key i))) (.header 0)
  let label (i : Fin m) := (key i,st i)
  let pool := (List.finRange K).flatMap fun j => (states N).map (fun s => (j,s))
  have member (i : Fin m) : label i ∈ pool := by
    apply List.mem_flatMap.mpr
    refine ⟨key i,by simp,List.mem_map.mpr ⟨st i,?_,rfl⟩⟩
    apply WitnessStream.prefix_mem_of_le
    have len := short i
    rw [List.length_append] at len
    omega
  have injective {i j : Fin m} (eq : label i = label j) : i=j := by
    obtain ⟨hk,hs⟩ := Prod.mk.inj eq
    change key i=key j at hk
    change (l i).foldl (step (library (key i))) (.header 0) =
      (l j).foldl (step (library (key j))) (.header 0) at hs
    rw [hk] at hs
    apply fam.2 i j
    · exact WitnessStream.mixed_sound _ _ _ _ hs (own j)
    · exact WitnessStream.mixed_sound _ _ _ _ hs.symm (hk ▸ own i)
  let code (i : Fin m) : Fin pool.length := ⟨pool.idxOf (label i),List.idxOf_lt_length_of_mem (member i)⟩
  have bound := Bounded.fin_size_le code (fun i j h => by
    apply injective
    have get := congrArg (fun k : Fin pool.length => pool[k.val]) h
    simpa only [code,List.getElem_idxOf] using get)
  simpa only [pool,pool_len,List.length_finRange] using bound

/-- The same estimate stated for physical cuts of concrete length-N words. -/
theorem fixed_cut_bound {N K m : Nat} (library : Fin K → Assignment) (covers : Covers N library)
    (words : Fin m → Word) (cut : Nat) (short : ∀ i, (words i).length ≤ N)
    (yes : ∀ i, ThreeSAT (words i))
    (separate : ∀ i j, ThreeSAT ((words i).take cut ++ (words j).drop cut) →
      ThreeSAT ((words j).take cut ++ (words i).drop cut) → i=j) :
    m ≤ K * (2 + (N+1) + 3*(N+1)^2 + 4*(N+1)^3) := by
  rw [← WitnessStream.states_length]
  apply cover_bound library covers (fun i => (words i).take cut) (fun i => (words i).drop cut)
  · simpa only [List.take_append_drop] using short
  · exact ⟨fun i => by simpa only [List.take_append_drop] using yes i,separate⟩

end Mobius.WitnessCut
