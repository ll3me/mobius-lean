import Mobius.BoundaryProbe
import Mobius.Bounded

/-! A one-pass interface for the ordinary binary encoding of BoundaryProbe.
All four ports vary. Only correctness on these 65,536 promised words is
assumed. Width at the cut is distinguished from total scanner state count. -/
namespace Mobius.BoundaryScan

open Complexity.SAT Mobius.BoundaryProbe

set_option maxRecDepth 8192

private def firstEight (x y : B) := (probe x y 0 0).take 8
private def lastEight (u v : B) := (probe 0 0 u v).drop 8

def prefixWord (x y : B) : Word := writeNat 16 ++ writeValues encodeClause (firstEight x y)
def suffixWord (u v : B) : Word := writeValues encodeClause (lastEight u v)

private theorem bodies (x y u v : B) : probe x y u v = firstEight x y ++ lastEight u v := rfl

private theorem write_append (f : α → Word) (a b : List α) :
    writeValues f (a ++ b) = writeValues f a ++ writeValues f b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, writeValues, ih, List.append_assoc]

theorem encode_split (x y u v : B) : encode (probe x y u v) = prefixWord x y ++ suffixWord u v := by
  unfold encode writeList
  rw [probe_length, bodies, write_append]
  exact (List.append_assoc ..).symm

theorem prefix_length (x y : B) : (prefixWord x y).length = 77 := by rfl
theorem suffix_length (u v : B) : (suffixWord u v).length = 60 := by rfl

theorem word_length (x y u v : B) : (encode (probe x y u v)).length = 137 := by
  rw [encode_split, List.length_append, prefix_length, suffix_length]

def Correct (initial : σ) (step : σ → Bool → σ) (accept : σ → Bool) : Prop :=
  ∀ x y u v : B, accept ((encode (probe x y u v)).foldl step initial) = true ↔
    ThreeSAT (encode (probe x y u v))

theorem seam_injective (initial : σ) (step : σ → Bool → σ) (accept : σ → Bool)
    (correct : Correct initial step accept) {x y x' y' : B}
    (same : (prefixWord x y).foldl step initial = (prefixWord x' y').foldl step initial) :
    x = x' ∧ y = y' := by
  have own := (correct x' y' y' x').mpr ((probe_threeSAT_iff ..).mpr ⟨rfl,rfl⟩)
  have mixed := (correct x y y' x').trans (probe_threeSAT_iff ..)
  rw [encode_split, List.foldl_append] at own mixed
  exact mixed.mp (same ▸ own)

private def lo (i : Fin 256) : B := BitVec.ofNat 4 i.val
private def hi (i : Fin 256) : B := BitVec.ofNat 4 (i.val / 16)

private theorem restored (i : Fin 256) : (hi i).toNat * 16 + (lo i).toNat = i.val := by
  revert i; decide

theorem one_pass_lower_bound (initial : Fin s) (step : Fin s → Bool → Fin s)
    (accept : Fin s → Bool) (correct : Correct initial step accept) : 256 ≤ s := by
  apply Bounded.fin_size_le (fun i : Fin 256 => (prefixWord (lo i) (hi i)).foldl step initial)
  intro i j same
  have eq := seam_injective initial step accept correct same
  apply Fin.ext
  calc
    _ = (hi i).toNat * 16 + (lo i).toNat := (restored i).symm
    _ = (hi j).toNat * 16 + (lo j).toNat := by rw [eq.1,eq.2]
    _ = _ := restored j

/-- Read four signs at their wire-format offsets (least significant bit first). -/
private def signs (w : Word) (i j k l : Nat) : B :=
  BitVec.ofBoolListLE [w.getD i false,w.getD j false,w.getD k false,w.getD l false]

private def firstPair (w : Word) : B × B :=
  (signs w 19 23 28 34, signs w 41 49 58 68)

private def lastPair (w : Word) : B × B :=
  (signs w 2 10 19 29, signs w 40 44 49 55)

private theorem rebuild (x : B) :
    BitVec.ofBoolListLE [x.getLsbD 0,x.getLsbD 1,x.getLsbD 2,x.getLsbD 3] = x := by
  revert x; decide

private theorem firstPair_reads (x y : B) : firstPair (prefixWord x y) = (x,y) := by
  apply Prod.ext
  · exact rebuild x
  · exact rebuild y

private theorem lastPair_reads (u v : B) : lastPair (suffixWord u v) = (u,v) := by
  apply Prod.ext
  · exact rebuild u
  · exact rebuild v

/-- A direct uniform construction. It uses extra temporary storage while
    reading the two segments and exactly two four-bit registers at the cut. -/
inductive Buffered where
  | before (initialBits : Word)
  | after (remember : B × B) (trailingBits : Word)

private def stage (w : Word) : Buffered :=
  if w.length < 77 then .before w else .after (firstPair (w.take 77)) (w.drop 77)

def bufferedStep (s : Buffered) (b : Bool) : Buffered := match s with
  | .before w => stage (w ++ [b])
  | .after p w => .after p (w ++ [b])

def bufferedAccept : Buffered → Bool
  | .before _ => false
  | .after p w => decide (p.1 = (lastPair w).2 ∧ p.2 = (lastPair w).1)

private theorem stage_step (w : Word) (b : Bool) :
    bufferedStep (stage w) b = stage (w ++ [b]) := by
  by_cases short : w.length < 77
  · simp only [stage, short, ↓reduceIte, bufferedStep]
  · have hi : 77 ≤ w.length := by omega
    have longer : ¬ (w ++ [b]).length < 77 := by simp; omega
    simp only [stage,short,longer,↓reduceIte,bufferedStep,List.take_append_of_le_length hi,
      List.drop_append_of_le_length hi]

private theorem buffered_run (w tail : Word) :
    tail.foldl bufferedStep (stage w) = stage (w ++ tail) := by
  induction tail generalizing w with
  | nil => simp
  | cons b bs ih => rw [List.foldl_cons, stage_step, ih]; simp [List.append_assoc]

private theorem from_start (w : Word) : w.foldl bufferedStep (.before []) = stage w := by
  simpa only [show stage [] = .before [] by rfl, List.nil_append] using buffered_run [] w

/-- This state is the whole interface between the two input segments. -/
theorem buffered_at_cut (x y : B) :
    (prefixWord x y).foldl bufferedStep (.before []) = .after (x,y) [] := by
  rw [from_start]
  have len := prefix_length x y
  have take : (prefixWord x y).take 77 = prefixWord x y := by rw [← len]; simp
  have drop : (prefixWord x y).drop 77 = [] := by rw [← len]; simp
  simp only [stage, len, Nat.lt_irrefl, ↓reduceIte,take,drop,firstPair_reads]

private theorem after_run (p : B × B) (ws tail : Word) :
    tail.foldl bufferedStep (.after p ws) = .after p (ws ++ tail) := by
  induction tail generalizing ws with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons]
    change bs.foldl bufferedStep (.after p (ws ++ [b])) = _
    rw [ih]
    simp [List.append_assoc]

theorem buffered_correct : Correct (.before []) bufferedStep bufferedAccept := by
  intro x y u v
  rw [probe_threeSAT_iff, encode_split, List.foldl_append, buffered_at_cut, after_run]
  simp [bufferedAccept,lastPair_reads]

end Mobius.BoundaryScan
