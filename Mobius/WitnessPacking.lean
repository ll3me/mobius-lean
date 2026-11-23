import Mobius.WitnessCut
import Init.Data.Nat.Sqrt

/-! A constructive bounded library of sparse SAT assignments.
For each residue modulo k, write membership bits through the largest
present quotient and then a separator. If the unary price is ≤ k², the
entire description needs at most 3k ternary tokens, or 6k binary bits. -/
namespace Mobius.WitnessPacking
open Complexity.SAT
open Mobius.UnaryWitness (price)

private abbrev Token := Option Bool

private def height (k r : Nat) : List Nat → Nat
  | [] => 0
  | i::is => if i%k=r then max (i/k+1) (height k r is) else height k r is

private def quotientSum (k : Nat) : List Nat → Nat
  | [] => 0
  | i::is => i/k + quotientSum k is

private def bucketSum (k r : Nat) : List Nat → Nat
  | [] => 0
  | i::is => (if i%k=r then i/k else 0) + bucketSum k r is

private theorem height_mem (k : Nat) {is : List Nat} {j : Nat} (h : j∈is) :
    j/k < height k (j%k) is := by
  induction is with
  | nil => simp at h
  | cons i is ih =>
    rcases List.mem_cons.mp h with eq | mem
    · subst i
      simp [height]; omega
    · have lt := ih mem
      simp only [height]
      split <;> omega

private theorem height_bound (k r : Nat) (is : List Nat) : height k r is ≤ 1 + bucketSum k r is := by
  induction is with
  | nil => exact Nat.zero_le _
  | cons i is ih =>
    by_cases eq : i%k=r
    · simp only [height,bucketSum,ite_eq_left eq]
      apply Nat.max_le.mpr
      generalize i/k = v
      omega
    · simpa only [height,bucketSum,ite_eq_right eq,Nat.zero_add] using ih

private theorem quotient_price (k : Nat) (is : List Nat) : k*quotientSum k is ≤ price is := by
  induction is with
  | nil => simp [quotientSum,price]
  | cons i is ih =>
    have slot := Nat.mul_div_le i k
    change k*(i/k + quotientSum k is) ≤ i+1+price is
    rw [Nat.mul_add]; omega

private def rowsum (start : Nat) : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f start + rowsum (start+1) n f

private theorem rows_add (start n : Nat) (f g : Nat → Nat) :
    rowsum start n (fun r => f r + g r) = rowsum start n f + rowsum start n g := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [rowsum,ih]; omega

private theorem rows_const (start n v : Nat) : rowsum start n (fun _ => v) = n*v := by
  induction n generalizing start with
  | zero => simp [rowsum]
  | succ n ih => simp only [rowsum,ih,Nat.succ_mul]; omega

private theorem rows_mono (start n : Nat) (f g : Nat → Nat) (h : ∀ r, f r ≤ g r) :
    rowsum start n f ≤ rowsum start n g := by
  induction n generalizing start with
  | zero => exact Nat.le_refl 0
  | succ n ih => exact Nat.add_le_add (h start) (ih _)

private theorem rows_delta (start n t v : Nat) :
    rowsum start n (fun r => if t=r then v else 0) =
    if start≤t ∧ t<start+n then v else 0 := by
  induction n generalizing start with
  | zero => simp [rowsum]; omega
  | succ n ih =>
    rw [rowsum,ih]
    by_cases eq : t=start <;> split <;> split <;> split <;> omega

private theorem all_buckets (k start n : Nat) (is : List Nat) :
    rowsum start n (fun r => bucketSum k r is) ≤ quotientSum k is := by
  induction is with
  | nil => simp [bucketSum,quotientSum,rows_const]
  | cons i is ih =>
    simp only [bucketSum,quotientSum,rows_add,rows_delta]
    generalize i/k = v
    split <;> omega

private def bits (k r : Nat) (is : List Nat) := (List.range (height k r is)).map
  (fun q => is.contains (r+k*q))

private theorem bit_read (k j : Nat) (is : List Nat) :
    (bits k (j%k) is).getD (j/k) false = is.contains j := by
  by_cases inside : j/k < height k (j%k) is
  · simp only [bits,List.getD,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some,
        Nat.mod_add_div]
  · have absent : j ∉ is := fun h => inside (height_mem k h)
    have none : ((bits k (j%k) is)[j/k]?) = none := List.getElem?_eq_none
      (by simp only [bits,List.length_map,List.length_range]; omega)
    simp [List.getD,none,absent]

/-- Separate buckets by none; data bits are some false / some true. -/
private def body (k start : Nat) : Nat → List Nat → List Token
  | 0, _ => []
  | n+1, is => (bits k start is).map some ++ (none :: body k (start+1) n is)

private theorem body_length (k start n : Nat) (is : List Nat) :
    (body k start n is).length = rowsum start n (fun r => height k r is+1) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [body,List.length_append,List.length_map,List.length_cons,ih,bits,List.length_range,rowsum]
    omega

private theorem budget {k N : Nat} (positive : 0 < k) (size : N ≤ k*k) (is : List Nat)
    (bounded : price is ≤ N) : (body k 0 k is).length ≤ 3*k := by
  have q := quotient_price k is
  have sum_le : quotientSum k is ≤ k := by
    by_cases le : quotientSum k is ≤ k
    · exact le
    · have lt := Nat.mul_lt_mul_of_pos_left (show k<quotientSum k is by omega) positive
      omega
  rw [body_length]
  have each (r : Nat) : height k r is+1 ≤ 2+bucketSum k r is := by
    have := height_bound k r is
    omega
  have bound := rows_mono 0 k _ _ each
  have upper : rowsum 0 k (fun r => 2+bucketSum k r is) =
      k*2 + rowsum 0 k (fun r => bucketSum k r is) := by
    rw [rows_add, rows_const]
  rw [upper] at bound
  have bins := all_buckets k 0 k is
  omega

private def lookup : List Token → Nat → Nat → Bool
  | [], _, _ => false
  | none :: _, 0, _ => false
  | none :: ts, r+1, q => lookup ts r q
  | some b :: _, 0, 0 => b
  | some _ :: ts, 0, q+1 => lookup ts 0 q
  | some _ :: ts, r+1, q => lookup ts (r+1) q

private theorem read_here (bs : List Bool) (tail : List Token) (q : Nat) :
    lookup (bs.map some ++ (none::tail)) 0 q = bs.getD q false := by
  induction bs generalizing q with
  | nil => cases q <;> rfl
  | cons b bs ih => cases q <;> simp [lookup,ih]

private theorem read_later (bs : List Bool) (tail : List Token) (r q : Nat) :
    lookup (bs.map some ++ (none::tail)) (r+1) q = lookup tail r q := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [lookup,ih]

private theorem read_body (k start n : Nat) (is : List Nat) (tail : List Token)
    (r q : Nat) (inRange : r<n) :
    lookup (body k start n is ++ tail) r q = (bits k (start+r) is).getD q false := by
  induction n generalizing start r with
  | zero => omega
  | succ n ih =>
    simp only [body,List.append_assoc,List.cons_append]
    cases r with
    | zero => exact read_here ..
    | succ r =>
      rw [read_later]
      simpa only [Nat.succ_add, Nat.add_succ] using ih (start+1) r (by omega)

private def decode (k : Nat) (ts : List Token) : Assignment :=
  fun i => lookup ts (i%k) (i/k)

private theorem decode_body (k : Nat) (positive : 0<k) (is : List Nat) (tail : List Token) :
    decode k (body k 0 k is ++ tail) = fun j => is.contains j := by
  funext j
  unfold decode
  rw [read_body k 0 k is tail (j%k) (j/k) (Nat.mod_lt j positive),Nat.zero_add,bit_read]

/-- Enumeration of all fixed-size ternary words. No order or distinctness
    convention on the original witness list is required by the encoder. -/
private def words : Nat → List (List Token)
  | 0 => [[]]
  | n+1 => (words n).flatMap fun w => [none::w,some false::w,some true::w]

private theorem words_len (n : Nat) : (words n).length = 3^n := by
  have triples (ws : List (List Token)) :
      (ws.flatMap fun w => [none::w,some false::w,some true::w]).length = ws.length*3 := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,
        ih,Nat.succ_mul]; omega
  induction n with
  | zero => rfl
  | succ n ih => rw [words,triples,ih,Nat.pow_succ]

private theorem words_complete (ts : List Token) : ts ∈ words ts.length := by
  induction ts with
  | nil => simp [words]
  | cons t ts ih =>
    apply List.mem_flatMap.mpr
    refine ⟨ts,ih,?_⟩
    cases t with
    | none => simp
    | some b => cases b <;> simp

/-- Actual finite library, decoded uniformly from a length-3k ternary word. -/
def library (k : Nat) : Fin (3^(3*k)) → Assignment := fun idx =>
  decode k ((words (3*k))[idx.val]'(by rw [words_len]; exact idx.isLt))

theorem library_covers {N k : Nat} (positive : 0<k) (size : N≤k*k) :
    WitnessCut.Covers N (library k) := by
  intro is _ cheap
  let payload := body k 0 k is
  let pad : List Token := List.replicate (3*k-payload.length) none
  let word := payload ++ pad
  have bound := budget positive size is cheap
  change payload.length ≤ 3*k at bound
  have len : word.length = 3*k := by simp [word,pad]; omega
  have mem : word ∈ words (3*k) := len ▸ words_complete word
  have ok := List.idxOf_lt_length_of_mem mem
  let index : Fin (3^(3*k)) := ⟨(words (3*k)).idxOf word, by rw [← words_len]; exact ok⟩
  refine ⟨index,?_⟩
  unfold library
  rw [show ((words (3*k))[index.val]) = word from List.getElem_idxOf ok]
  exact decode_body k positive is pad

theorem ternary_le_binary (k : Nat) : 3^(3*k) ≤ 2^(6*k) := by
  calc
    3^(3*k) ≤ 4^(3*k) := Nat.pow_le_pow_left (by decide : 3≤4) _
    _ = (2^2)^(3*k) := rfl
    _ = 2^(6*k) := by rw [← Nat.pow_mul]; congr 1; omega

/-- For every physical cut, every finite positive fooling family of words
    of length at most N obeys this bound. Mixed words may be malformed. -/
theorem fixed_cut_bound {N m k : Nat} (positive : 0<k) (size : N≤k*k)
    (ws : Fin m → Word) (cut : Nat) (len : ∀ i, (ws i).length ≤ N)
    (yes : ∀ i, ThreeSAT (ws i))
    (separate : ∀ i j, ThreeSAT ((ws i).take cut ++ (ws j).drop cut) →
      ThreeSAT ((ws j).take cut ++ (ws i).drop cut) → i=j) :
    m ≤ 2^(6*k) * (2 + (N+1) + 3*(N+1)^2 + 4*(N+1)^3) := by
  exact Nat.le_trans (WitnessCut.fixed_cut_bound (library k) (library_covers positive size) ws cut len yes separate)
    (Nat.mul_le_mul_right _ (ternary_le_binary k))

/-- The positive ceiling square root; at N=0 this convention gives one. -/
def radius (N : Nat) : Nat := (N-1).sqrt + 1

theorem radius_covers (N : Nat) : N ≤ radius N * radius N := by
  have h := Nat.lt_succ_sqrt (N-1)
  change N-1 < radius N * radius N at h
  omega

private theorem absorb_state (N k : Nat) (size : N ≤ k*k) :
    2 + (N+1) + 3*(N+1)^2 + 4*(N+1)^3 ≤ 2^(6*k+4) := by
  have np : N+1 ≤ 2^(2*k) := by
    calc
      N+1 ≤ k*k+1 := Nat.succ_le_succ size
      _ ≤ (k+1)^2 := by grind
      _ ≤ (2^k)^2 := Nat.pow_le_pow_left (show k+1 ≤ 2^k from Nat.lt_two_pow_self) _
      _ = 2^(2*k) := by rw [← Nat.pow_mul,Nat.mul_comm k 2]
  have h1 : (N+1)^1 ≤ (N+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (N+1)^2 ≤ (N+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  simp only [Nat.pow_one] at h1
  calc
    _ ≤ 16*(N+1)^3 := by omega
    _ ≤ 16*(2^(2*k))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left np 3)
    _ = 2^(6*k+4) := by
      rw [← Nat.pow_mul,show 2*k*3 = 6*k by omega,Nat.pow_add,Nat.mul_comm (2^(6*k)) (2^4)]

/-- A pure exponential in the square root, with no polynomial factor and
    no independent choice of k required. -/
theorem sqrt_bound {N m : Nat} (ws : Fin m → Word) (cut : Nat)
    (len : ∀ i, (ws i).length ≤ N) (yes : ∀ i, ThreeSAT (ws i))
    (separate : ∀ i j, ThreeSAT ((ws i).take cut ++ (ws j).drop cut) →
       ThreeSAT ((ws j).take cut ++ (ws i).drop cut) → i=j) :
    m ≤ 2^(12*radius N+4) := by
  let k := radius N
  have pos : 0<k := Nat.zero_lt_succ _
  have size : N≤k*k := radius_covers N
  calc
    m ≤ 2^(6*k) * (2+(N+1)+3*(N+1)^2+4*(N+1)^3) := fixed_cut_bound pos size ws cut len yes separate
    _ ≤ 2^(6*k)*2^(6*k+4) := Nat.mul_le_mul_left _ (absorb_state N k size)
    _ = _ := by rw [← Nat.pow_add]; congr 1; change 6*k+(6*k+4)=12*k+4; omega

end Mobius.WitnessPacking
