/-! Integer Walsh moments of a weighted list of sign patterns, after
    grouping identical patterns. No positivity of the masses is assumed. -/
namespace Mobius.SignReadout

def Cube : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Cube n

def constantMode : (n : Nat) → Cube n → Bool
  | 0, _ => true
  | n+1, (b,s) => !b && constantMode n s

def moment : (n : Nat) → (Cube n → Int) → Cube n → Int
  | 0, mass, _ => mass ()
  | n+1, mass, (b,s) =>
    let left := moment n (fun x => mass (false,x)) s
    let right := moment n (fun x => mass (true,x)) s
    if b then left-right else left+right

def doubleScale : Nat → Int → Int
  | 0, a => a
  | n+1, a => doubleScale n (a+a)

theorem uniform_mass (n : Nat) (mass : Cube n → Int) (scale total : Int)
    (cancel : ∀ s, scale * moment n mass s = if constantMode n s then total else 0) :
    ∀ x, doubleScale n scale * mass x = total := by
  induction n generalizing scale with
  | zero =>
    intro x
    cases x
    exact cancel ()
  | succ n ih =>
    rintro ⟨b,x⟩
    apply ih (fun y => mass (b,y)) (scale+scale)
    intro s
    have plus := cancel (false,s)
    have minus := cancel (true,s)
    simp [moment, constantMode, Int.mul_add] at plus
    simp [moment, constantMode, Int.mul_sub] at minus
    rw [Int.add_mul]
    cases b <;> omega

end Mobius.SignReadout
