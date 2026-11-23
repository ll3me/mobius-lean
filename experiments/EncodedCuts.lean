import Mobius.BoundedBridge

/-! Check the inputs of the proposed machine crossing-sequence experiment
using the public 3-SAT encoder. This checks the layout and splicing of input
words; it makes no assertion about a deciding machine or its time. -/

open Mobius.Bounded (block)
open Mobius.BoundedBridge (toWord)

private def inputWord (m u v : Nat) :=
  toWord (block (BitVec.ofNat (2*m) u) ++ block (BitVec.ofNat (2*m) v))

private def checkCase (m : Nat) : IO Unit := do
  let n := 2*m
  let expected := 20*n*n + 92*n + 1
  -- The left formula block ends after the clause-count header and one body.
  let right := 8*n + 1 + (10*n*n + 42*n)
  let width := 22*m*m + 42*m
  let left := right-width
  let base := ((inputWord m 0 0).drop left).take width
  for u in List.range (2^m) do
    let a := inputWord m u u
    for v in List.range (2^m) do
      let b := inputWord m v v
      let mixed := inputWord m u v
      unless mixed.length == expected && (mixed.drop left).take width == base do
        throw (IO.userError "fixed interval check failed")
      for cut in [left, left+width/2, right] do
        unless (a.take cut ++ b.drop cut) == mixed do
          throw (IO.userError "input splice failed")
  IO.println s!"m={m}: {(2^m)^2} ordered input pairs; encoded length {expected}, fixed interval {width}"

#eval [1,2,3].forM checkCase
