import Mobius.RigidityData

namespace Mobius.Rigidity
open Mobius.SignObstruction (B Cell Rectangle translate)

private theorem transport_pair (g h : Chart) (s p : Cell) (r : Rectangle) (turn : Bool) :
    translate p (mapRect g.act (translate s (flip (mapRect h.act r) turn))) =
      translate (p.1 ^^^ g.act s.1,p.2 ^^^ g.act s.2)
        (flip (mapRect (g.comp h).act r) turn) := by
  obtain ⟨x,y,d⟩ := r
  cases turn <;> simp [translate, mapRect, flip, Chart.comp, g.linear, BitVec.xor_assoc]

/-- Every two directed squares of distinct directions occur together in a
single affine copy of the tagged parity certificate, up to opposite anchors. -/
theorem pair_in_chart (x y d x' y' e : B) (hd : d ≠ 0) (he : e ≠ 0) (hne : d ≠ e) :
    ∃ (g : Chart) (s : Cell) (r q : Rectangle) (a b : Bool),
      r ∈ Mobius.TwoPhases.certificate ∧ q ∈ Mobius.TwoPhases.certificate ∧ r ≠ q ∧
      flip (translate s (mapRect g.act r)) a = (x,y,d) ∧
      flip (translate s (mapRect g.act q)) b = (x',y',e) := by
  obtain ⟨g,h1,h2⟩ := directions_chart d e hd he hne
  obtain ⟨h,s,r,q,a,b,hr,hq,first,second⟩ :=
    standard_pair (g.inv (x ^^^ x')) (g.inv (y ^^^ y'))
  let p : Cell := (x,y)
  let t : Cell := (x ^^^ g.act s.1, y ^^^ g.act s.2)
  have ar : flip (translate t (mapRect (g.comp h).act r)) a = (x,y,d) := by
    have k := congrArg (fun z => translate p (mapRect g.act z)) first
    rw [transport_pair, flip_translate] at k
    apply k.trans
    change (x ^^^ g.act 0, y ^^^ g.act 0, g.act 1) = (x,y,d)
    rw [g.zero, h1]
    simp
  have aq : flip (translate t (mapRect (g.comp h).act q)) b = (x',y',e) := by
    have k := congrArg (fun z => translate p (mapRect g.act z)) second
    rw [transport_pair, flip_translate] at k
    apply k.trans
    change (x ^^^ g.act (g.inv (x ^^^ x')), y ^^^ g.act (g.inv (y ^^^ y')), g.act 2) = (x',y',e)
    rw [g.right, g.right, h2, ← BitVec.xor_assoc, ← BitVec.xor_assoc]
    simp
  refine ⟨g.comp h,t,r,q,a,b,hr,hq,?_,ar,aq⟩
  rintro rfl
  have ha := congrArg (fun z : Rectangle => z.2.2) ar
  have hb := congrArg (fun z : Rectangle => z.2.2) aq
  cases a <;> cases b <;> simp [flip,translate,mapRect] at ha hb <;> exact hne (ha.symm.trans hb)

end Mobius.Rigidity
