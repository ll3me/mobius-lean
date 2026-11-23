import Mobius.FullCaps
import Mobius.AxisCompiler

/-! An explicit cap per named core coordinate. The private coordinate of
cap j, axis a>0, is v+3j+(a-1). The cost theorem uses the actual full boards
in these coordinates. -/
namespace Mobius.CapAtlas
open Mobius.AxisGlue (Atlas Axis bits Matching World)
open Mobius.FullCaps (ci vi)
open Mobius.SignObstruction (B)

abbrev coreIdx (n : Nat) (i : Fin k) := ci n i
abbrev capIdx (k : Nat) (j : Fin n) := vi k j
abbrev coreCoord (n : Nat) (x : Fin v) := x.castAdd (3*n)

def capLoc (name : Fin n → Fin v) (j : Fin n) (a : Axis) : Fin (v+3*n) :=
  if a=0 then coreCoord n (name j)
  else ⟨v+3*j.val+(a.val-1),by omega⟩

private theorem core_inj {x y : Fin v} (h : coreCoord n x=coreCoord n y) : x=y :=
  Fin.ext (congrArg (fun z : Fin (v+3*n) => z.val) h)

theorem core_cap {name : Fin n → Fin v} {x : Fin v} {j : Fin n} {a : Axis} :
    coreCoord n x=capLoc name j a ↔ x=name j ∧ a=0 := by
  by_cases h : a=0
  · subst a
    simp only [capLoc,ite_true]
    exact ⟨fun eq => ⟨core_inj eq,True.intro⟩,fun e => congrArg (coreCoord n) e.1⟩
  · constructor
    · intro eq
      have hv := congrArg Fin.val eq
      simp only [capLoc,ite_eq_right h,coreCoord,Fin.val_castAdd] at hv
      have bound := x.isLt
      omega
    · intro c; exact False.elim (h c.2)

theorem cap_pairs (name : Fin n → Fin v) (inj : ∀ i j, name i=name j → i=j)
    {i j : Fin n} {a b : Axis} (eq : capLoc name i a=capLoc name j b) : i=j ∧ a=b := by
  by_cases az : a=0
  · subst a
    have c := core_cap.mp (show coreCoord n (name i)=capLoc name j b from eq)
    exact ⟨inj _ _ c.1,c.2.symm⟩
  by_cases bz : b=0
  · subst b
    have c := core_cap.mp (show coreCoord n (name j)=capLoc name i a from eq.symm)
    exact False.elim (az c.2)
  have hv := congrArg Fin.val eq
  simp only [capLoc,ite_eq_right az,ite_eq_right bz] at hv
  have aa : a.val≠0 := fun h => az (Fin.ext h)
  have bb : b.val≠0 := fun h => bz (Fin.ext h)
  have al := a.isLt
  have bl := b.isLt
  exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩

def location (T : Atlas k v) (name : Fin n → Fin v) : Fin (k+n) → Axis → Fin (v+3*n) :=
  Fin.addCases (fun i a => coreCoord n (T.loc i a)) (capLoc name)

@[simp] theorem location_core (T : Atlas k v) (name : Fin n → Fin v) (i : Fin k) (a : Axis) :
    location T name (ci n i) a = coreCoord n (T.loc i a) := by simp [location,ci]
@[simp] theorem location_cap (T : Atlas k v) (name : Fin n → Fin v) (j : Fin n) (a : Axis) :
    location T name (vi k j) a = capLoc name j a := by simp [location,vi]

def attach (T : Atlas k v) (name : Fin n → Fin v) (inj : ∀ i j, name i=name j → i=j) :
    Atlas (k+n) (v+3*n) where
  loc := location T name
  inj i := by
    induction i using Fin.addCases with
    | left i => intro a b eq; exact T.inj i a b (core_inj (by simpa only [location_core] using eq))
    | right j => intro a b eq; exact (cap_pairs name inj (by simpa only [location_cap] using eq)).2
  linear i j := by
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        intro ne a b c d ab cd
        apply T.linear i j (fun e => ne (congrArg (ci n) e)) a b c d
        · exact core_inj (by simpa only [location_core] using ab)
        · exact core_inj (by simpa only [location_core] using cd)
      | right j =>
        intro _ a b c d ab cd
        have h := core_cap.mp (show coreCoord n (T.loc i a)=capLoc name j b from by simpa only [location_core,location_cap] using ab)
        have h' := core_cap.mp (show coreCoord n (T.loc i c)=capLoc name j d from by simpa only [location_core,location_cap] using cd)
        exact T.inj i a c (h.1.trans h'.1.symm)
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        intro _ a b c d ab cd
        have h := core_cap.mp (show coreCoord n (T.loc j b)=capLoc name i a from by simpa only [location_core,location_cap] using ab.symm)
        have h' := core_cap.mp (show coreCoord n (T.loc j d)=capLoc name i c from by simpa only [location_core,location_cap] using cd.symm)
        exact h.2.trans h'.2.symm
      | right j =>
        intro ne a b c d ab _
        have h := cap_pairs name inj (i:=i) (j:=j) (a:=a) (b:=b) (by simpa only [location_cap] using ab)
        exact False.elim (ne (congrArg (vi k) h.1))

@[simp] theorem core_loc (T : Atlas k v) (name : Fin n → Fin v) (inj) (i : Fin k) (a : Axis) :
    (attach T name inj).loc (ci n i) a=coreCoord n (T.loc i a) := location_core ..
@[simp] theorem cap_loc (T : Atlas k v) (name : Fin n → Fin v) (inj) (j : Fin n) (a : Axis) :
    (attach T name inj).loc (vi k j) a=capLoc name j a := location_cap ..
@[simp] theorem cap_port (T : Atlas k v) (name : Fin n → Fin v) (inj) (j : Fin n) :
    (attach T name inj).loc (vi k j) 0=coreCoord n (name j) := by rw [cap_loc]; rfl

/-- The named coordinates coincide exactly with the designated axes where
they occur on the core. A named unused variable simply gets an isolated cap. -/
def Names (T : Atlas k v) (p : Fin k → B) (name : Fin n → Fin v) :=
  ∀ i a, bits (p i) a=true ↔ ∃ j, T.loc i a=name j

theorem wiring_attach (T : Atlas k v) (name : Fin n → Fin v) (inj) (p : Fin k → B)
    (shared : AxisNetwork.AllSharedArePorts T p) (names : Names T p name) :
    FullCaps.Wiring (attach T name inj) p where
  coreShared i j ne a b eq := shared i j ne a b (core_inj (by simpa only [FullCaps.cores,core_loc] using eq))
  incident i j a b eq := by
    rw [core_loc,cap_loc] at eq
    have c := core_cap.mp eq
    exact ⟨(names i a).mpr ⟨j,c.1⟩,c.2⟩
  cover i a yes := by
    obtain ⟨j,h⟩ := (names i a).mp yes
    exact ⟨j,by rw [core_loc,cap_port,h]⟩
  separate i j a b eq := (cap_pairs name inj (i:=i) (j:=j) (a:=a) (b:=b) (by simpa only [cap_loc] using eq)).1

theorem feasible_cores (T : Atlas k v) (name : Fin n → Fin v) (inj) (p : Fin k → B) :
    AxisNetwork.Feasible (FullCaps.cores (attach T name inj)) p ↔ AxisNetwork.Feasible T p := by
  constructor
  · rintro ⟨pick,agree,allow⟩
    refine ⟨pick,fun i j a b same => agree i j a b ?_,allow⟩
    simp only [FullCaps.cores,core_loc,same]
  · rintro ⟨pick,agree,allow⟩
    refine ⟨pick,fun i j a b same => agree i j a b (core_inj (n:=n) ?_),allow⟩
    simpa only [FullCaps.cores,core_loc] using same


/-- Six port names private to each source row: its three occurrence
coordinates (0,1,2) and its three relay coordinates (4,5,6). -/
def rowOffset (s : Fin 6) : Fin 19 := ⟨if s.val<3 then s.val else s.val+1,by split <;> omega⟩

private theorem offset_inj : ∀ a b : Fin 6, rowOffset a=rowOffset b → a=b := by decide
private def rowName (i : Fin m) (s : Fin 6) : Fin (6*m) := ⟨6*i.val+s.val,by omega⟩
private def owner (q : Fin (6*m)) : Fin m := ⟨q.val/6,by omega⟩
private def slot (q : Fin (6*m)) : Fin 6 := ⟨q.val%6,by omega⟩
private theorem owner_name (i : Fin m) (s : Fin 6) : owner (rowName i s)=i := by
  apply Fin.ext; change (6*i.val+s.val)/6=i.val; omega
private theorem slot_name (i : Fin m) (s : Fin 6) : slot (rowName i s)=s := by
  apply Fin.ext; change (6*i.val+s.val)%6=s.val; omega

def compiledName (m v : Nat) : Fin (v+6*m) → Fin (v+19*m) :=
  Fin.addCases (AxisCompiler.original m)
    (fun q => AxisCompiler.localVertex v (owner q) (rowOffset (slot q)))

private theorem name_original (a : Fin v) :
    compiledName m v (a.castAdd (6*m))=AxisCompiler.original m a := Fin.addCases_left ..
private theorem name_local (a : Fin (6*m)) :
    compiledName m v (a.natAdd v) = AxisCompiler.localVertex v (owner a) (rowOffset (slot a)) :=
  Fin.addCases_right ..

private theorem local_equal {i j : Fin m} {a b : Fin 19}
    (eq : AxisCompiler.localVertex v i a=AxisCompiler.localVertex v j b) : i=j ∧ a=b := by
  have h := congrArg Fin.val eq
  change v+19*i.val+a.val=v+19*j.val+b.val at h
  have a19 := a.isLt; have b19 := b.isLt
  exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩

private theorem original_not_local (a : Fin v) (i : Fin m) (b : Fin 19) :
    AxisCompiler.original m a ≠ AxisCompiler.localVertex v i b := by
  intro h
  have val := congrArg Fin.val h
  change a.val=v+19*i.val+b.val at val
  omega

theorem compiledName_inj (m v : Nat) (i j : Fin (v+6*m)) :
    compiledName m v i=compiledName m v j → i=j := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      intro eq; rw [name_original,name_original] at eq
      have eqv := congrArg (fun a : Fin (v+19*m) => a.val) eq
      exact congrArg (Fin.castAdd (6*m)) (Fin.ext eqv)
    | right j =>
      intro eq; rw [name_original,name_local] at eq
      exact False.elim (original_not_local _ _ _ eq)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      intro eq; rw [name_local,name_original] at eq
      exact False.elim (original_not_local _ _ _ eq.symm)
    | right j =>
      intro eq
      rw [name_local,name_local] at eq
      obtain ⟨rows,offsets⟩ := local_equal eq
      have slots := offset_inj _ _ offsets
      have hr := congrArg Fin.val rows
      have hs := congrArg Fin.val slots
      change i.val/6=j.val/6 at hr
      change i.val%6=j.val%6 at hs
      exact congrArg (Fin.natAdd v) (Fin.ext (by omega))

private theorem template_port : ∀ (s : AxisCompiler.Tag) (a : Axis),
    bits (AxisCompiler.mask s) a=true ↔ AxisCompiler.shape s a=0 ∨
      ∃ b, AxisCompiler.privateIndex (AxisCompiler.shape s a)=rowOffset b := by decide

theorem compiled_names (f : AxisCompiler.Source m v) :
    Names (AxisCompiler.atlas f) (AxisCompiler.ports m) (compiledName m v) := by
  intro i a
  let s := AxisCompiler.tag i
  let r := AxisCompiler.row i
  change bits (AxisCompiler.mask s) a=true ↔ ∃ j, AxisCompiler.locate f r s a=compiledName m v j
  rw [template_port]
  by_cases original : AxisCompiler.shape s a=0
  · constructor
    · intro _
      refine ⟨(f r (AxisCompiler.sourceSlot s)).castAdd (6*m),?_⟩
      rw [name_original]
      simp [AxisCompiler.locate,original]
    · intro _; exact Or.inl original
  · constructor
    · intro h
      obtain ⟨b,code⟩ := h.resolve_left original
      refine ⟨(rowName r b).natAdd v,?_⟩
      rw [name_local,owner_name,slot_name]
      simp [AxisCompiler.locate,original,code]
    · rintro ⟨j,eq⟩
      right
      induction j using Fin.addCases with
      | left j =>
        rw [name_original] at eq
        simp only [AxisCompiler.locate,ite_eq_right original] at eq
        exact False.elim (original_not_local _ _ _ eq.symm)
      | right j =>
        rw [name_local] at eq
        simp only [AxisCompiler.locate,ite_eq_right original] at eq
        exact ⟨slot j,(local_equal eq).2⟩

def compiled (f : AxisCompiler.Source m v) :
    Atlas (7*m+(v+6*m)) ((v+19*m)+3*(v+6*m)) :=
  attach (AxisCompiler.atlas f) (compiledName m v) (compiledName_inj m v)

theorem compiled_wiring (f : AxisCompiler.Source m v) :
    FullCaps.Wiring (compiled f) (AxisCompiler.ports m) :=
  wiring_attach _ _ _ _ (AxisCompiler.all_shared f) (compiled_names f)

/-- A concrete reduction from every three-occurrence exact-one source.
There are 7m cores, v+6m caps, and no precondition on the source variables;
in particular the same variable may occur more than once in a source row. -/
theorem compiled_threshold (gap : AxisPortCost.Gap282) (f : AxisCompiler.Source m v) :
    (∃ r c : World ((v+19*m)+3*(v+6*m)),
      FullCaps.cost (compiled f) (AxisCompiler.ports m) r c ≤ (7*m)*126+(v+6*m)*128) ↔
      AxisCompiler.Satisfiable f := by
  rw [FullCaps.threshold_iff gap _ _ (compiled_wiring f) (AxisCompiler.admissible m)]
  exact ((feasible_cores _ _ _ _).trans (AxisNetwork.feasible_iff_boolean _ _)).trans
    (AxisCompiler.boolean_iff f)


/-- The literal union cost traverses all complete boards and deduplicates
actual ambient addresses. It has no argument carrying the port masks. -/
theorem compiled_union_iff (gap : AxisPortCost.Gap282) (f : AxisCompiler.Source m v) :
    (∃ r c : World ((v+19*m)+3*(v+6*m)),
      FullCaps.unionCost (compiled f) r c ≤ (7*m)*126+(v+6*m)*128) ↔
      AxisCompiler.Satisfiable f := by
  simpa only [FullCaps.union_cost_eq _ _ (compiled_wiring f)] using compiled_threshold gap f

end Mobius.CapAtlas
