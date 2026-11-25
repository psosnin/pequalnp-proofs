import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11159_aux

open PEqualNP.CircuitLowerBounds

-- The gate-list induction adapts the project proof in L_meta_2462.lean.
private def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

private theorem scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

private theorem scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

private theorem scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

private theorem scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

private def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

end PEqualNP.Outside.L_meta_11159_aux

open PEqualNP.Outside.L_meta_11159_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_11159 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < x1 + x3 ∧ x7 < x1 + x3) →     ∀ (x4 x5 : Fin x1 → Bool) (x6 : ℕ → ℕ),       (∀ (x7 : Fin x1), x4 x7 = Bool.true → x6 ↑x7 = (0 : ℕ)) →         (∀ (x8 : Fin x1), x5 x8 = Bool.true → x6 ↑x8 ≤ (1 : ℕ)) →           (∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) (x11 x12 : ℕ), x2.gates[x9]? = Option.some x10 → x10.inputs = [x11, x12] → (x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x1 + x9) ≤ x6 x11 + x6 x12) ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 (x1 + x9) ≤ Min.min (x6 x11) (x6 x12))) →             ∃ (x10 : ℕ → Bool),               (∀ (x11 : Fin x1), x10 ↑x11 = x5 x11) ∧                 (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate) (x13 x14 : ℕ),                     x2.gates[x11]? = Option.some x12 →                       x12.inputs = [x13, x14] →                         have x17 : List Bool := x2.wires (List.ofFn x4);                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x10 (x1 + x11) = (x17.getD x13 Bool.false && x10 x14 || x10 x13 && x17.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10 (x1 + x11) = (x10 x13 || x10 x14))) ∧                   ∀ (x11 : ℕ), x10 x11 = Bool.true → x6 x11 ≤ (1 : ℕ) := by
  classical
  intro N C shape base seed d baseCost seedCost gateCost
  let actual := C.wires (List.ofFn base)
  let diffStep (v : List Bool) (g : Gate) :=
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if g.op = .and then
      (actual.getD a false && v.getD b false) || (v.getD a false && actual.getD b false)
    else v.getD a false || v.getD b false
  let traces := scan diffStep C.gates (List.ofFn seed)
  let v (k : ℕ) := traces.getD k false
  have atInput (i : Fin N) : v i.val = seed i := by
    change (scan _ _ _).getD _ false = _
    rw [scan_prefix _ _ _ _ _ (by simpa using i.isLt)]
    simp [List.getD_eq_getElem?_getD]
  have recD (j : ℕ) (g : Gate) (a b : ℕ) (hg : C.gates[j]? = some g) (hab : g.inputs=[a,b]) :
      (g.op = .and → v (N+j) = ((actual.getD a false && v b) || (v a && actual.getD b false))) ∧
      (g.op = .or → v (N+j) = (v a || v b)) := by
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
    obtain ⟨_, c, e, hc, _, hca, heb⟩ := shape j _ (List.getElem?_eq_getElem hj)
    rw [hab] at hc
    simp only [List.cons.injEq,and_true] at hc
    obtain ⟨rfl,rfl⟩ := hc
    have h := scan_gate diffStep C.gates (List.ofFn seed) false j hj (by
      intro u u' same
      simp only [diffStep,hab,List.getD_cons_zero,List.getD_cons_succ]
      rw [same a (by simpa using hca),same b (by simpa using heb)])
    change _ ∧ _
    simp only [List.length_ofFn] at h
    constructor <;> intro op
    all_goals simpa [v,traces,diffStep,hab,op] using h
  refine ⟨v,atInput,recD,?_⟩
  have invariant (k : ℕ) :
      (actual.getD k false = true → d k = 0) ∧ (v k = true → d k ≤ 1) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      by_cases raw : k < N
      · let i : Fin N := ⟨k,raw⟩
        have read : actual.getD k false = base i := by
          change (scan boolStep C.gates (List.ofFn base)).getD k false = _
          rw [scan_prefix _ _ _ _ _ (by simpa using raw)]
          simp [i,List.getD_eq_getElem?_getD,raw]
        exact ⟨fun b => baseCost i (read ▸ b),fun b => seedCost i (atInput i ▸ b)⟩
      · let j := k-N
        have kj : k=N+j := by dsimp [j]; omega
        by_cases good : j < C.gates.length
        · let g := C.gates[j]
          have found : C.gates[j]? = some g := List.getElem?_eq_getElem good
          obtain ⟨op,a,b,pins,_,ha,hb⟩ := shape _ _ found
          have left := ih a (by omega)
          have right := ih b (by omega)
          have hd := recD j g a b found pins
          have cost := gateCost j g a b found pins
          have he := scan_gate boolStep C.gates (List.ofFn base) false j good (by
            intro u u' same
            change g.op.eval (g.inputs.map _) = g.op.eval (g.inputs.map _)
            rw [pins]
            simp only [List.map_cons,List.map_nil,same a (by simpa using ha),same b (by simpa using hb)])
          simp only [List.length_ofFn] at he
          change actual.getD (N+j) false = g.op.eval (g.inputs.map fun i => actual.getD i false) at he
          rw [pins] at he
          rcases op with op | op
          · have heq : actual.getD (N+j) false = (actual.getD a false && actual.getD b false) := by
              simpa [op,GateOp.eval] using he
            have rel := cost.1 op
            rw [kj,heq,hd.1 op]
            simp only [Bool.and_eq_true,Bool.or_eq_true]
            constructor
            · rintro ⟨l,r⟩; have := left.1 l; have := right.1 r; omega
            · rintro (⟨l,r⟩ | ⟨l,r⟩)
              · have := left.1 l; have := right.2 r; omega
              · have := left.2 l; have := right.1 r; omega
          · have heq : actual.getD (N+j) false = (actual.getD a false || actual.getD b false) := by
              simpa [op,GateOp.eval] using he
            have rel := cost.2 op
            rw [kj,heq,hd.2 op]
            simp only [Bool.or_eq_true]
            constructor
            · rintro (h | h)
              · have := left.1 h; omega
              · have := right.1 h; omega
            · rintro (h | h)
              · have := left.2 h; omega
              · have := right.2 h; omega
        · have alen : actual.length = N+C.gates.length := by
            change (scan boolStep C.gates (List.ofFn base)).length = _
            simp [scan_length]
          have tlen : traces.length = N+C.gates.length := by simp [traces,scan_length]
          have a := List.getD_eq_default actual false (n:=k) (by omega)
          have t := List.getD_eq_default traces false (n:=k) (by omega)
          change (actual.getD k false = true → _) ∧ (traces.getD k false = true → _)
          rw [a,t]
          simp
  exact fun k => (invariant k).2
