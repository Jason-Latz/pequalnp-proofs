import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fixing the two complementary pins makes any gate that reads both a constant.
-- The remaining search needs separate readers and only the boundary rows of the two cofactors.
-- The ordinary lower bound is L-meta-2331. The two-reader restriction follows
-- from L-meta-2305 and L-meta-2307. Boundary-row tests also appear in PR 9289.
theorem PEqualNP.Outside.R_meta_4645_643
    (shape :
      let F := fun (x : Fin 9 → Bool) =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ C : Circuit, FanInTwo C → (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 0)) →
        circuitFun 9 C = F → C.size ≤ 15 → ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 14 ∧
        (∀ g ∈ D.gates, g.op = .and ∨ g.op = .or) ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!(x 0)]) = F x)
    (readers :
      let F := fun (x : Fin 9 → Bool) =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → (∀ g ∈ D.gates, g.op = .and ∨ g.op = .or) →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!(x 0)]) = F x) →
        (D.gates.filter (fun g => g.inputs.contains 0 || g.inputs.contains 9)).length ≤ 2)
    (ordinary :
      let F := fun (x : Fin 9 → Bool) =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ C : Circuit, FanInTwo C → circuitFun 9 C = F → 15 ≤ C.size)
    (search :
      let tests : List ℕ := [1027, 1542, 1548, 1037, 1041, 1560, 1057, 554, 562, 1602, 69, 616, 628, 1668, 1157, 650, 1696, 712, 201, 720, 261, 1800, 1289, 788, 1824, 1856, 1345, 385, 914]
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
        (∀ g ∈ D.gates, g.op = .and ∨ g.op = .or) →
        (D.gates.filter (fun g => g.inputs.contains 0 || g.inputs.contains 9)).length ≤ 2 →
        (∀ g ∈ D.gates, 0 ∈ g.inputs → 9 ∉ g.inputs) →
        (∃ g ∈ D.gates, 0 ∈ g.inputs) → (∃ g ∈ D.gates, 9 ∈ g.inputs) →
        ∃ r ∈ tests, D.eval (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 9]) ≠ r.testBit 10) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = !x3 (0 : Fin (9 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have gateCount (C : Circuit) : C.size = C.gates.length := rfl
  have suffixComparison (skip : ℕ) (D : Circuit) (u v : List Bool)
      (hlen : u.length = v.length)
      (hinput : ∀ j ≠ skip, u.getD j false = true → v.getD j false = true)
      (hop : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or)
      (hskip : ∀ g ∈ D.gates, skip ∉ g.inputs) (hout : D.output ≠ skip) :
      D.eval u = true → D.eval v = true := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    have stepOrder (g : Gate) (a b : List Bool) (hl : a.length = b.length)
        (hi : ∀ j ≠ skip, a.getD j false = true → b.getD j false = true)
        (ho : g.op = .and ∨ g.op = .or) (hs : skip ∉ g.inputs) :
        ∀ j ≠ skip, (step a g).getD j false = true → (step b g).getD j false = true := by
      have evalOrder : g.op.eval (g.inputs.map fun j => a.getD j false) = true →
          g.op.eval (g.inputs.map fun j => b.getD j false) = true := by
        intro hab
        rcases ho with h | h
        · simp only [h, evalAnd, List.all_eq_true, List.mem_map, id_eq] at hab ⊢
          rintro _ ⟨j, hj, rfl⟩
          exact hi j (fun e => hs (e ▸ hj)) (hab _ ⟨j, hj, rfl⟩)
        · simp only [h, evalOr, List.any_eq_true, List.mem_map, id_eq] at hab ⊢
          obtain ⟨_, ⟨j, hj, rfl⟩, hjtrue⟩ := hab
          exact ⟨_, ⟨j, hj, rfl⟩, hi j (fun e => hs (e ▸ hj)) hjtrue⟩
      intro j hj hv
      by_cases h : j < a.length
      · simp only [step, List.getD_append _ _ _ _ h] at hv
        simp only [step, List.getD_append _ _ _ _ (show j < b.length by omega)]
        exact hi j hj hv
      · simp only [step, List.getD_append_right _ _ _ _ (show a.length ≤ j by omega)] at hv
        simp only [step, List.getD_append_right _ _ _ _ (show b.length ≤ j by omega), ← hl]
        cases hd : j - a.length with
        | zero => simpa using evalOrder (by simpa [hd] using hv)
        | succ => simp [hd] at hv
    have foldOrder (gs : List Gate) (a b : List Bool) (hl : a.length = b.length)
        (hi : ∀ j ≠ skip, a.getD j false = true → b.getD j false = true)
        (ho : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (hs : ∀ g ∈ gs, skip ∉ g.inputs) :
        ∀ j ≠ skip, (gs.foldl step a).getD j false = true →
          (gs.foldl step b).getD j false = true := by
      induction gs generalizing a b with
      | nil => exact hi
      | cons g gs ih =>
        apply ih (step a g) (step b g) (by simp [step, hl])
        · exact stepOrder g a b hl hi (ho g (by simp)) (hs g (by simp))
        · exact fun g hg => ho g (by simp [hg])
        · exact fun g hg => hs g (by simp [hg])
    exact foldOrder D.gates u v hlen hinput hop hskip D.output hout

  have suffixPrefix (D : Circuit) (xs : List Bool) (j : ℕ) (hj : j < xs.length) :
      (D.wires xs).getD j false = xs.getD j false := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    change (D.gates.foldl step xs).getD j false = _
    induction D.gates generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step xs g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj

  have bothPolarityReaders (D : Circuit)
      (hop : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or)
      (F : (Fin 9 → Bool) → Bool)
      (hcorrect : ∀ x, D.eval (List.ofFn x ++ [!(x 0)]) = F x)
      (hclamp : ¬ ∀ x, D.eval (List.ofFn x ++ [false]) = F x)
      (hzero : F (fun _ => false) = false)
      (hone : F (fun i => decide (i = 0)) = false)
      (hneighbour : F (fun i => decide (i = 1)) = false)
      (hedge : F (fun i => decide (i = 0 ∨ i = 1)) = true) :
      (∃ g ∈ D.gates, 0 ∈ g.inputs) ∧ (∃ g ∈ D.gates, 9 ∈ g.inputs) := by
    have hout0 : D.output ≠ 0 := by
      intro hout
      have h := hcorrect (fun i => decide (i = 0))
      change (D.wires _).getD D.output false = _ at h
      rw [hone, hout, suffixPrefix _ _ _ (by simp)] at h
      exact Bool.false_ne_true h.symm
    have hout9 : D.output ≠ 9 := by
      intro hout
      have h := hcorrect (fun _ => false)
      change (D.wires _).getD D.output false = _ at h
      rw [hzero, hout, suffixPrefix _ _ _ (by simp)] at h
      exact Bool.false_ne_true h.symm
    constructor
    · by_contra h
      push Not at h
      let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
      let y : Fin 9 → Bool := fun i => decide (i = 1)
      have hinput : ∀ j ≠ 0, (List.ofFn x ++ [!(x 0)]).getD j false = true →
          (List.ofFn y ++ [!(y 0)]).getD j false = true := by
        intro j hj hv
        by_cases hs : j < 10
        · interval_cases j <;> first | contradiction | (simp [x, y, List.getD_eq_getElem?_getD] at hv ⊢)
        · have bound : (List.ofFn x ++ [!(x 0)]).length ≤ j := by simpa using Nat.le_of_not_lt hs
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none bound] at hv
          contradiction
      have order := suffixComparison 0 D _ _ (by simp) hinput hop h hout0
      rw [hcorrect, hcorrect] at order
      change F (fun i => decide (i = 0 ∨ i = 1)) = true → F (fun i => decide (i = 1)) = true at order
      rw [hedge, hneighbour] at order
      exact Bool.false_ne_true (order rfl)
    · by_contra h
      push Not at h
      apply hclamp
      intro x
      have equal : ∀ j ≠ 9, (List.ofFn x ++ [!(x 0)]).getD j false =
          (List.ofFn x ++ [false]).getD j false := by
        intro j hj
        by_cases hlt : j < 9
        · have hl : j < (List.ofFn x).length := by simpa using hlt
          rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ hl]
        · have hb : (List.ofFn x).length ≤ j := by simp; omega
          simp only [List.getD_append_right _ _ _ _ hb, List.length_ofFn]
          cases hd : j - 9 with
          | zero => omega
          | succ n => simp
      have forward := suffixComparison 9 D (List.ofFn x ++ [!(x 0)]) (List.ofFn x ++ [false])
        (by simp) (fun j hj hz => (equal j hj).symm ▸ hz) hop h hout9
      have backward := suffixComparison 9 D (List.ofFn x ++ [false]) (List.ofFn x ++ [!(x 0)])
        (by simp) (fun j hj hz => (equal j hj) ▸ hz) hop h hout9
      rw [hcorrect] at forward backward
      exact Bool.eq_iff_iff.mpr ⟨backward, forward⟩

  have clearPairedReaders (D : Circuit)
      (hfan : FanInTwo D) (hop : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or) :
      ∃ E : Circuit, E.size = D.size ∧ FanInTwo E ∧
        (∀ g ∈ E.gates, g.op = .and ∨ g.op = .or) ∧
        (∀ g ∈ E.gates, 0 ∈ g.inputs → 9 ∉ g.inputs) ∧
        (E.gates.filter (fun g => g.inputs.contains 0 || g.inputs.contains 9)).length ≤
          (D.gates.filter (fun g => g.inputs.contains 0 || g.inputs.contains 9)).length ∧
        (∀ x : Fin 9 → Bool, E.eval (List.ofFn x ++ [!(x 0)]) = D.eval (List.ofFn x ++ [!(x 0)])) := by
    let paired (g : Gate) := g.inputs.contains 0 && g.inputs.contains 9
    let reads (g : Gate) := g.inputs.contains 0 || g.inputs.contains 9
    let clean (g : Gate) : Gate :=
      if paired g then ⟨if g.op.eval [] then .or else .and, []⟩ else g
    let E : Circuit := ⟨D.gates.map clean, D.output⟩
    have readsClean (g : Gate) : reads (clean g) = (reads g && !paired g) := by
      cases h : paired g <;> simp [clean, h, reads]
    have mapCount (gs : List Gate) :
        ((gs.map clean).filter reads).length ≤ (gs.filter reads).length := by
      rw [List.filter_map, List.length_map]
      change (gs.filter (fun g => reads (clean g))).length ≤ _
      simp only [readsClean]
      simpa only [List.filter_filter, Bool.and_comm] using
        (List.length_filter_le (fun g => !paired g) (gs.filter reads))
    have twoPins (xs : List ℕ) (len : xs.length ≤ 2) (h0 : 0 ∈ xs) (h9 : 9 ∈ xs) :
        xs = [0,9] ∨ xs = [9,0] := by
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
      · simp at h0
      · simp only [List.mem_singleton] at h0 h9
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h9
        rcases h0 with h0 | h0 <;> rcases h9 with h9 | h9 <;> (first | omega | simp_all)
      · simp at len
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    have stepEq (g : Gate) (hg : g ∈ D.gates) (w : List Bool)
        (inv : w.getD 9 false = !(w.getD 0 false)) : step w (clean g) = step w g := by
      by_cases h : paired g = true
      · have pins : 0 ∈ g.inputs ∧ 9 ∈ g.inputs := by simpa [paired] using h
        obtain hp | hp := twoPins g.inputs (hfan g hg).2 pins.1 pins.2 <;>
          obtain ho | ho := hop g hg <;>
          simp only [step, clean, h, ite_true, hp, ho, evalAnd, evalOr, List.map_cons, List.map_nil,
            List.all_nil, List.any_nil, List.all_cons, List.any_cons, id_eq] <;>
          rw [inv] <;> cases w.getD 0 false <;> rfl
      · simp [step, clean, show paired g = false from Bool.eq_false_iff.mpr h]
    have foldEq (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ D.gates) (w : List Bool)
        (len : 9 < w.length) (inv : w.getD 9 false = !(w.getD 0 false)) :
        (gs.map clean).foldl step w = gs.foldl step w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [stepEq g (sub g (by simp)) w inv]
        apply ih (fun g hg => sub g (by simp [hg]))
        · simp only [step, List.length_append, List.length_singleton]
          omega
        · simpa only [step, List.getD_append _ _ _ _ len,
            List.getD_append _ _ _ _ (show 0 < w.length by omega)] using inv
    have ops (g : Gate) (hg : g ∈ D.gates) : (clean g).op = .and ∨ (clean g).op = .or := by
      simp only [clean]
      split
      · split <;> simp
      · exact hop g hg
    refine ⟨E, by simp [E, gateCount], ?_, ?_, ?_, mapCount D.gates, ?_⟩
    · intro g hg
      obtain ⟨g, member, rfl⟩ := List.mem_map.mp hg
      constructor
      · change (clean g).op = .and ∨ (clean g).op = .or ∨ (clean g).op = .not
        exact (ops g member).imp_right Or.inl
      · simp only [clean]
        split
        · simp
        · exact (hfan g member).2
    · intro g hg
      obtain ⟨g, member, rfl⟩ := List.mem_map.mp hg
      exact ops g member
    · intro g hg h0 h9
      obtain ⟨g, member, rfl⟩ := List.mem_map.mp hg
      by_cases h : paired g = true
      · simp [clean, h] at h0
      · have hfalse := Bool.eq_false_iff.mpr h
        simp only [clean, hfalse, Bool.false_eq_true, ite_false] at h0 h9
        exact h (by simp [paired, h0, h9])
    · intro x
      change ((D.gates.map clean).foldl step _).getD D.output false =
        (D.gates.foldl step _).getD D.output false
      rw [foldEq D.gates (fun _ h => h) _ (by simp)]
      have size : (List.ofFn x).length = 9 := by simp
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), size]
      simp

  have removeFalseInput (D : Circuit) (hfan : FanInTwo D) :
      ∃ C : Circuit, C.size = D.size ∧ FanInTwo C ∧
        ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = D.eval (List.ofFn x ++ [false]) := by
    let wire (j : ℕ) := if j < 9 then j else if j = 9 then 9 + D.size else j - 1
    let gate (g : Gate) : Gate := ⟨g.op, g.inputs.map wire⟩
    let C : Circuit := ⟨D.gates.map gate, wire D.output⟩
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    have absent (w : List Bool) (j : ℕ) (h : w.length ≤ j) : w.getD j false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
      rfl
    have foldMap (gs : List Gate) (large small : List Bool)
        (len : large.length = small.length + 1) (start : 9 ≤ small.length)
        (count : small.length + gs.length = 9 + D.size)
        (agree : ∀ j, large.getD j false = small.getD (wire j) false) :
        ∀ j, (gs.foldl step large).getD j false = ((gs.map gate).foldl step small).getD (wire j) false := by
      induction gs generalizing large small with
      | nil => exact agree
      | cons g gs ih =>
        have nextVal : (g.inputs.map fun j => large.getD j false) =
            ((gate g).inputs.map fun j => small.getD j false) := by
          simp only [gate, List.map_map, Function.comp_def, agree]
        have stepLen (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by simp [step]
        simp only [List.foldl_cons, List.map_cons]
        apply ih (step large g) (step small (gate g))
        · simp [stepLen, len]
        · simp only [stepLen]; omega
        · simp only [stepLen]; simp only [List.length_cons] at count; omega
        · intro j
          by_cases slot : j = 9
          · subst j
            have over : (step small (gate g)).length ≤ 9 + D.size := by
              simp only [stepLen, List.length_cons] at *
              omega
            rw [show wire 9 = 9 + D.size by simp [wire], absent _ _ over]
            rw [show (step large g).getD 9 false = large.getD 9 false from
              List.getD_append _ _ _ _ (by omega), agree, show wire 9 = 9 + D.size by simp [wire]]
            exact absent _ _ (by omega)
          by_cases old : j < large.length
          · have oldSmall : wire j < small.length := by
              by_cases input : j < 9
              · simpa [wire, input] using (show j < small.length by omega)
              · simp [wire, input, slot]; omega
            rw [show (step large g).getD j false = large.getD j false from List.getD_append _ _ _ _ old,
                show (step small (gate g)).getD (wire j) false = small.getD (wire j) false from
                  List.getD_append _ _ _ _ oldSmall]
            exact agree j
          · have index : wire j = j - 1 := by simp [wire, show ¬ j < 9 by omega, slot]
            rw [index]
            simp only [step, List.getD_append_right _ _ _ _ (show large.length ≤ j by omega),
              List.getD_append_right _ _ _ _ (show small.length ≤ j - 1 by omega), nextVal]
            rw [show j - large.length = j - 1 - small.length by omega]
    refine ⟨C, by simp [C, gateCount], ?_, ?_⟩
    · intro g hg
      obtain ⟨g, member, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g member).1, by simpa [gate] using (hfan g member).2⟩
    · intro x
      have first : ∀ j, (List.ofFn x ++ [false]).getD j false = (List.ofFn x).getD (wire j) false := by
        have len : (List.ofFn x).length = 9 := by simp
        intro j
        by_cases input : j < 9
        · rw [List.getD_append _ _ _ _ (by simpa using input)]
          simp [wire, input]
        · by_cases slot : j = 9
          · subst j
            rw [show wire 9 = 9 + D.size by simp [wire],
              List.getD_append_right _ _ _ _ (show (List.ofFn x).length ≤ 9 by omega), len]
            exact (absent (List.ofFn x) (9 + D.size) (by omega)).symm
          · rw [absent _ _ (by simp; omega), show wire j = j - 1 by simp [wire,input,slot], absent _ _ (by omega)]
      exact (foldMap D.gates _ _ (by simp) (by simp) (by simp [gateCount]) first D.output).symm

  let F := fun (x : Fin 9 → Bool) =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  intro C fan first output
  by_contra h
  have correct : circuitFun 9 C = F := by
    rw [output]
    funext x
    simp [F, List.any, Bool.or_assoc]
  obtain ⟨D, legalD, sizeD, opsD, correctD⟩ := shape C fan first correct (by omega)
  have countD := readers D legalD sizeD opsD correctD
  obtain ⟨E, sizeE, legalE, opsE, separate, fewer, same⟩ := clearPairedReaders D legalD opsD
  have small : E.size ≤ 14 := by omega
  have agrees (x : Fin 9 → Bool) : E.eval (List.ofFn x ++ [!(x 0)]) = F x :=
    (same x).trans (correctD x)
  have clamp : ¬ ∀ x : Fin 9 → Bool, E.eval (List.ofFn x ++ [false]) = F x := by
    intro eq
    obtain ⟨R, sizeR, legalR, sameR⟩ := removeFalseInput E legalE
    have targetR : circuitFun 9 R = F := funext fun x => (sameR x).trans (eq x)
    have large := ordinary R legalR targetR
    omega
  obtain ⟨pos, neg⟩ := bothPolarityReaders E opsE F agrees clamp
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨r, tested, differs⟩ := search E legalE small opsE (fewer.trans countD) separate pos neg
  let tests : List ℕ := [1027, 1542, 1548, 1037, 1041, 1560, 1057, 554, 562, 1602, 69, 616, 628, 1668, 1157, 650, 1696, 712, 201, 720, 261, 1800, 1289, 788, 1824, 1856, 1345, 385, 914]
  let x := fun i : Fin 9 => r.testBit i.val
  have labels : tests.all (fun n =>
      (n.testBit 9 == !(n.testBit 0)) &&
        (n.testBit 10 == F (fun i : Fin 9 => n.testBit i.val))) = true := by decide
  have row := List.all_eq_true.mp labels r tested
  have pins : r.testBit 9 = !(x 0) := eq_of_beq (Bool.and_eq_true_iff.mp row).1
  have value : r.testBit 10 = F x := eq_of_beq (Bool.and_eq_true_iff.mp row).2
  exact differs (by rw [pins, value]; exact agrees x)
