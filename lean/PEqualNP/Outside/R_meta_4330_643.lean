import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The size-at-most-17 case is proved inside R_meta_2371_2.
-- The split into three initial signals follows PR 9573.
-- Each input to the initial OR must be read again, by distinct sensitivity witnesses.
theorem PEqualNP.Outside.R_meta_4330_643
    (small :
      let F := fun (x : Fin 10 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      ∀ (C : Circuit) (s : Bool), FanInTwo C → C.size ≤ 17 →
        (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) != s) = F x) → ∃ (E : Circuit) (b : Bool), FanInTwo E ∧ E.size ≤ 15 ∧
        ∀ x : Fin 10 → Bool, x 9 = false → (E.eval (List.ofFn x) != b) = F x)
    (normal :
      let F := fun (x : Fin 10 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      let reads (D : Circuit) (v : Fin 10) := (D.gates.filter fun g => g.inputs.contains v.val).length
      let seed (j : Fin 3) (x : Fin 10 → Bool) := if j = 0 then !(x 0) else x 0 || x (Fin.ofNat 10 j.val)
      let fit (C : Circuit) (s : Bool) := ∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) != s) = F x
      ∀ (C : Circuit) (s : Bool), FanInTwo C → C.size = 18 → fit C s →
        (∃ (D : Circuit) (b : Bool), FanInTwo D ∧
          ((D.size ≤ 17 ∧ fit D b) ∨
            (D.size ≤ 15 ∧ ∀ x : Fin 10 → Bool, x 9 = false → (D.eval (List.ofFn x) != b) = F x))) ∨
        (∃ (j : Fin 3) (D : Circuit) (b : Bool), FanInTwo D ∧ D.size = 17 ∧
          (∀ p q : Fin 10, p ≠ q → (⟨.and,[p.val,q.val]⟩ : Gate) ∉ D.gates) ∧
          (∀ v : Fin 10, reads D v ≤ if v = 0 ∨ (j ≠ 0 ∧ v = Fin.ofNat 10 j.val) then 1 else 2) ∧
          ∀ x : Fin 10 → Bool, (D.eval (List.ofFn x ++ [seed j x]) != b) = F x))
    (closeNot :
      let F := fun (x : Fin 10 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      let reads (D : Circuit) (v : Fin 10) := (D.gates.filter fun g => g.inputs.contains v.val).length
      ∀ (D : Circuit) (b : Bool), FanInTwo D → D.size = 17 → (∀ p q : Fin 10, p ≠ q → (⟨.and,[p.val,q.val]⟩ : Gate) ∉ D.gates) →
        (∀ v : Fin 10, reads D v ≤ if v = 0 then 1 else 2) →
        (∀ x : Fin 10 → Bool, (D.eval (List.ofFn x ++ [!(x 0)]) != b) = F x) → ∃ (E : Circuit) (b : Bool), FanInTwo E ∧ E.size ≤ 15 ∧
        ∀ x : Fin 10 → Bool, x 9 = false → (E.eval (List.ofFn x) != b) = F x)
    (closeOr :
      let F := fun (x : Fin 10 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      let reads (D : Circuit) (v : Fin 10) := (D.gates.filter fun g => g.inputs.contains v.val).length
      ∀ (v : Fin 10) (D : Circuit) (b : Bool), v = 1 ∨ v = 2 → FanInTwo D → D.size = 17 → (∀ p q : Fin 10, p ≠ q → (⟨.and,[p.val,q.val]⟩ : Gate) ∉ D.gates) →
        (∀ u : Fin 10, reads D u ≤ 2) → reads D 0 = 1 → reads D v = 1 →
        (∀ x : Fin 10 → Bool, (D.eval (List.ofFn x ++ [x 0 || x v]) != b) = F x) → ∃ (E : Circuit) (b : Bool), FanInTwo E ∧ E.size ≤ 15 ∧
        ∀ x : Fin 10 → Bool, x 9 = false → (E.eval (List.ofFn x) != b) = F x) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size = (17 : ℕ) →         have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => (x3.wires ({ gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x4 Bool.false;         (∀ (x10 : Fin (10 : ℕ) → Bool), (if x5 = Bool.true then !x9 x10 else x9 x10) = x1 x10) →           ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : ℕ) (x13 : Bool),             PEqualNP.MetaComplexity.FanInTwo x11 ∧               x11.size ≤ (15 : ℕ) ∧                 have x14 : (Fin (10 : ℕ) → Bool) → Bool := fun (x14 : Fin (10 : ℕ) → Bool) => (x11.wires (List.ofFn x14)).getD x12 Bool.false;                 ∀ (x15 : Fin (10 : ℕ) → Bool), x15 (9 : Fin (10 : ℕ)) = Bool.false → (if x13 = Bool.true then !x14 x15 else x14 x15) = x1 x15 := by
  have readFree (D : Circuit) (pin : ℕ) (xs ys : List Bool)
      (len : xs.length = ys.length)
      (initial : ∀ j ≠ pin, xs.getD j false = ys.getD j false)
      (misses : ∀ g ∈ D.gates, pin ∉ g.inputs) (output : D.output ≠ pin) :
      D.eval xs = D.eval ys := by
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    have run (gs : List Gate) (a b : List Bool) (len : a.length = b.length)
        (initial : ∀ j ≠ pin, a.getD j false = b.getD j false)
        (misses : ∀ g ∈ gs, pin ∉ g.inputs) :
        ∀ j ≠ pin, (gs.foldl step a).getD j false = (gs.foldl step b).getD j false := by
      induction gs generalizing a b with
      | nil => exact initial
      | cons g gs ih =>
        have values : (g.inputs.map fun j => a.getD j false) = (g.inputs.map fun j => b.getD j false) := by
          apply List.map_congr_left
          intro j hj
          exact initial j (fun h => misses g (by simp) (h ▸ hj))
        simp only [List.foldl_cons]
        apply ih (step a g) (step b g) (by simp [step, len])
        · intro j hj
          by_cases h : j < a.length
          · simp only [step, List.getD_append _ _ _ _ h,
              List.getD_append _ _ _ _ (show j < b.length by omega)]
            exact initial j hj
          · simp only [step, List.getD_append_right _ _ _ _ (show a.length ≤ j by omega),
              List.getD_append_right _ _ _ _ (show b.length ≤ j by omega), values, len]
        · exact fun g hg => misses g (List.mem_cons_of_mem _ hg)
    exact run D.gates xs ys len initial misses D.output output

  have inputPrefix (D : Circuit) (xs : List Bool) (j : ℕ) (hj : j < xs.length) :
      (D.wires xs).getD j false = xs.getD j false := by
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    change (D.gates.foldl step xs).getD j false = _
    induction D.gates generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step xs g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj

  have needsRead (D : Circuit) (a b : Fin 10) (polarity : Bool)
      (F : (Fin 10 → Bool) → Bool)
      (correct : ∀ x, (D.eval (List.ofFn x ++ [x a || x b]) != polarity) = F x)
      (zero : F (fun _ => false) = false) (single : F (fun i => decide (i = a)) = false)
      (sensitive : ∃ x y : Fin 10 → Bool,
        x b = true ∧ y b = true ∧ (∀ j ≠ a, x j = y j) ∧ F x ≠ F y) :
      ∃ g ∈ D.gates, a.val ∈ g.inputs := by
    have input (x : Fin 10 → Bool) (i : Fin 10) :
        (List.ofFn x ++ [x a || x b]).getD i false = x i := by
      rw [List.getD_append _ _ _ _ (by simpa using i.isLt),
        List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [i.isLt]
    have output : D.output ≠ a.val := by
      intro h
      have eval (x : Fin 10 → Bool) : D.eval (List.ofFn x ++ [x a || x b]) = x a := by
        change (D.wires _).getD D.output false = _
        rw [h, inputPrefix _ _ _ (by simp; have := a.isLt; omega), input]
      have h0 := correct (fun _ => false)
      have h1 := correct (fun i => decide (i = a))
      rw [eval, zero] at h0
      rw [eval, single] at h1
      cases polarity <;> simp at h0 h1
    by_contra missing
    push Not at missing
    obtain ⟨x, y, xb, yb, eq, ne⟩ := sensitive
    let row (z : Fin 10 → Bool) := List.ofFn z ++ [z a || z b]
    have initial : ∀ j ≠ a.val, (row x).getD j false = (row y).getD j false := by
      intro j hj
      by_cases old : j < 10
      · exact (input x ⟨j, old⟩).trans ((eq ⟨j, old⟩ (fun h => hj (congrArg Fin.val h))).trans
          (input y ⟨j, old⟩).symm)
      · have sameTail : row x = List.ofFn x ++ [true] ∧ row y = List.ofFn y ++ [true] := by
          simp [row, xb, yb]
        rw [sameTail.1, sameTail.2,
          List.getD_append_right _ _ _ _ (show (List.ofFn x).length ≤ j by simp; omega),
          List.getD_append_right _ _ _ _ (show (List.ofFn y).length ≤ j by simp; omega)]
        simp
    have same := readFree D a.val (row x) (row y) (by simp [row]) initial missing output
    apply ne
    rw [← correct x, ← correct y]
    change (D.eval (row x) != polarity) = (D.eval (row y) != polarity)
    rw [same]

  let F := fun (x : Fin 10 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  let reads (D : Circuit) (v : Fin 10) := (D.gates.filter fun g => g.inputs.contains v.val).length
  have phase (z b : Bool) : (z != b) = (if b = true then !z else z) := by
    cases b <;> cases z <;> rfl
  have graph (x : Fin 10 → Bool) : F x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    simp [F, List.any, Fin.ofNat, Bool.or_assoc]
  dsimp only
  intro g D out s hg legal size fits
  let C : Circuit := ⟨g :: D.gates, out⟩
  have cap : C.size = 18 := by
    change (g :: D.gates).length = 18
    change D.gates.length = 17 at size
    simp [size]
  have fan : FanInTwo C := by
    intro a h
    rcases List.mem_cons.mp h with rfl | h
    · exact hg _ List.mem_cons_self
    · exact legal a h
  have fit (x : Fin 10 → Bool) : (C.eval (List.ofFn x) != s) = F x := by
    rw [phase, graph]
    exact fits x
  have solved : ∃ (E : Circuit) (b : Bool), FanInTwo E ∧ E.size ≤ 15 ∧
        ∀ x : Fin 10 → Bool, x 9 = false → (E.eval (List.ofFn x) != b) = F x := by
    obtain ⟨S,b,fanS,smaller⟩ | ⟨j,S,b,fanS,sizeS,shape,count,fitS⟩ := normal C s fan cap fit
    · rcases smaller with ⟨sizeS,fitS⟩ | ⟨sizeS,fitS⟩
      · exact small S b fanS sizeS fitS
      · exact ⟨S,b,fanS,sizeS,fitS⟩
    · by_cases hzero : j = 0
      · subst j
        exact closeNot S b fanS sizeS shape (by simpa using count) (by simpa using fitS)
      · let v : Fin 10 := Fin.ofNat 10 j.val
        have choices : v = 1 ∨ v = 2 := by
          have range := j.isLt
          have notZero : j.val ≠ 0 := fun h => hzero (Fin.ext h)
          have jcases : j.val = 1 ∨ j.val = 2 := by omega
          rcases jcases with h | h
          · exact Or.inl (Fin.ext (by simp [v, h]))
          · exact Or.inr (Fin.ext (by simp [v, h]))
        have seeded (x : Fin 10 → Bool) : (S.eval (List.ofFn x ++ [x 0 || x v]) != b) = F x := by
          have hx := fitS x
          simp only [if_neg hzero] at hx
          exact hx
        have reverse (x : Fin 10 → Bool) : (S.eval (List.ofFn x ++ [x v || x 0]) != b) = F x := by
          rw [Bool.or_comm]
          exact seeded x
        have sensitivity0 : ∃ x y : Fin 10 → Bool,
            x v = true ∧ y v = true ∧ (∀ i ≠ 0, x i = y i) ∧ F x ≠ F y := by
          rcases choices with h | h
          · rw [h]
            refine ⟨fun i => decide (i = 1 ∨ i = 4), fun i => decide (i = 0 ∨ i = 1 ∨ i = 4),
              by decide, by decide, ?_, by decide⟩
            intro i hi
            simp [hi]
          · rw [h]
            refine ⟨fun i => decide (i = 2 ∨ i = 4), fun i => decide (i = 0 ∨ i = 2 ∨ i = 4),
              by decide, by decide, ?_, by decide⟩
            intro i hi
            simp [hi]
        have sensitivityV : ∃ x y : Fin 10 → Bool,
            x 0 = true ∧ y 0 = true ∧ (∀ i ≠ v, x i = y i) ∧ F x ≠ F y := by
          rcases choices with h | h
          · rw [h]
            refine ⟨fun i => decide (i = 0 ∨ i = 2), fun i => decide (i = 1 ∨ i = 0 ∨ i = 2),
              by decide, by decide, ?_, by decide⟩
            intro i hi
            simp [hi]
          · rw [h]
            refine ⟨fun i => decide (i = 0 ∨ i = 3), fun i => decide (i = 2 ∨ i = 0 ∨ i = 3),
              by decide, by decide, ?_, by decide⟩
            intro i hi
            simp [hi]
        have singles : ∀ i : Fin 10, F (fun k => decide (k = i)) = false := by dsimp [F]; decide
        have pos (u : Fin 10) (h : ∃ g ∈ S.gates, u.val ∈ g.inputs) : 0 < reads S u := by
          exact List.length_filter_pos_iff.mpr (by simpa using h)
        have positive0 := pos 0 (needsRead S 0 v b F seeded (by decide) (singles 0) sensitivity0)
        have positiveV := pos v (needsRead S v 0 b F reverse (by decide) (singles v) sensitivityV)
        have bounded (u : Fin 10) : reads S u ≤ if u = 0 ∨ (j ≠ 0 ∧ u = v) then 1 else 2 := count u
        have limit0 : reads S 0 ≤ 1 := by
          have h := bounded 0
          rwa [if_pos (Or.inl rfl)] at h
        have limitV : reads S v ≤ 1 := by
          have h := bounded v
          rwa [if_pos (Or.inr ⟨hzero, rfl⟩)] at h
        have limits (u : Fin 10) : reads S u ≤ 2 := by
          have hu := bounded u
          split at hu <;> omega
        have count0 : reads S 0 = 1 := by omega
        have countV : reads S v = 1 := by omega
        exact closeOr v S b choices fanS sizeS shape limits count0 countV seeded
  obtain ⟨E,b,fanE,capE,evalE⟩ := solved
  refine ⟨E, E.output, b, fanE, capE, fun x hx => ?_⟩
  have eq := evalE x hx
  rw [phase, graph] at eq
  exact eq
