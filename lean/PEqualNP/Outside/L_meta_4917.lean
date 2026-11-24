import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_4917 :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (14 : ℕ) ∧
        ∀ (x2 : Fin (42 : ℕ) → Bool),
          x1.wires (List.ofFn x2) =
            have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) =>
              x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));
            (List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++
              List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ) := by
  let combine (a b : ℕ) : Gate := ⟨.or, [a,b]⟩
  -- The first seven gates form pairs. The next seven extend them to triples.
  let C : Circuit := ⟨[
    combine 26 38, combine 29 41, combine 32 23, combine 35 26,
    combine 38 29, combine 41 32, combine 23 35,
    combine 42 41, combine 43 23, combine 44 26, combine 45 29,
    combine 46 32, combine 47 35, combine 48 38], 55⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C, combine]
  · intro x
    simp [C, combine, Circuit.wires, GateOp.eval, List.ofFn_succ, List.getD_eq_getElem?_getD,
      Fin.ofNat, List.foldl_cons, Bool.or_assoc]
