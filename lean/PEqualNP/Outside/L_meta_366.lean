import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_366 : ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] → ∀ O : Finset (Fin 5) → Finset (Fin 5 × Fin 5), (∀ J : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 5 × Fin 5 → ZMod 2 | ∃ J : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  intro E hE O hO
  subst hE
  have hvc : PEqualNP.MetaComplexity.SingleLevel.vc ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)) ≤ 3 := by
    unfold PEqualNP.MetaComplexity.SingleLevel.vc
    exact Nat.sInf_le ⟨({0, 2, 3} : Finset (Fin 5)), by decide, by decide⟩
  refine le_trans hvc ?_
  set S : Set (Fin 5 × Fin 5 → ZMod 2) :=
    {w : Fin 5 × Fin 5 → ZMod 2 |
      ∃ J : Finset (Fin 5),
        (∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)),
          ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧
        w = fun d => if d ∈ O J then 1 else 0}
  set W := vectorSpan (ZMod 2) S
  let w : Finset (Fin 5) → (Fin 5 × Fin 5 → ZMod 2) := fun J d => if d ∈ O J then 1 else 0
  have h_in_S :
      ∀ J : Finset (Fin 5),
        (∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)),
          ¬ (f.1 ∈ J ∧ f.2 ∈ J)) →
        w J ∈ S := fun J hJ => ⟨J, hJ, rfl⟩
  have h_zero :
      ∀ J : Finset (Fin 5),
        (∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)),
          ¬ (f.1 ∈ J ∧ f.2 ∈ J)) →
        ∀ d : Fin 5 × Fin 5, d.2 ∈ J → w J d = 0 := by
    intro J hJ d hd
    have hnot : d ∉ O J := fun hmem => (hO J hJ).2.2 d hmem hd
    simp [w, hnot]
  have h_one :
      ∀ J : Finset (Fin 5),
        (∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)),
          ¬ (f.1 ∈ J ∧ f.2 ∈ J)) →
        ∀ e ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)),
          e.1 ∈ J → w J e = 1 := by
    intro J hJ e he he1
    have hrev : (e.2, e.1) ∉ O J := fun hmem => (hO J hJ).2.2 (e.2, e.1) hmem he1
    have hmem : e ∈ O J := ((hO J hJ).2.1 e he).1.resolve_right hrev
    simp [w, hmem]
  let J1 : Finset (Fin 5) := {0, 2}
  let J2 : Finset (Fin 5) := {0, 3}
  let J3 : Finset (Fin 5) := {1, 3}
  let J4 : Finset (Fin 5) := {1, 4}
  let J5 : Finset (Fin 5) := {2, 4}
  have hJ1 : ∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)), ¬ (f.1 ∈ J1 ∧ f.2 ∈ J1) := by decide
  have hJ2 : ∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)), ¬ (f.1 ∈ J2 ∧ f.2 ∈ J2) := by decide
  have hJ3 : ∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)), ¬ (f.1 ∈ J3 ∧ f.2 ∈ J3) := by decide
  have hJ4 : ∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)), ¬ (f.1 ∈ J4 ∧ f.2 ∈ J4) := by decide
  have hJ5 : ∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] : List (Fin 5 × Fin 5)), ¬ (f.1 ∈ J5 ∧ f.2 ∈ J5) := by decide
  let v1 := w J2 - w J1
  let v2 := w J3 - w J1
  let v3 := w J4 - w J1
  let v4 := w J5 - w J1
  have hv1 : v1 ∈ W := vsub_mem_vectorSpan (ZMod 2) (h_in_S J2 hJ2) (h_in_S J1 hJ1)
  have hv2 : v2 ∈ W := vsub_mem_vectorSpan (ZMod 2) (h_in_S J3 hJ3) (h_in_S J1 hJ1)
  have hv3 : v3 ∈ W := vsub_mem_vectorSpan (ZMod 2) (h_in_S J4 hJ4) (h_in_S J1 hJ1)
  have hv4 : v4 ∈ W := vsub_mem_vectorSpan (ZMod 2) (h_in_S J5 hJ5) (h_in_S J1 hJ1)
  have hfinrank :
      ∀ u0 u1 u2 : Fin 5 × Fin 5 → ZMod 2,
        u0 ∈ W → u1 ∈ W → u2 ∈ W →
        (∀ c0 c1 c2 : ZMod 2, c0 • u0 + c1 • u1 + c2 • u2 = 0 → c0 = 0 ∧ c1 = 0 ∧ c2 = 0) →
        3 ≤ Module.finrank (ZMod 2) W := by
    intro u0 u1 u2 hu0 hu1 hu2 hind
    let b : Fin 3 → W := ![⟨u0, hu0⟩, ⟨u1, hu1⟩, ⟨u2, hu2⟩]
    have hli : LinearIndependent (ZMod 2) b := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hg' := congrArg Subtype.val hg
      simp only [Fin.sum_univ_three, b, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero] at hg'
      have ⟨hc0, hc1, hc2⟩ := hind (g 0) (g 1) (g 2) (by simpa [add_assoc] using hg')
      fin_cases i <;> simp [hc0, hc1, hc2]
    simpa using hli.fintype_card_le_finrank
  have hw1_01 : w J1 (0, 1) = 1 := h_one J1 hJ1 (0, 1) (by decide) (by decide)
  have hw1_12 : w J1 (1, 2) = 0 := h_zero J1 hJ1 (1, 2) (by decide)
  have hw1_23 : w J1 (2, 3) = 1 := h_one J1 hJ1 (2, 3) (by decide) (by decide)
  have hw1_04 : w J1 (0, 4) = 1 := h_one J1 hJ1 (0, 4) (by decide) (by decide)
  have hw2_01 : w J2 (0, 1) = 1 := h_one J2 hJ2 (0, 1) (by decide) (by decide)
  have hw2_23 : w J2 (2, 3) = 0 := h_zero J2 hJ2 (2, 3) (by decide)
  have hw2_34 : w J2 (3, 4) = 1 := h_one J2 hJ2 (3, 4) (by decide) (by decide)
  have hw2_04 : w J2 (0, 4) = 1 := h_one J2 hJ2 (0, 4) (by decide) (by decide)
  have hw3_01 : w J3 (0, 1) = 0 := h_zero J3 hJ3 (0, 1) (by decide)
  have hw3_23 : w J3 (2, 3) = 0 := h_zero J3 hJ3 (2, 3) (by decide)
  have hw3_34 : w J3 (3, 4) = 1 := h_one J3 hJ3 (3, 4) (by decide) (by decide)
  have hw4_01 : w J4 (0, 1) = 0 := h_zero J4 hJ4 (0, 1) (by decide)
  have hw4_12 : w J4 (1, 2) = 1 := h_one J4 hJ4 (1, 2) (by decide) (by decide)
  have hw4_34 : w J4 (3, 4) = 0 := h_zero J4 hJ4 (3, 4) (by decide)
  have hw4_04 : w J4 (0, 4) = 0 := h_zero J4 hJ4 (0, 4) (by decide)
  have hw5_12 : w J5 (1, 2) = 0 := h_zero J5 hJ5 (1, 2) (by decide)
  have hw5_23 : w J5 (2, 3) = 1 := h_one J5 hJ5 (2, 3) (by decide) (by decide)
  have hw5_04 : w J5 (0, 4) = 0 := h_zero J5 hJ5 (0, 4) (by decide)
  by_cases hd : (2, 3) ∈ O J4
  · have hw4_23 : w J4 (2, 3) = 1 := by simp [w, hd]
    refine hfinrank v1 v3 v4 hv1 hv3 hv4 ?_
    intro c0 c1 c2 h
    have e23 := congrFun h (2, 3)
    simp only [v1, v3, v4, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
      hw1_23, hw2_23, hw4_23, hw5_23] at e23
    have hc0 : c0 = 0 :=
      (by decide : ∀ x y z : ZMod 2, x * (0 - 1) + y * (1 - 1) + z * (1 - 1) = 0 → x = 0) c0 c1 c2 e23
    have e12 := congrFun h (1, 2)
    simp only [hc0, zero_smul, zero_add, v3, v4, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      Pi.zero_apply, smul_eq_mul, hw1_12, hw4_12, hw5_12] at e12
    have hc1 : c1 = 0 :=
      (by decide : ∀ y z : ZMod 2, y * (1 - 0) + z * (0 - 0) = 0 → y = 0) c1 c2 e12
    have e04 := congrFun h (0, 4)
    simp only [hc0, hc1, zero_smul, zero_add, v4, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply,
      smul_eq_mul, hw1_04, hw5_04] at e04
    have hc2 : c2 = 0 :=
      (by decide : ∀ z : ZMod 2, z * (0 - 1) = 0 → z = 0) c2 e04
    exact ⟨hc0, hc1, hc2⟩
  · have hw4_23 : w J4 (2, 3) = 0 := by simp [w, hd]
    refine hfinrank v1 v2 v3 hv1 hv2 hv3 ?_
    intro c0 c1 c2 h
    have e01 := congrFun h (0, 1)
    simp only [v1, v2, v3, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
      hw1_01, hw2_01, hw3_01, hw4_01] at e01
    have e23 := congrFun h (2, 3)
    simp only [v1, v2, v3, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
      hw1_23, hw2_23, hw3_23, hw4_23] at e23
    have e34 := congrFun h (3, 4)
    by_cases ha : (3, 4) ∈ O J1
    · have hw1_34 : w J1 (3, 4) = 1 := by simp [w, ha]
      simp only [v1, v2, v3, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
        hw1_34, hw2_34, hw3_34, hw4_34] at e34
      exact (by decide : ∀ x y z : ZMod 2,
        x * (1 - 1) + y * (0 - 1) + z * (0 - 1) = 0 →
        x * (0 - 1) + y * (0 - 1) + z * (0 - 1) = 0 →
        x * (1 - 1) + y * (1 - 1) + z * (0 - 1) = 0 →
        x = 0 ∧ y = 0 ∧ z = 0) c0 c1 c2 e01 e23 e34
    · have hw1_34 : w J1 (3, 4) = 0 := by simp [w, ha]
      simp only [v1, v2, v3, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
        hw1_34, hw2_34, hw3_34, hw4_34] at e34
      exact (by decide : ∀ x y z : ZMod 2,
        x * (1 - 1) + y * (0 - 1) + z * (0 - 1) = 0 →
        x * (0 - 1) + y * (0 - 1) + z * (0 - 1) = 0 →
        x * (1 - 0) + y * (1 - 0) + z * (0 - 0) = 0 →
        x = 0 ∧ y = 0 ∧ z = 0) c0 c1 c2 e01 e23 e34
