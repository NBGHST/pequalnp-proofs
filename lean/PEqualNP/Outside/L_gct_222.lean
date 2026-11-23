import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_222 : ∀ a b : Fin 4 → ℂ, (∑ j, b j = 0) → a 0 = 0 → (∑ i, a i = 0) → Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + (if i = 0 then b j else if j = 0 then a i else 0)) = 24 := by
  intro a b hb ha0 ha
  have hprod :
      ∀ σ : Equiv.Perm (Fin 4),
        (∏ i : Fin 4,
            (Matrix.of fun (i j : Fin 4) =>
              (1 : ℂ) + (if i = 0 then b j else if j = 0 then a i else 0)) (σ i) i) =
          (1 + a (σ 0)) * (1 + b (σ.symm 0)) := by
    intro σ
    by_cases h0 : σ 0 = 0
    · have hs0 : σ.symm 0 = 0 := σ.symm_apply_eq.mpr h0.symm
      have hp :
          (∏ i : Fin 4,
              (Matrix.of fun (i j : Fin 4) =>
                (1 : ℂ) + (if i = 0 then b j else if j = 0 then a i else 0)) (σ i) i) =
            1 + b 0 := by
        refine (Finset.prod_eq_single (0 : Fin 4) ?_ (fun h => absurd (Finset.mem_univ 0) h)).trans ?_
        · intro i _ hi
          have hsi : σ i ≠ 0 := fun h => hi (σ.injective (h.trans h0.symm))
          simp [Matrix.of_apply, hsi, hi]
        · simp [Matrix.of_apply, h0]
      rw [hp, h0, hs0, ha0]
      ring
    · have hs0 : σ.symm 0 ≠ 0 := fun h => h0 (by simpa [h] using σ.apply_symm_apply 0)
      have hp :
          (∏ i : Fin 4,
              (Matrix.of fun (i j : Fin 4) =>
                (1 : ℂ) + (if i = 0 then b j else if j = 0 then a i else 0)) (σ i) i) =
            ∏ i ∈ ({0, σ.symm 0} : Finset (Fin 4)),
              (Matrix.of fun (i j : Fin 4) =>
                (1 : ℂ) + (if i = 0 then b j else if j = 0 then a i else 0)) (σ i) i := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro i _ hi
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        have hsi : σ i ≠ 0 := fun h => hi.2 (by rw [← h, Equiv.symm_apply_apply])
        simp [Matrix.of_apply, hsi, hi.1]
      rw [hp, Finset.prod_pair hs0.symm]
      simp [Matrix.of_apply, h0]
  have hsum_apply :
      ∀ f : Fin 4 → ℂ, (∑ i : Fin 4, f i = 0) → (∑ σ : Equiv.Perm (Fin 4), f (σ 0)) = 0 := by
    intro f hf
    have hu : ∀ u : Fin 4, (∑ σ : Equiv.Perm (Fin 4), f (σ 0)) = ∑ σ : Equiv.Perm (Fin 4), f (σ u) := by
      intro u
      exact Fintype.sum_equiv (Equiv.mulRight (Equiv.swap (0 : Fin 4) u))
        (fun σ => f (σ 0)) (fun σ => f (σ u))
        (fun σ => by simp [Equiv.Perm.mul_apply])
    have h4 : (4 : ℂ) * ∑ σ : Equiv.Perm (Fin 4), f (σ 0) = 0 := by
      calc
        (4 : ℂ) * ∑ σ : Equiv.Perm (Fin 4), f (σ 0)
            = ∑ _u : Fin 4, ∑ σ : Equiv.Perm (Fin 4), f (σ 0) := by simp
        _ = ∑ u : Fin 4, ∑ σ : Equiv.Perm (Fin 4), f (σ u) := Finset.sum_congr rfl fun u _ => hu u
        _ = ∑ σ : Equiv.Perm (Fin 4), ∑ u : Fin 4, f (σ u) := Finset.sum_comm
        _ = ∑ _σ : Equiv.Perm (Fin 4), ∑ i : Fin 4, f i := by
              refine Finset.sum_congr rfl fun σ _ => ?_
              exact Fintype.sum_equiv σ (fun u => f (σ u)) f (fun _ => rfl)
        _ = 0 := by simp [hf]
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
  have hsum1 : (∑ _σ : Equiv.Perm (Fin 4), (1 : ℂ)) = 24 := by
    simp [Fintype.card_perm, Nat.factorial]
  have hsum2 : (∑ σ : Equiv.Perm (Fin 4), a (σ 0)) = 0 := hsum_apply a ha
  have hsum3 : (∑ σ : Equiv.Perm (Fin 4), b (σ.symm 0)) = 0 := by
    have hinv :
        (∑ σ : Equiv.Perm (Fin 4), b (σ.symm 0)) = ∑ σ : Equiv.Perm (Fin 4), b (σ 0) :=
      Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin 4)))
        (fun σ => b (σ.symm 0)) (fun σ => b (σ 0))
        (fun σ => by change b (σ.symm 0) = b (σ⁻¹ 0); rfl)
    rw [hinv]
    exact hsum_apply b hb
  have hsum4 : (∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)) = 0 := by
    let c : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
    have hc0 : c 0 = 0 := by decide
    have hc1 : c 1 = 2 := by decide
    have hc2 : c 2 = 3 := by decide
    have hc3 : c 3 = 1 := by decide
    have hmul_symm : ∀ σ : Equiv.Perm (Fin 4), (c * σ).symm 0 = σ.symm 0 := fun σ =>
      (c * σ).symm_apply_eq.mpr (by simp [Equiv.Perm.mul_apply, hc0])
    have hs1 :
        (∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)) =
          ∑ σ : Equiv.Perm (Fin 4), a (c (σ 0)) * b (σ.symm 0) :=
      (Fintype.sum_equiv (Equiv.mulLeft c)
        (fun σ => a (c (σ 0)) * b (σ.symm 0))
        (fun σ => a (σ 0) * b (σ.symm 0))
        (fun σ => by simp [Equiv.Perm.mul_apply, hmul_symm])).symm
    have hs2 :
        (∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)) =
          ∑ σ : Equiv.Perm (Fin 4), a (c (c (σ 0))) * b (σ.symm 0) := by
      rw [hs1]
      exact (Fintype.sum_equiv (Equiv.mulLeft c)
        (fun σ => a (c (c (σ 0))) * b (σ.symm 0))
        (fun σ => a (c (σ 0)) * b (σ.symm 0))
        (fun σ => by simp [Equiv.Perm.mul_apply, hmul_symm])).symm
    have ha123 : a 1 + a 2 + a 3 = 0 := by
      have hsum := ha
      rw [Fin.sum_univ_four, ha0, zero_add] at hsum
      linear_combination hsum
    have hcycle : ∀ x : Fin 4, a x + a (c x) + a (c (c x)) = 0 := by
      intro x
      fin_cases x
      · simp [hc0, ha0]
      · simp [hc1, hc2]; linear_combination ha123
      · simp [hc2, hc3]; linear_combination ha123
      · simp [hc3, hc1]; linear_combination ha123
    have h3 : (3 : ℂ) * ∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0) = 0 := by
      calc
        (3 : ℂ) * ∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)
            = (∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)) +
              (∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)) +
              (∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)) := by ring
        _ = (∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)) +
            (∑ σ : Equiv.Perm (Fin 4), a (c (σ 0)) * b (σ.symm 0)) +
            (∑ σ : Equiv.Perm (Fin 4), a (c (c (σ 0))) * b (σ.symm 0)) := by
              linear_combination hs1 + hs2
        _ = ∑ σ : Equiv.Perm (Fin 4), (a (σ 0) + a (c (σ 0)) + a (c (c (σ 0)))) * b (σ.symm 0) := by
              simp only [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun σ _ => ?_
              ring
        _ = 0 := by simp [hcycle]
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rw [Matrix.permanent]
  simp_rw [hprod]
  have hexp :
      (∑ σ : Equiv.Perm (Fin 4), (1 + a (σ 0)) * (1 + b (σ.symm 0))) =
        (∑ _σ : Equiv.Perm (Fin 4), (1 : ℂ)) +
        (∑ σ : Equiv.Perm (Fin 4), a (σ 0)) +
        (∑ σ : Equiv.Perm (Fin 4), b (σ.symm 0)) +
        (∑ σ : Equiv.Perm (Fin 4), a (σ 0) * b (σ.symm 0)) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [hexp, hsum1, hsum2, hsum3, hsum4]
  norm_num
