/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Height
import Mathlib.Data.Setoid.Partition

/-!
-/

open Set

variable (α : Type*) [Preorder α]

variable {α} in
theorem chainHeight_Ioi_add_one (a : α) : chainHeight (Iio a) + 1 = chainHeight (Iic a) := by
  apply WithTop.eq_of_forall_coe_le_iff
  intro n
  rw [ENat.some_eq_coe, ← add_zero (Iic a).chainHeight, ← Nat.cast_zero, le_chainHeight_add_nat_iff,
    ← Nat.cast_one, le_chainHeight_add_nat_iff]
  simp only [subchain, mem_setOf_eq]
  constructor <;> rintro ⟨l, ⟨hlc, hl_mem⟩, hln⟩
  · use l ++ [a]
    grind
  · refine ⟨l.dropLast, ⟨hlc.dropLast, fun i hi ↦ ?_⟩, by grind⟩
    exact hlc.pairwise.rel_dropLast_getLast hi |>.trans_le (hl_mem _ <| List.getLast_mem _)

/-- Elements of a fixed height form an antichain. -/
theorem isAntichain_fiber_chainHeight_Iio (n : ℕ) :
    IsAntichain (· < ·) {x : α | chainHeight (Iio x) = n} := by
  intro x hx y hy hne hlt
  rw [mem_setOf_eq] at hx hy
  have := calc
    (n + 1 : ℕ∞) = chainHeight (Iio x) + 1 := by rw [hx]
    _ = chainHeight (Iic x) := chainHeight_Ioi_add_one _
    _ ≤ chainHeight (Iio y) := chainHeight_mono <| Iic_subset_Iio.2 hlt
    _ = n := hy
  exact n.lt_succ_self.not_ge <| mod_cast this

variable {α}

noncomputable def Finpartition.comapChainHeightIio (h : chainHeight (univ : Set α) ≠ ⊤) :
    Finpartition (univ : Set α) := by
  classical
  refine .ofErase
    ((Finset.range (chainHeight (univ : Set α)).toNat).image fun n : ℕ ↦
      {a | chainHeight (Iio a) = n}) ?_ ?_
  · apply Finset.SupIndep.image
    apply Set.PairwiseDisjoint.supIndep
    rintro m - n - hne
    simp +contextual only [Function.onFun, Function.comp_apply, id_eq, disjoint_left, mem_setOf_eq]
    norm_cast
    simp [hne]
  · refine eq_univ_of_forall fun a ↦ ?_
    suffices ∃ n < (univ : Set α).chainHeight.toNat, (Iio a).chainHeight = ↑n by simpa
    have : (Iio a).chainHeight ≠ ⊤ :=
      ne_top_of_le_ne_top h <| chainHeight_mono <| subset_univ (Iio a)
    use (Iio a).chainHeight.toNat, ?_, ?_
    · refine (Nat.lt_add_one _).trans_le ?_
      rw [← Nat.cast_le (α := ℕ∞)]
      push_cast [ENat.coe_toNat h, ENat.coe_toNat this, chainHeight_Ioi_add_one]
      exact chainHeight_mono <| subset_univ _
    · symm
      simp [this]
