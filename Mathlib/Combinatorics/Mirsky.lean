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

variable (α : Type _) [Preorder α]

/-- Elements of a fixed height form an antichain. -/
theorem isAntichain_fiber_chainHeight_Iic (n : ℕ) :
    IsAntichain (· < ·) { x : α | chainHeight (Iic x) = n } := fun x hx y hy hne hlt ↦
  (Nat.cast_lt.2 n.lt_succ_self).not_le <|
    calc (n + 1 : ℕ∞) = chainHeight (Iic x) + 1 := by rw [← hx.out]
    _ = chainHeight (insert y (Iic x)) :=
      (chainHeight_insert_of_forall_lt _ fun z hz ↦ hz.trans_lt hlt).symm
    _ ≤ chainHeight (Iic y) := chainHeight_mono <| insert_subset.2 ⟨le_rfl, Iic_subset_Iic.2 hlt.le⟩
    _ = n := hy

variable {α}

theorem chainHeight_Iic_ne_zero (x : α) : chainHeight (Iic x) ≠ 0 := by simp [nonempty_Iic.ne_empty]

def Finpartition.comapChainHeightIic (h : chainHeight (univ : Set α) ≠ ⊤) :
    Finpartition (univ : Set α) where
  parts := _
  supIndep := _
  supParts := _
  not_bot_mem := _
