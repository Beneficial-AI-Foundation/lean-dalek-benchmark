/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `FieldElement51::sub`

Specification and proof for `FieldElement51::sub`.

This function performs field element subtraction. To avoid underflow, a multiple
of p is added.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Sub

/-
natural language description:

    • Takes two input FieldElement51s a and b and returns another FieldElement51 d
      that is a representant of the difference a - b in the field (modulo p = 2^255 - 19).

    • The implementation adds a multiple of p (namely 16p) as a bias value to a before
      subtraction is performed to avoid underflow: computes (a + 16*p) - b, then reduces

natural language specs:

    • For appropriately bounded FieldElement51s a and b:
      Field51_as_Nat(sub(a, b)) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p), or equivalently
      Field51_as_Nat(sub(a, b)) + Field51_as_Nat(b) ≡ Field51_as_Nat(a) (mod p)
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.sub`**:
- No panic (always returns successfully when bounds are satisfied)
- The result d satisfies the field subtraction property:

  Field51_as_Nat(d) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p), or equivalently
  Field51_as_Nat(d) + Field51_as_Nat(b) ≡ Field51_as_Nat(a) (mod p)

- Requires that input limbs are bounded:
  - For a: limbs must allow addition with 16*p without U64 overflow
    - a[0] must be ≤ 18410715276690587951 (= 2^64 - 1 - 36028797018963664)
    - a[1..4] must be ≤ 18410715276690587663 (= 2^64 - 1 - 36028797018963952)
  - For b: limbs must be ≤ the constants (representing 16*p) to avoid underflow
    - b[0] must be ≤ 36028797018963664
    - b[1..4] must be ≤ 36028797018963952
  To make the theorem more easily readable and provable, we
  replace these precise bounds with the slightly looser bounds
  a[i] < 2^63  and b[i] < 2^54
-/
@[progress]
theorem sub_spec (a b : Array U64 5#usize)
    (h_bounds_a : ∀ i < 5, a[i]!.val < 2 ^ 63)
    (h_bounds_b : ∀ i < 5, b[i]!.val < 2 ^ 54) :
    ∃ d, sub a b = ok d ∧
    (∀ i < 5, d[i]!.val < 2 ^ 52) ∧
    (Field51_as_Nat d + Field51_as_Nat b) % p = Field51_as_Nat a % p := by
  unfold sub
  -- To do: some problem using `progress*` in this proof and so doing each step manually.
  -- Change to `progress*` when possible.

  set k := 36028797018963664#u64 with hk
  set j := 36028797018963952#u64 with hj

  -- Limb 0
  have hlen_a0 : 0#usize < a.length := by scalar_tac
  obtain ⟨a0, ha0_ok⟩ := Array.index_usize_spec a 0#usize hlen_a0
  simp only [ha0_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha0 : (a.val)[0]! = a0

  have ha0_bound : a0.val + k.val ≤ U64.max := by
    have := h_bounds_a 0 (by simp); scalar_tac
  obtain ⟨a0', ha0'_ok, ha0'_val⟩ := U64.add_spec ha0_bound
  simp only [ha0'_ok, bind_tc_ok]

  have hlen_b0 : 0#usize < b.length := by scalar_tac
  obtain ⟨b0, hb0_ok⟩ := Array.index_usize_spec b 0#usize hlen_b0
  simp only [hb0_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb0 : (b.val)[0]! = b0

  have ha0'_sub_bound : b0 ≤ a0'.val := by
    rw [ha0'_val, ← hb0]
    have := h_bounds_b 0 (by simp); scalar_tac
  obtain ⟨i3, hi3_ok, hi3_val, hi3_val'⟩ := U64.sub_spec ha0'_sub_bound
  simp only [hi3_ok, bind_tc_ok]

  -- Limb 1
  have hlen_a1 : 1#usize < a.length := by scalar_tac
  obtain ⟨a1, ha1_ok⟩ := Array.index_usize_spec a 1#usize hlen_a1
  simp only [ha1_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha1 : (a.val)[1]! = a1

  have ha1_bound : a1.val + j.val ≤ U64.max := by
    have := h_bounds_a 1 (by simp); scalar_tac
  obtain ⟨a1', ha1'_ok, ha1'_val⟩ := U64.add_spec ha1_bound
  simp only [ha1'_ok, bind_tc_ok]

  have hlen_b1 : 1#usize < b.length := by scalar_tac
  obtain ⟨b1, hb1_ok⟩ := Array.index_usize_spec b 1#usize hlen_b1
  simp only [hb1_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb1 : (b.val)[1]! = b1

  have ha1'_sub_bound : b1 ≤ a1'.val := by
    rw [ha1'_val, ← hb1]
    have := h_bounds_b 1 (by simp); scalar_tac
  obtain ⟨i7, hi7_ok, hi7_val, hi7_val'⟩ := U64.sub_spec ha1'_sub_bound
  simp only [hi7_ok, bind_tc_ok]

  -- Limb 2
  have hlen_a2 : 2#usize < a.length := by scalar_tac
  obtain ⟨a2, ha2_ok⟩ := Array.index_usize_spec a 2#usize hlen_a2
  simp only [ha2_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha2 : (a.val)[2]! = a2

  have ha2_bound : a2.val + j.val ≤ U64.max := by
    have := h_bounds_a 2 (by simp); scalar_tac
  obtain ⟨a2', ha2'_ok, ha2'_val⟩ := U64.add_spec ha2_bound
  simp only [ha2'_ok, bind_tc_ok]

  have hlen_b2 : 2#usize < b.length := by scalar_tac
  obtain ⟨b2, hb2_ok⟩ := Array.index_usize_spec b 2#usize hlen_b2
  simp only [hb2_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb2 : (b.val)[2]! = b2

  have ha2'_sub_bound : b2 ≤ a2'.val := by
    rw [ha2'_val, ← hb2]
    have := h_bounds_b 2 (by simp); scalar_tac
  obtain ⟨i11, hi11_ok, hi11_val, hi11_val'⟩ := U64.sub_spec ha2'_sub_bound
  simp only [hi11_ok, bind_tc_ok]

  -- Limb 3
  have hlen_a3 : 3#usize < a.length := by scalar_tac
  obtain ⟨a3, ha3_ok⟩ := Array.index_usize_spec a 3#usize hlen_a3
  simp only [ha3_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha3 : (a.val)[3]! = a3

  have ha3_bound : a3.val + j.val ≤ U64.max := by
    have := h_bounds_a 3 (by simp); scalar_tac
  obtain ⟨a3', ha3'_ok, ha3'_val⟩ := U64.add_spec ha3_bound
  simp only [ha3'_ok, bind_tc_ok]

  have hlen_b3 : 3#usize < b.length := by scalar_tac
  obtain ⟨b3, hb3_ok⟩ := Array.index_usize_spec b 3#usize hlen_b3
  simp only [hb3_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb3 : (b.val)[3]! = b3

  have ha3'_sub_bound : b3 ≤ a3'.val := by
    rw [ha3'_val, ← hb3]
    have := h_bounds_b 3 (by simp); scalar_tac
  obtain ⟨i15, hi15_ok, hi15_val, hi15_val'⟩ := U64.sub_spec ha3'_sub_bound
  simp only [hi15_ok, bind_tc_ok]

  -- Limb 4
  have hlen_a4 : 4#usize < a.length := by scalar_tac
  obtain ⟨a4, ha4_ok⟩ := Array.index_usize_spec a 4#usize hlen_a4
  simp only [ha4_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha4 : (a.val)[4]! = a4

  have ha4_bound : a4.val + j.val ≤ U64.max := by
    have := h_bounds_a 4 (by simp); scalar_tac
  obtain ⟨a4', ha4'_ok, ha4'_val⟩ := U64.add_spec ha4_bound
  simp only [ha4'_ok, bind_tc_ok]

  have hlen_b4 : 4#usize < b.length := by scalar_tac
  obtain ⟨b4, hb4_ok⟩ := Array.index_usize_spec b 4#usize hlen_b4
  simp only [hb4_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb4 : (b.val)[4]! = b4

  have ha4'_sub_bound : b4 ≤ a4'.val := by
    rw [ha4'_val, ← hb4]
    have := h_bounds_b 4 (by simp); scalar_tac
  obtain ⟨i19, hi19_ok, hi19_val, hi19_val'⟩ := U64.sub_spec ha4'_sub_bound
  simp only [hi19_ok, bind_tc_ok]

  -- Call reduce and get the result
  obtain ⟨d, hreduce_ok, hreduce_bounds, hreduce_eq⟩ :=
    reduce_spec (Array.make 5#usize [i3, i7, i11, i15, i19])
  simp only [hreduce_ok, ok.injEq, exists_eq_left']

  refine ⟨fun i hi ↦ ?_, ?_⟩
  · -- BEGIN TASK
    sorry
    -- END TASK
  · -- BEGIN TASK
    sorry
    -- END TASK

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Sub
