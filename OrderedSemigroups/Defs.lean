
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Ordered Semigroups

This file defines ordered semigroups and provides some basic instances.

-/

public section

variable {α : Type*}

class IsLeftOrderedSemigroup (α : Type*) [Semigroup α] [PartialOrder α] where
  mul_le_mul_left' (a b : α) :a ≤ b → ∀ c : α, c * a ≤ c * b

instance [Semigroup α] [PartialOrder α] [IsLeftOrderedSemigroup α] :
    MulLeftMono α where
  elim a b c bc := IsLeftOrderedSemigroup.mul_le_mul_left' b c bc a

class IsRightOrderedSemigroup (α : Type*) [Semigroup α] [PartialOrder α] where
  mul_le_mul_right' (a b : α) : a ≤ b → ∀ c : α, a * c ≤ b * c

instance [Semigroup α] [PartialOrder α] [IsRightOrderedSemigroup α] :
    MulRightMono α where
  elim a b c bc := IsRightOrderedSemigroup.mul_le_mul_right' b c bc a

class IsOrderedSemigroup (α : Type*) [Semigroup α] [PartialOrder α] extends
    IsLeftOrderedSemigroup α, IsRightOrderedSemigroup α

class IsLeftOrderedCancelSemigroup (α : Type*) [Semigroup α] [PartialOrder α]
    extends IsLeftOrderedSemigroup α where
  le_of_mul_le_mul_right' : ∀ a b c : α, a * b ≤ a * c → b ≤ c

instance [Semigroup α] [PartialOrder α] [IsLeftOrderedCancelSemigroup α] :
    MulLeftReflectLE α where
  le_of_mul_le_mul_left' h := IsLeftOrderedCancelSemigroup.le_of_mul_le_mul_right' _ _ _ h

instance [Semigroup α] [PartialOrder α] [IsLeftOrderedCancelSemigroup α] :
    MulLeftReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ fun _ ↦ MulLeftReflectLE.le_of_mul_le_mul_left'

instance [Semigroup α] [PartialOrder α] [IsLeftOrderedCancelSemigroup α] :
    IsLeftCancelMul α where
  mul_left_cancel _ _ _ h :=
    (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge

class IsRightOrderedCancelSemigroup (α : Type*) [Semigroup α] [PartialOrder α]
    extends IsRightOrderedSemigroup α where
  le_of_mul_le_mul_left' : ∀ a b c : α, b * a ≤ c * a → b ≤ c

instance [Semigroup α] [PartialOrder α] [IsRightOrderedCancelSemigroup α] :
    MulRightReflectLE α where
  le_of_mul_le_mul_right' h := IsRightOrderedCancelSemigroup.le_of_mul_le_mul_left' _ _ _ h

instance [Semigroup α] [PartialOrder α] [IsRightOrderedCancelSemigroup α] :
    MulRightReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ fun _ ↦ MulRightReflectLE.le_of_mul_le_mul_right'

instance [Semigroup α] [PartialOrder α] [IsRightOrderedCancelSemigroup α] :
    IsRightCancelMul α where
  mul_right_cancel _ _ _ h :=
    (le_of_mul_le_mul_right' h.le).antisymm <| le_of_mul_le_mul_right' h.ge

class IsOrderedCancelSemigroup (α : Type*) [Semigroup α] [PartialOrder α]
    extends IsLeftOrderedCancelSemigroup α, IsRightOrderedCancelSemigroup α

instance [Semigroup α] [PartialOrder α] [IsOrderedCancelSemigroup α] :
    IsOrderedSemigroup α where

-- Strict monotonicity instances (derived from monotonicity + cancellation)
instance [Semigroup α] [PartialOrder α] [IsLeftOrderedCancelSemigroup α] :
    MulLeftStrictMono α where
  elim a b c bc := by
    have hle := IsLeftOrderedSemigroup.mul_le_mul_left' b c bc.le a
    have hne : a * b ≠ a * c := fun h => bc.ne (mul_left_cancel h)
    exact lt_of_le_of_ne hle hne

instance [Semigroup α] [PartialOrder α] [IsRightOrderedCancelSemigroup α] :
    MulRightStrictMono α where
  elim a b c bc := by
    have hle := IsRightOrderedSemigroup.mul_le_mul_right' b c bc.le a
    have hne : b * a ≠ c * a := fun h => bc.ne (mul_right_cancel h)
    exact lt_of_le_of_ne hle hne
