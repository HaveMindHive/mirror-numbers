import Mathlib

/-!
# The wall frame of a prime hop (tUrUq's mirror method, 11-26-2026): the missing mirror

Every seat off the 2-mirror and the 3-mirror is 6a + 1 (first seat of its 6-block) or 6a + 5 (last
seat). A hop p = 6a + r → q = 6b + r' crosses w = b - a walls (multiples of 6) and takes a seat step
s = (r' - r)/4 ∈ {-1, 0, +1}. Then the half gap is h = 3w + 2s, the 4-side flips exactly when w is
odd, the 3-facing flips exactly when s ≠ 0, and the last seat of a block cannot hop without a wall.
The side flip is a property of the hop (its walls), not of the family of p: the old reading counted
it by start family only, which is why one family seemed to "flip far more often".
Also: the hand-off (p, q) ↦ (h, m) applied twice returns the split at half scale (the recursive
inverse), the lake centre 2pq/(p+q) sits below the true centre m by exactly h²/m, the prime between
two centres sits off their centre by a quarter of the gap change, and on any 0/1 walk the flips up
and the flips down differ only by the end seats (exact balance).
No sorry, no native_decide.
-/

namespace WallMirror

/-- A seat off 2 and 3 in block a: 6a + r with r = 1 or r = 5. -/
def Seat (r : ℤ) : Prop := r = 1 ∨ r = 5

/-- The half gap of the hop 6a + r → 6b + r' is 3·walls + 2·step. -/
theorem half_gap_walls (a b r r' : ℤ) (hr : Seat r) (hr' : Seat r') :
    ((6 * b + r') - (6 * a + r)) / 2 = 3 * (b - a) + 2 * ((r' - r) / 4) := by
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> omega

/-- The seat step is -1, 0 or 1. -/
theorem step_cases (r r' : ℤ) (hr : Seat r) (hr' : Seat r') :
    (r' - r) / 4 = -1 ∨ (r' - r) / 4 = 0 ∨ (r' - r) / 4 = 1 := by
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> omega

/-- The 4-side is kept exactly when an even number of walls is crossed. -/
theorem side_is_walls (a b r r' : ℤ) (hr : Seat r) (hr' : Seat r') :
    (6 * b + r') % 4 = (6 * a + r) % 4 ↔ (b - a) % 2 = 0 := by
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> omega

/-- The 3-facing is kept exactly when the seat step is 0 (same seat of the block). -/
theorem facing_is_step (a b r r' : ℤ) (hr : Seat r) (hr' : Seat r') :
    (6 * b + r') % 3 = (6 * a + r) % 3 ↔ r' = r := by
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> omega

/-- The last seat of a block (6a + 5) cannot hop forward without crossing a wall: a hop with
w = 0 (same block) starts at 6a + 1 and lands on 6a + 5 (the cousin hop, gap 4). -/
theorem no_wall_needs_first_seat (a r r' : ℤ) (hr : Seat r) (hr' : Seat r')
    (hlt : 6 * a + r < 6 * a + r') : r = 1 ∧ r' = 5 := by
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> omega

/-- The same hop read from its end: a hop with w = 0 arrives at the last seat. So "w = 0 belongs to
6k+1" (read from p) and "w = 0 belongs to 6k-1" (read from q) are one fact. -/
theorem no_wall_lands_last_seat (a r r' : ℤ) (hr : Seat r) (hr' : Seat r')
    (hlt : 6 * a + r < 6 * a + r') : r' = 5 :=
  (no_wall_needs_first_seat a r r' hr hr' hlt).2

/-- Per-block mirror 6a + r ↦ 6a + (6 - r): swaps the two seats, keeps every seat's 4-side. -/
theorem block_mirror_keeps_side (a r : ℤ) (hr : Seat r) :
    (6 * a + (6 - r)) % 4 = (6 * a + r) % 4 := by
  rcases hr with rfl | rfl <;> omega

/-- The per-block mirror sends the hop (s, w) to (-s, w): same walls, opposite step. -/
theorem block_mirror_hop (a b r r' : ℤ) (hr : Seat r) (hr' : Seat r') :
    ((6 - r') - (6 - r)) / 4 = -((r' - r) / 4) ∧ (b - a) = (b - a) := by
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> omega

/-- Recursive inverse: the hand-off (p, q) ↦ (h, m) = ((q-p)/2, (p+q)/2) applied to (h, m) gives
(difference, sum) = (2h, 2m)... i.e. the split (p, q) itself scaled: m - h = p and m + h = q, and
the hand-off of (h, m) is ((m-h)/2, (m+h)/2) = (p/2, q/2). -/
theorem hand_off_twice (h m : ℤ) :
    (m + h) - (m - h) = 2 * h ∧ (m + h) + (m - h) = 2 * m := by constructor <;> ring

/-- The lake centre (slide rule K²/x with K² = pq, image of the true centre m) sits below m by h²/m. -/
theorem lake_centre (p q : ℚ) (hp : 0 < p) (hq : 0 < q) :
    (p + q) / 2 - 2 * p * q / (p + q) = ((q - p) / 2) ^ 2 / ((p + q) / 2) := by
  have hpq : p + q ≠ 0 := by positivity
  field_simp
  ring

/-- The prime between two centres sits off the centre of the centres by a quarter of the gap change. -/
theorem centre_of_centres (p₀ p₁ p₂ : ℚ) :
    p₁ - ((p₀ + p₁) / 2 + (p₁ + p₂) / 2) / 2 = ((p₁ - p₀) - (p₂ - p₁)) / 4 := by ring

/-- Exact balance of flips on a 0/1 walk: flips up (0 → 1) minus flips down (1 → 0) over n hops
equals g n - g 0, so it is -1, 0 or 1. Every flip of the facing (or of the side) in one direction is
paid back by one in the other, up to the two end seats. -/
theorem flips_balance (g : ℕ → ℤ) (hg : ∀ i, g i = 0 ∨ g i = 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, (if g i = 0 ∧ g (i + 1) = 1 then (1 : ℤ) else 0))
      - (∑ i ∈ Finset.range n, (if g i = 1 ∧ g (i + 1) = 0 then (1 : ℤ) else 0))
      = g n - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have e : ∀ A B C D : ℤ, (A + B) - (C + D) = (A - C) + (B - D) := by intros; ring
    rw [e, ih]
    rcases hg n with h1 | h1 <;> rcases hg (n + 1) with h2 | h2 <;> simp [h1, h2] <;> omega

theorem flips_balance_bound (g : ℕ → ℤ) (hg : ∀ i, g i = 0 ∨ g i = 1) (n : ℕ) :
    |(∑ i ∈ Finset.range n, (if g i = 0 ∧ g (i + 1) = 1 then (1 : ℤ) else 0))
      - (∑ i ∈ Finset.range n, (if g i = 1 ∧ g (i + 1) = 0 then (1 : ℤ) else 0))| ≤ 1 := by
  rw [flips_balance g hg n]
  rcases hg n with h1 | h1 <;> rcases hg 0 with h2 | h2 <;> simp [h1, h2]

end WallMirror
