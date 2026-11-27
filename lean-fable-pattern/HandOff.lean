import Mathlib

/-!
# The hand-off law (tUrUq's split, 11-26-2026): the common relationship of a prime split

A split p < q (both seats off the 2-mirror and the 3-mirror, as every prime from 5 on is) has
half gap h and centre m = p + h, so q = p + 2h = m + h.
The two small mirrors are handed off: the 2-mirror sits on exactly one of m, h; the 3-mirror
sits on exactly one of m, h; no mirror r passes through both m and h unless it passes through
p and q themselves. The half gap's own seat on the 3-mirror is fixed by p's facing
(h ≢ p mod 3), and the 4-side (p mod 4) is kept exactly when h is even.
Everything here is about the seats, not about primality: it holds for any two odd numbers
off the 3-mirror, which is why it is read from p alone before q is known.
No sorry, no native_decide.
-/

namespace HandOff

/-- Off the 2-mirror and the 3-mirror: the seats every prime ≥ 5 takes. -/
def Off23 (p h : ℕ) : Prop := p % 2 = 1 ∧ (p + 2 * h) % 2 = 1 ∧ p % 3 ≠ 0 ∧ (p + 2 * h) % 3 ≠ 0

/-- The 2-mirror is handed to exactly one of the centre p + h and the half gap h. -/
theorem two_hand_off (p h : ℕ) (hs : Off23 p h) : ((p + h) % 2 = 0) ↔ ¬ (h % 2 = 0) := by
  obtain ⟨h1, -, -, -⟩ := hs
  omega

/-- The 3-mirror is handed to exactly one of the centre and the half gap. -/
theorem three_hand_off (p h : ℕ) (hs : Off23 p h) : ((p + h) % 3 = 0) ↔ ¬ (h % 3 = 0) := by
  obtain ⟨-, -, h3, h4⟩ := hs
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with hp3 | hp3 <;>
    rcases (by omega : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2) with hh3 | hh3 | hh3 <;> omega

/-- A mirror through both the centre and the half gap passes through p and q themselves,
so for a prime split no mirror r ≥ 2 does. -/
theorem never_both (p h r : ℕ) (hm : r ∣ p + h) (hh : r ∣ h) : r ∣ p ∧ r ∣ p + 2 * h := by
  refine ⟨?_, ?_⟩
  · have := Nat.dvd_sub hm hh
    simpa using this
  · have e : p + 2 * h = (p + h) + h := by ring
    rw [e]; exact Nat.dvd_add hm hh

/-- The half gap's seat on the 3-mirror is read from p's facing alone: h ≢ p (mod 3). -/
theorem half_gap_facing (p h : ℕ) (hs : Off23 p h) : h % 3 ≠ p % 3 := by
  obtain ⟨-, -, h3, h4⟩ := hs
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with hp3 | hp3 <;>
    rcases (by omega : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2) with hh3 | hh3 | hh3 <;> omega

/-- The 4-side (circle primes 1 mod 4 vs 3 mod 4) is kept exactly when the half gap is even. -/
theorem side_kept (p h : ℕ) (hs : Off23 p h) : (h % 2 = 0) ↔ (p + 2 * h) % 4 = p % 4 := by
  obtain ⟨h1, -, -, -⟩ := hs
  omega

/-- The facing on the 3-mirror is kept exactly when 3 divides h (the gap is a multiple of 6). -/
theorem facing_kept (p h : ℕ) (hs : Off23 p h) : (h % 3 = 0) ↔ (p + 2 * h) % 3 = p % 3 := by
  obtain ⟨-, -, h3, h4⟩ := hs
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with hp3 | hp3 <;>
    rcases (by omega : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2) with hh3 | hh3 | hh3 <;> omega

/-- Each odd prime seat p ≥ 5 has one neighbour that is a prime inside the evens (2 mod 4):
on the right for the circle side p ≡ 1 (mod 4), on the left for p ≡ 3 (mod 4). -/
theorem e2_neighbour (p : ℕ) (hp : p % 2 = 1) :
    (p % 4 = 1 → (p + 1) % 4 = 2) ∧ (p % 4 = 3 → (p - 1) % 4 = 2) := by omega

/-- Per family (p mod 12), the half gap h sits in exactly four of the six classes mod 6;
the 3-facing picks the four, the 4-side does not change them. -/
theorem family_classes (p h : ℕ) (hs : Off23 p h) :
    (p % 3 = 1 → h % 6 ∈ ({0, 2, 3, 5} : Finset ℕ)) ∧
    (p % 3 = 2 → h % 6 ∈ ({0, 1, 3, 4} : Finset ℕ)) := by
  obtain ⟨-, -, h3, h4⟩ := hs
  constructor <;> intro hp <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;>
    rcases (by omega : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2) with hh3 | hh3 | hh3 <;> omega

end HandOff
