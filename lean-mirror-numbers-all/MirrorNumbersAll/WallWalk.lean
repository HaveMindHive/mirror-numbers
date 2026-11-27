import Mathlib
import MirrorNumbersAll.PrimeHandOff
import MirrorNumbersAll.Gems

/-!
# The wall walk names exactly the primes, at every size (tUrUq, 11-27-2026)

A seat beside a wall is n = 6k + f with facing f = +1 or -1. A prime block r = 6 kr + fr closes
that seat exactly when k = f fr kr (mod r) (`PrimeHandOff.wall_law_prime`). The walk names a seat
when no block r with r * r <= n closes it.

* `wall_walk`      : a seat n >= 5 beside a wall is prime exactly when no prime block r >= 5 with
  r * r <= n closes it by the wall law. No range: this holds for every n.
* `wall_walk_seat` : every prime past 3 is a seat beside a wall, so the walk misses none.

The walk feeds itself: the blocks it needs for a seat n are the primes up to the square root of n,
and those it has already named (by `wall_walk` applied to the smaller seats, with 2 and 3 as the two
mirrors). So the walk from 2 and 3 alone names every prime in order, with no outside list.
No sorry, no admit, no native_decide.
-/

namespace WallWalk

/-- THE WALL WALK: a seat n = 6k + f (f = +-1, n >= 5) is prime exactly when no prime block
r = 6 kr + fr (r >= 5, r * r <= n) has k = f fr kr (mod r). -/
theorem wall_walk (k f : ℤ) (hf : f = 1 ∨ f = -1) (n : ℕ) (hn : (n : ℤ) = 6 * k + f) (h5 : 5 ≤ n) :
    n.Prime ↔ ∀ r : ℕ, r.Prime → 5 ≤ r → r * r ≤ n →
      ∀ kr fr : ℤ, fr * fr = 1 → (r : ℤ) = 6 * kr + fr → ¬ (r : ℤ) ∣ k - f * fr * kr := by
  constructor
  · intro hp r hr hr5 hrr kr fr hfr hre hd
    have h1 : (r : ℤ) ∣ 6 * k + f := (PrimeHandOff.wall_law_prime r hr hr5 kr fr k f hfr hre).2 hd
    rw [← hn] at h1
    have h2 : r ∣ n := Int.natCast_dvd_natCast.1 h1
    rcases (Nat.dvd_prime hp).1 h2 with h | h
    · omega
    · subst h; nlinarith
  · intro hall
    by_contra hnp
    have hn0 : 0 < n := by omega
    set m := n.minFac with hm
    have hmp : m.Prime := Nat.minFac_prime (by omega)
    have hmd : m ∣ n := Nat.minFac_dvd n
    have hsq : m ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hnp
    have hn6 : n % 6 = 1 ∨ n % 6 = 5 := by omega
    have hm2 : m ≠ 2 := by
      intro h; rw [h] at hmd; omega
    have hm3 : m ≠ 3 := by
      intro h; rw [h] at hmd; omega
    have hm5 : 5 ≤ m := by
      have := hmp.two_le
      rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with h | h | h | h
      · exact absurd h hm2
      · exact absurd h hm3
      · rw [h] at hmp; exact absurd hmp (by decide)
      · exact h
    have hseat := Gems.prime_seat m hmp hm5
    set kr : ℤ := ((m : ℤ) + 1) / 6 with hkr
    set fr : ℤ := (m : ℤ) - 6 * kr with hfr
    have hfr1 : fr * fr = 1 := by
      rcases hseat with h | h
      · have : fr = 1 := by omega
        rw [this]; norm_num
      · have : fr = -1 := by omega
        rw [this]; norm_num
    have hme : (m : ℤ) = 6 * kr + fr := by omega
    have hdz : (m : ℤ) ∣ 6 * k + f := by rw [← hn]; exact Int.natCast_dvd_natCast.2 hmd
    have := (PrimeHandOff.wall_law_prime m hmp hm5 kr fr k f hfr1 hme).1 hdz
    exact hall m hmp hm5 (by nlinarith) kr fr hfr1 hme this

/-- Every prime past 3 is a seat beside a wall: n = 6k + f with f = +-1. -/
theorem wall_walk_seat (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ k f : ℤ, (f = 1 ∨ f = -1) ∧ (p : ℤ) = 6 * k + f := by
  rcases Gems.prime_seat p hp h5 with h | h
  · exact ⟨(p : ℤ) / 6, 1, Or.inl rfl, by omega⟩
  · exact ⟨(p : ℤ) / 6 + 1, -1, Or.inr rfl, by omega⟩

end WallWalk
