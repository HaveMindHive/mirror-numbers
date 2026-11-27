import Mathlib

/-!
# Two parts (tUrUq's mirror method, 11-26-2026): halving = the neighbours, turn = the number itself

An odd n read two ways: halving k, k+1, k (k = (n-1)/2: the neighbours n-1, n+1 halved, the left-outs' blocks)
beside its turn face a × b (its own blocks). The tie: both are square-difference pictures of n,
centre² − wing² = n, with centre − wing = the block. The halving is the block-1 face. A prime has exactly one
picture (prime_one_picture); an odd composite has one more per face (face_square). The neighbours never carry a
block of n (neighbour_up/down). A candidate p + 2h has p's halving shifted by h (candidate_shift); the seat
rule reads the halving's sum (wing_add_centre); the repeat reading q ≡ p (mod r) is h ≡ 0 (mod r) (repeat_*).
Per family p mod 12 the 2 and 3 of the left-outs sit in fixed places (family_*). Decimal unit line: 11 × d =
10d + d (eleven_unit); (k ones)(10^(k−1)+1) = (k−1 ones) 2 (k−1 ones) as repunit_mirror over 9×.
No sorry, no native_decide.
-/

namespace TwoParts

/-- Halving of odd n = 2k+1 is the square-difference picture with block 1: (k+1)² − k² = 2k+1. -/
theorem halving_square (k : ℕ) : (k + 1) ^ 2 - k ^ 2 = 2 * k + 1 := by
  have : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
  omega

/-- A turn face a × b of odd a = 2i+1, b = 2j+1 is the same shape: centre i+j+1, wing j−i. -/
theorem face_square (i j : ℤ) : (i + j + 1) ^ 2 - (j - i) ^ 2 = (2 * i + 1) * (2 * j + 1) := by ring

/-- centre − wing = the block a, centre + wing = the other block b. -/
theorem face_block (i j : ℤ) :
    (i + j + 1) - (j - i) = 2 * i + 1 ∧ (i + j + 1) + (j - i) = 2 * j + 1 := by
  constructor <;> ring

/-- The halving centre sits above the face centre by (a−1)(b−1)/2: 2 × (halving centre − face centre) = (a−1)(b−1). -/
theorem centre_gap (i j : ℤ) :
    2 * (((2 * i + 1) * (2 * j + 1) + 1) / 2 - (i + j + 1)) = (2 * i) * (2 * j) := by
  have h : ((2 * i + 1) * (2 * j + 1) + 1) / 2 = 2 * i * j + i + j + 1 := by
    have : (2 * i + 1) * (2 * j + 1) + 1 = 2 * (2 * i * j + i + j + 1) := by ring
    rw [this]; omega
  rw [h]; ring

/-- A prime has one picture: (c−w)(c+w) = p with w < c forces c − w = 1 and c + w = p (the halving). -/
theorem prime_one_picture (p c w : ℕ) (hp : p.Prime) (hw : w < c) (h : (c - w) * (c + w) = p) :
    c - w = 1 ∧ c + w = p := by
  have hd : (c - w) ∣ p := ⟨c + w, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · refine ⟨h1, ?_⟩
    rw [h1] at h; simpa using h
  · exfalso
    rw [h1] at h
    have h2 : c + w = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h, mul_one])
    have := hp.two_le
    omega

/-- The upper neighbour carries no block of n. -/
theorem neighbour_up (n : ℕ) : Nat.Coprime n (n + 1) := by
  rw [Nat.coprime_self_add_right]; exact Nat.coprime_one_right n

/-- The lower neighbour carries no block of n+1. -/
theorem neighbour_down (n : ℕ) : Nat.Coprime (n + 1) n := (neighbour_up n).symm

/-- Candidate halving: the picture of p + 2h is p's shifted by h (odd p). -/
theorem candidate_shift (p h : ℕ) (hp : p % 2 = 1) :
    (p + 2 * h - 1) / 2 = (p - 1) / 2 + h ∧ (p + 2 * h + 1) / 2 = (p + 1) / 2 + h := by omega

/-- wing + centre = n for odd n: a seat rule r ∣ n reads the halving's sum. -/
theorem wing_add_centre (n : ℕ) (hn : n % 2 = 1) : (n - 1) / 2 + (n + 1) / 2 = n := by omega

/-- Left-outs of the candidate via h (r = 5): 5 ∣ y−1 iff h ≡ −wing_p, 5 ∣ y+1 iff h ≡ −centre_p. -/
theorem five_left_outs (p h : ℕ) (hp : p % 2 = 1) :
    ((p + 2 * h - 1) % 5 = 0 ↔ (h + (p - 1) / 2) % 5 = 0) ∧
    ((p + 2 * h + 1) % 5 = 0 ↔ (h + (p + 1) / 2) % 5 = 0) := by omega

/-- The repeat reading: p + 2h sits in p's seat mod 3 iff h ≡ 0 (mod 3). -/
theorem repeat_three (p h : ℕ) : (p + 2 * h) % 3 = p % 3 ↔ h % 3 = 0 := by omega
theorem repeat_five (p h : ℕ) : (p + 2 * h) % 5 = p % 5 ↔ h % 5 = 0 := by omega
theorem repeat_seven (p h : ℕ) : (p + 2 * h) % 7 = p % 7 ↔ h % 7 = 0 := by omega

/-- Per family: where the 2 and 3 of the left-outs sit in the halving (wing mod 6, centre mod 6). -/
theorem family_one (p : ℕ) (h : p % 12 = 1) : ((p - 1) / 2) % 6 = 0 ∧ ((p + 1) / 2) % 6 = 1 := by omega
theorem family_five (p : ℕ) (h : p % 12 = 5) : ((p - 1) / 2) % 6 = 2 ∧ ((p + 1) / 2) % 6 = 3 := by omega
theorem family_seven (p : ℕ) (h : p % 12 = 7) : ((p - 1) / 2) % 6 = 3 ∧ ((p + 1) / 2) % 6 = 4 := by omega
theorem family_eleven (p : ℕ) (h : p % 12 = 11) : ((p - 1) / 2) % 6 = 5 ∧ ((p + 1) / 2) % 6 = 0 := by omega

/-- Wing × centre carries 6 off 2 and 3: p = 6k+1 gives 3k(3k+1), p = 6k+5 gives (3k+2)(3k+3). -/
theorem wing_centre_six_plus (k : ℕ) : 6 ∣ (3 * k) * (3 * k + 1) := by
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self k
  exact ⟨t + k ^ 2, by nlinarith [ht]⟩
theorem wing_centre_six_minus (k : ℕ) : 6 ∣ (3 * k + 2) * (3 * k + 3) := by
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self k
  exact ⟨t + k ^ 2 + 2 * k + 1, by nlinarith [ht]⟩

/-- Decimal unit line: 11 is the one of 10s, d × 11 = 10d + d ("dd"). -/
theorem eleven_unit (d : ℕ) : 11 * d = 10 * d + d := by ring

/-- Repunit mirror, times 9: (10^(m+1) − 1)(10^m + 1) = (10^m − 1)·10^(m+1) + 18·10^m + (10^m − 1),
i.e. (m+1 ones) × (10^m + 1) = (m ones) 2 (m ones). -/
theorem repunit_mirror (m : ℕ) :
    ((10 : ℤ) ^ (m + 1) - 1) * (10 ^ m + 1) = (10 ^ m - 1) * 10 ^ (m + 1) + 18 * 10 ^ m + (10 ^ m - 1) := by
  ring

end TwoParts
