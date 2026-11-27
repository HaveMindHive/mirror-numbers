import Mathlib

/-!
# The digit mirror on the offset-eleven line (tUrUq, Turaq Rayn-McLean, 11-27-2026)

His words: "it absolutely is, any time you see that mirror structure it is, but we need to nail that
relationship down. all that weird digit stuff is what i want to explain."

The per-block mirror of his scripts (standard-mirror-line_v1.0_11-26-2026.py): inside block j of width O,
n faces (2j+1)·O − n, a multiple of O folding to the block below. With O = B + 1, the one of base B
(|^1: 3 in base 2, 11 in base 10, 101 in base 100):

* `two_digit_sum`, `two_digit_diff`: a two-digit number and its reversal add to (B+1)·(digit sum) and
  differ by (B−1)·(digit difference): the 11 mirror and the 9 mirror of base 10.
* `block_mirror_add`: for every n ≥ 1, n and its block mirror add to (2j+1)·O.
* `block_mirror_eq_rev_iff`: for EVERY base B ≥ 2 and every two-digit (a, c), the block mirror of a·B + c
  on O = B + 1 is its reversal c·B + a exactly when the digits are neighbours (a = c + 1 or c = a + 1).
* `neighbour_rev_step`: on those pairs the reversal moves by exactly one B − 1 (one 9 in base 10).
* finite facts by `decide`: the nine decimal pairs, the base-2 pair, the 101 pairs, no three-digit decimal
  number is its own block mirror's reversal on 11, and the corrected first crossings (`first_crossings`).
No sorry, no admit, no native_decide.
-/

namespace DigitMirror

/-- Block index of his script: n // O, a multiple of O counted in the block below. -/
def blockIdx (O n : ℕ) : ℕ := if n % O = 0 then n / O - 1 else n / O

/-- The per-block mirror n ↦ (2j+1)·O − n (standard-mirror-line_v1.0_11-26-2026.py, `block_mirror`). -/
def blockMirror (O n : ℕ) : ℕ := (2 * blockIdx O n + 1) * O - n

/-- Two-digit reversal in base B: a·B + c ↦ c·B + a. -/
def rev2 (B n : ℕ) : ℕ := (n % B) * B + n / B

/-- Three-digit decimal reversal. -/
def rev3 (n : ℕ) : ℕ := (n % 10) * 100 + (n / 10 % 10) * 10 + n / 100

/-- The 11 mirror (one of the base): n + rev n = (B+1) × digit sum. -/
theorem two_digit_sum (B a c : ℕ) : (a * B + c) + (c * B + a) = (B + 1) * (a + c) := by ring

/-- The 9 mirror (base less one): n − rev n = (B−1) × digit difference. -/
theorem two_digit_diff (B a c : ℤ) : (a * B + c) - (c * B + a) = (B - 1) * (a - c) := by ring

/-- n and its block mirror fill the block: n + M(n) = (2j+1)·O, for every n ≥ 1. -/
theorem block_mirror_add (O n : ℕ) (hO : 0 < O) (hn : 0 < n) :
    n + blockMirror O n = (2 * blockIdx O n + 1) * O := by
  unfold blockMirror
  have key : n ≤ (2 * blockIdx O n + 1) * O := by
    have hd := Nat.div_add_mod n O
    have hr := Nat.mod_lt n hO
    unfold blockIdx
    split_ifs with h
    · rw [h, add_zero] at hd
      obtain ⟨q, hq⟩ : ∃ q, n / O = q + 1 := by
        rcases Nat.eq_zero_or_pos (n / O) with h0 | h0
        · rw [h0, mul_zero] at hd; omega
        · exact ⟨n / O - 1, by omega⟩
      rw [hq] at hd ⊢
      simp only [Nat.add_sub_cancel]
      have e1 : (2 * q + 1) * O = 2 * (O * q) + O := by ring
      have e2 : O * (q + 1) = O * q + O := by ring
      omega
    · have e1 : (2 * (n / O) + 1) * O = 2 * (O * (n / O)) + O := by ring
      omega
  omega

/-- The block mirror equals m exactly when n + m fills the block. -/
theorem block_mirror_eq_iff (O n m : ℕ) (hO : 0 < O) (hn : 0 < n) :
    blockMirror O n = m ↔ n + m = (2 * blockIdx O n + 1) * O := by
  have := block_mirror_add O n hO hn
  omega

/-- The block index of a two-digit number a·B + c on O = B + 1. -/
theorem idx_two_digit (B a c : ℕ) (ha : a < B) (hc : c < B) (hn : 0 < a * B + c) :
    (a < c → blockIdx (B + 1) (a * B + c) = a) ∧ (c ≤ a → blockIdx (B + 1) (a * B + c) = a - 1) := by
  have hB : 0 < B + 1 := by omega
  constructor
  · intro h
    have e : a * B + c = (B + 1) * a + (c - a) := by
      obtain ⟨d, rfl⟩ : ∃ d, c = a + d := ⟨c - a, by omega⟩
      simp only [Nat.add_sub_cancel_left]; ring
    have hdm := (Nat.div_mod_unique hB).2 ⟨(by rw [e]; ring : c - a + (B + 1) * a = a * B + c), by omega⟩
    unfold blockIdx; rw [if_neg (by omega)]; exact hdm.1
  · intro h
    rcases Nat.eq_or_lt_of_le h with h | h
    · -- c = a: a multiple, a ≥ 1
      subst h
      have e : c * B + c = (B + 1) * c := by ring
      have hc1 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · subst h0; simp at hn
        · exact h0
      have hdm := (Nat.div_mod_unique hB).2 ⟨(by rw [e]; ring : 0 + (B + 1) * c = c * B + c), hB⟩
      unfold blockIdx; rw [if_pos hdm.2, hdm.1]
    · obtain ⟨d, rfl⟩ : ∃ d, a = c + d + 1 := ⟨a - c - 1, by omega⟩
      have hdm := (Nat.div_mod_unique hB).2
        ⟨(by ring : (B - d) + (B + 1) * (c + d) + 0 = (B - d) + (B + 1) * (c + d)), (by omega : B - d < B + 1)⟩
      have e : (c + d + 1) * B + c = (B - d) + (B + 1) * (c + d) := by
        obtain ⟨k, hk⟩ : ∃ k, B = d + k := ⟨B - d, by omega⟩
        subst hk; simp only [Nat.add_sub_cancel_left]; ring
      unfold blockIdx; rw [e, if_neg (by rw [hdm.2]; omega), hdm.1]; omega

/-- THE DIGIT MIRROR LAW, every base B ≥ 2: on the line of the base's one O = B + 1, the block mirror of a
two-digit number is its digit reversal exactly when its two digits are neighbours. -/
theorem block_mirror_eq_rev_iff (B a c : ℕ) (ha : a < B) (hc : c < B) (hn : 0 < a * B + c) :
    blockMirror (B + 1) (a * B + c) = c * B + a ↔ (a = c + 1 ∨ c = a + 1) := by
  rw [block_mirror_eq_iff _ _ _ (by omega) hn, two_digit_sum, mul_comm (B + 1)]
  rw [Nat.mul_right_cancel_iff (by omega : 0 < B + 1)]
  obtain ⟨h1, h2⟩ := idx_two_digit B a c ha hc hn
  rcases lt_or_ge a c with h | h
  · rw [h1 h]; omega
  · rw [h2 h]
    have : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; omega
      · exact h0
    omega

/-- The general shift: the block mirror is the reversal moved by whole (B+1)s, (2j+1) − (a+c) of them. -/
theorem block_mirror_shift (B a c : ℕ) (hn : 0 < a * B + c) :
    (blockMirror (B + 1) (a * B + c) : ℤ) =
      (c * B + a : ℤ) + (B + 1) * ((2 * blockIdx (B + 1) (a * B + c) + 1 : ℤ) - (a + c)) := by
  have h := block_mirror_add (B + 1) (a * B + c) (by omega) hn
  have h' : ((a * B + c + blockMirror (B + 1) (a * B + c) : ℕ) : ℤ) =
      (((2 * blockIdx (B + 1) (a * B + c) + 1) * (B + 1) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

/-- On a neighbour pair the reversal steps by exactly one B − 1 (in base 10, one 9). -/
theorem neighbour_rev_step (B a : ℕ) : ((a + 1) * B + a) = (a * B + (a + 1)) + (B - 1) ∨ B = 0 := by
  rcases Nat.eq_zero_or_pos B with h | h
  · exact Or.inr h
  · left; obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring

/-- Base 10: the nine neighbour pairs 01 ↔ 10, 12 ↔ 21, …, 89 ↔ 98 are all the two-digit block-mirror reversals. -/
theorem decimal_pairs :
    (List.range 100).filter (fun n => 0 < n ∧ blockMirror 11 n = rev2 10 n) =
      [1, 10, 12, 21, 23, 32, 34, 43, 45, 54, 56, 65, 67, 76, 78, 87, 89, 98] := by decide

/-- Base 2 on O = 3 (|^1 in base 2): the one pair 01 ↔ 10, that is 1 ↔ 2. -/
theorem binary_pair :
    (List.range 4).filter (fun n => 0 < n ∧ blockMirror 3 n = rev2 2 n) = [1, 2] := by decide

/-- One scale up, base 100 on O = 101: decimal a0(a+1) ↔ (a+1)0a. -/
theorem hundred_pairs :
    (List.range 1000).filter (fun n => 0 < n ∧ blockMirror 101 n = rev3 n) =
      [1, 100, 102, 201, 203, 302, 304, 403, 405, 504, 506, 605, 607, 706, 708, 807, 809, 908] := by
  decide +kernel

/-- On the 11 line no three-digit number has its block mirror equal to its reversal. -/
theorem no_three_digit_on_eleven :
    (List.range' 100 900).filter (fun n => blockMirror 11 n = rev3 n) = [] := by decide +kernel

/-! ## His classes (offset-eleven_v1.0_11-26-2026.py): clean evens and frays -/

/-- Odd core with fuel (halve while even). -/
def oddCore : ℕ → ℕ → ℕ
  | 0, m => m
  | f + 1, m => if m % 2 = 0 ∧ m ≠ 0 then oddCore f (m / 2) else m

def core (m : ℕ) : ℕ := oddCore m m

/-- x is 2^a (x ≥ 1) exactly when its odd core is 1. -/
def isPow2 (x : ℕ) : Bool := x ≠ 0 ∧ core x = 1

/-- `strand(c) != "above"` in his script: self 1|3, 2^a+1, 3·2^a+1, the points 11 and 15. -/
def onLine (c : ℕ) : Bool :=
  c = 1 ∨ c = 3 ∨ isPow2 (c - 1) ∨ ((c - 1) % 3 = 0 ∧ isPow2 ((c - 1) / 3)) ∨ c = 11 ∨ c = 15

/-- `clean(m) != "fray"` in his script: core on the ratio-two line, or a doubled prime 2p. -/
def clean (m : ℕ) : Bool := onLine (core m) ∨ (m % 4 = 2 ∧ (m / 2).Prime)

/-- Crossing, prime side: a prime faces a frayed even (his ruling: 67 → 76 is one). -/
def crossP (n : ℕ) : Bool := n.Prime ∧ blockMirror 11 n ≠ 0 ∧ ¬ clean (blockMirror 11 n)

/-- Crossing, composite side: an odd composite faces a doubled prime 2q (33 ↔ 22). -/
def crossC (n : ℕ) : Bool :=
  n % 2 = 1 ∧ 3 ≤ n ∧ ¬ n.Prime ∧ blockMirror 11 n % 4 = 2 ∧ (blockMirror 11 n / 2).Prime

theorem his_rows :
    [67, 73, 97, 33].map (blockMirror 11) = [76, 70, 90, 22] ∧
    clean 76 = false ∧ clean 70 = false ∧ clean 8 = true ∧ clean 46 = true ∧ clean 60 = true := by decide

/-- The corrected first crossings below 100, both sides, in order. -/
theorem first_crossings :
    (List.range 100).filter (fun n => crossP n ∨ crossC n) = [33, 39, 63, 67, 69, 73, 93, 97] := by
  decide +kernel

/-- Prime side below 100: 67 ↔ 76, 73 ↔ 70, 97 ↔ 90. The first is 67, before 73. -/
theorem prime_crossings :
    (List.range 100).filter (fun n => crossP n) = [67, 73, 97] := by decide +kernel

/-- Of all two-digit crossings, exactly one is a digit mirror: 67 ↔ 76. -/
theorem crossing_digit_mirror :
    (List.range 100).filter (fun n => (crossP n ∨ crossC n) ∧ blockMirror 11 n = rev2 10 n) = [67] := by
  decide +kernel

end DigitMirror
