import Mathlib
import MirrorNumbersAll.TwoMirrors
import MirrorNumbersAll.RatioTwoLine

/-!
# The unified code, levels, faces, the picture rule, the octave sum (tUrUq, 11-26-2026)

New module for the combined library. It closes the checked-to-N claims of the paper that are
general exact statements about the code itself:

* `levels b d n`  : the build with block rule `b` carried `d` levels down (comma count = d).
  `blocks2 n = [n/2, n%2, n/2]` is the unified code w,c,w; `blocks3` is the ternary (turn) build.
* `levels_sum`    : every level holds exactly n units (both builds, every depth, every n).
* `levels_reverse`: every level reads the same from either wing.
* `levels_length` : every level is 3^d wide, so the zeros are 3^d - n: the zeros carry the scale.
* `levels_inj`    : each number has its own string.
* `levels_succ`, `levels_succ_step` : one level deeper is one order of the rewrite 0 -> 000, 1 -> 010
  once the string is in digits.
* `step_sum`, `step_reverse`, `step_length` : the rewrite keeps the units and the mirror, triples the width.
* `words2`, `words3`, `order_one_words` : the four words 000, 010, 101, 111 and their order-1 forms.
* `centre_eq_parity` : the ternary build's centre is a unit exactly when n is odd.
* `read` and the picture rule b + (s-1) a : halving (s = 2) and turn (s = 3) forms read exactly n.
* `wing_two_primes` : three primes b, b+2, b+4 force b = 3 (the one wing-2 picture of three primes).
* `unitProd` and the three faces: add, copies, product (bare units 1,|1|,1 = 3; 1,|p|,1 = p), reflection.
* `mark` : |^ across k steps is x (b^k + 1); digits 1,2,1 and 1,3,3,1 of its square and cube.
* `u_8k1` .. `u_8k7` : the class-by-8 weights (14,1), (16,4), (12,8), (8,12) on (u k, u (k+1)).
* `u_eleven_pow`, `u_thirtythree_pow` : u(11 2^j) = 20 2^j and u(33 2^j) = 63 2^j.
* `S_succ`, `octave_sum` : S(k+1) = 5 S(k) + 2^k and 3 S(k) + 2^k = 17 5^(k-1) for k >= 1,
  i.e. S(k) = (17 5^k - 5 2^k)/15: the binary drift of 5 against 4 per octave.
No sorry, no admit, no native_decide.
-/

namespace UnifiedCode

/-! ## 1. List helpers -/

theorem flatMap_sum_of (f : ℕ → List ℕ) (hf : ∀ m, (f m).sum = m) (l : List ℕ) :
    (l.flatMap f).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.sum_append, hf, ih, List.sum_cons]

theorem flatMap_length_of (f : ℕ → List ℕ) (c : ℕ) (hf : ∀ m, (f m).length = c) (l : List ℕ) :
    (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.length_append, hf, ih, List.length_cons]; ring

theorem reverse_flatMap' (l : List ℕ) (f : ℕ → List ℕ) :
    (l.flatMap f).reverse = l.reverse.flatMap (fun x => (f x).reverse) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatMap_append, List.reverse_append, ih]

theorem flatMap_flatMap (l : List ℕ) (f g : ℕ → List ℕ) :
    (l.flatMap f).flatMap g = l.flatMap fun x => (f x).flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatMap_append, ih]

theorem flatMap_congr' (l : List ℕ) (f g : ℕ → List ℕ) (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-! ## 2. Levels of a build -/

/-- The build with block rule `b`, carried `d` levels down. Level 0 is the number itself. -/
def levels (b : ℕ → List ℕ) : ℕ → ℕ → List ℕ
  | 0, n => [n]
  | d + 1, n => (b n).flatMap (levels b d)

/-- The unified code: w, c, w with w = n/2 and c = n%2 (0 the hinge, 1 the unit). -/
def blocks2 (n : ℕ) : List ℕ := [n / 2, n % 2, n / 2]

/-- The ternary (turn) build: n = 3k + r as k,k,k / k,k+1,k / k+1,k,k+1. -/
def blocks3 (n : ℕ) : List ℕ :=
  if n % 3 = 0 then [n / 3, n / 3, n / 3]
  else if n % 3 = 1 then [n / 3, n / 3 + 1, n / 3]
  else [n / 3 + 1, n / 3, n / 3 + 1]

theorem blocks2_sum (n : ℕ) : (blocks2 n).sum = n := by
  simp only [blocks2, List.sum_cons, List.sum_nil]; omega
theorem blocks2_reverse (n : ℕ) : (blocks2 n).reverse = blocks2 n := by simp [blocks2]
theorem blocks2_length (n : ℕ) : (blocks2 n).length = 3 := rfl
theorem blocks3_sum (n : ℕ) : (blocks3 n).sum = n := by
  unfold blocks3; split_ifs <;> simp only [List.sum_cons, List.sum_nil] <;> omega
theorem blocks3_reverse (n : ℕ) : (blocks3 n).reverse = blocks3 n := by
  unfold blocks3; split_ifs <;> simp
theorem blocks3_length (n : ℕ) : (blocks3 n).length = 3 := by
  unfold blocks3; split_ifs <;> rfl

/-- EVERY LEVEL HOLDS EXACTLY n UNITS (for any block rule whose blocks add to n). -/
theorem levels_sum (b : ℕ → List ℕ) (hb : ∀ n, (b n).sum = n) (d : ℕ) :
    ∀ n, (levels b d n).sum = n := by
  induction d with
  | zero => intro n; simp [levels]
  | succ d ih => intro n; rw [levels, flatMap_sum_of _ ih, hb]

/-- Every level reads the same from either wing. -/
theorem levels_reverse (b : ℕ → List ℕ) (hb : ∀ n, (b n).reverse = b n) (d : ℕ) :
    ∀ n, (levels b d n).reverse = levels b d n := by
  induction d with
  | zero => intro n; simp [levels]
  | succ d ih =>
    intro n
    rw [levels, reverse_flatMap']
    simp only [ih]
    rw [hb]

/-- Every level is 3^d wide: the zeros are 3^d - n. -/
theorem levels_length (b : ℕ → List ℕ) (hb : ∀ n, (b n).length = 3) (d : ℕ) :
    ∀ n, (levels b d n).length = 3 ^ d := by
  induction d with
  | zero => intro n; simp [levels]
  | succ d ih => intro n; rw [levels, flatMap_length_of _ _ ih, hb]; ring

/-- Each number has its own string. -/
theorem levels_inj (b : ℕ → List ℕ) (hb : ∀ n, (b n).sum = n) (d m n : ℕ)
    (h : levels b d m = levels b d n) : m = n := by
  have h1 := levels_sum b hb d m
  rw [h, levels_sum b hb d n] at h1
  exact h1.symm

/-- One level deeper is the leaves expanded once. -/
theorem levels_succ (b : ℕ → List ℕ) (d : ℕ) :
    ∀ n, levels b (d + 1) n = (levels b d n).flatMap (levels b 1) := by
  induction d with
  | zero =>
    intro n
    show (b n).flatMap (levels b 0) = [n].flatMap (fun m => (b m).flatMap (levels b 0))
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | succ d ih =>
    intro n
    have hf : levels b (d + 1) = fun m => (levels b d m).flatMap (levels b 1) := funext ih
    show (b n).flatMap (levels b (d + 1)) = ((b n).flatMap (levels b d)).flatMap (levels b 1)
    rw [hf, flatMap_flatMap]

/-- The unified code, every level. -/
theorem code_sum (d n : ℕ) : (levels blocks2 d n).sum = n := levels_sum blocks2 blocks2_sum d n
theorem code_reverse (d n : ℕ) : (levels blocks2 d n).reverse = levels blocks2 d n :=
  levels_reverse blocks2 blocks2_reverse d n
theorem code_length (d n : ℕ) : (levels blocks2 d n).length = 3 ^ d :=
  levels_length blocks2 blocks2_length d n

/-- The ternary build, every level: exactly n units, no excess, a mirror, 3^d wide. -/
theorem tern_sum (d n : ℕ) : (levels blocks3 d n).sum = n := levels_sum blocks3 blocks3_sum d n
theorem tern_reverse (d n : ℕ) : (levels blocks3 d n).reverse = levels blocks3 d n :=
  levels_reverse blocks3 blocks3_reverse d n
theorem tern_length (d n : ℕ) : (levels blocks3 d n).length = 3 ^ d :=
  levels_length blocks3 blocks3_length d n

/-- The four words at level one, both builds. -/
theorem words2 : levels blocks2 1 0 = [0, 0, 0] ∧ levels blocks2 1 1 = [0, 1, 0] ∧
    levels blocks2 1 2 = [1, 0, 1] ∧ levels blocks2 1 3 = [1, 1, 1] := by decide
theorem words3 : levels blocks3 1 0 = [0, 0, 0] ∧ levels blocks3 1 1 = [0, 1, 0] ∧
    levels blocks3 1 2 = [1, 0, 1] ∧ levels blocks3 1 3 = [1, 1, 1] := by decide

/-- Level two of the ternary build is exactly the order-1 words. -/
theorem order_one_words :
    levels blocks3 2 0 = [0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    levels blocks3 2 1 = [0, 0, 0, 0, 1, 0, 0, 0, 0] ∧
    levels blocks3 2 2 = [0, 1, 0, 0, 0, 0, 0, 1, 0] ∧
    levels blocks3 2 3 = [0, 1, 0, 0, 1, 0, 0, 1, 0] := by decide

/-- The paper's examples: 8 = 4,0,4 -> 2,0,2,,0,0,0,,2,0,2; 7 = 3,1,3 -> 1,1,1,,0,1,0,,1,1,1; 11 = 5,1,5. -/
theorem code_examples : levels blocks2 1 8 = [4, 0, 4] ∧
    levels blocks2 2 8 = [2, 0, 2, 0, 0, 0, 2, 0, 2] ∧
    levels blocks2 1 7 = [3, 1, 3] ∧
    levels blocks2 2 7 = [1, 1, 1, 0, 1, 0, 1, 1, 1] ∧
    levels blocks2 1 11 = [5, 1, 5] := by decide

/-! ## 3. Orders: the rewrite 0 -> 000, 1 -> 010 -/

/-- One order, applied to every digit at once. -/
def step (l : List ℕ) : List ℕ := l.flatMap (fun d => if d = 0 then [0, 0, 0] else [0, 1, 0])

theorem step_append (l₁ l₂ : List ℕ) : step (l₁ ++ l₂) = step l₁ ++ step l₂ := by
  simp [step, List.flatMap_append]

/-- Across orders the units stay fixed. -/
theorem step_sum (l : List ℕ) (h : ∀ d ∈ l, d ≤ 1) : (step l).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    have hd : d ≤ 1 := h d (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    unfold step at ih' ⊢
    rw [List.flatMap_cons, List.sum_append, ih', List.sum_cons]
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> simp

/-- The length triples per order. -/
theorem step_length (l : List ℕ) : (step l).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    unfold step at ih ⊢
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    split_ifs <;> simp <;> omega

/-- The mirror is kept: the rewrite of a mirror is a mirror. -/
theorem step_reverse (l : List ℕ) : (step l).reverse = step l.reverse := by
  unfold step
  rw [reverse_flatMap']
  congr 1
  funext x
  split_ifs <;> rfl

/-- The rewrite is the level-one build of each digit (both builds agree on 0 and 1). -/
theorem step_eq_level (b : ℕ → List ℕ) (h0 : b 0 = [0, 0, 0]) (h1 : b 1 = [0, 1, 0])
    (l : List ℕ) (h : ∀ d ∈ l, d ≤ 1) : step l = l.flatMap (levels b 1) := by
  unfold step
  apply flatMap_congr'
  intro x hx
  have := h x hx
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
  · show (if (0 : ℕ) = 0 then [0, 0, 0] else [0, 1, 0]) = (b 0).flatMap (levels b 0)
    rw [h0]; rfl
  · show (if (1 : ℕ) = 0 then [0, 0, 0] else [0, 1, 0]) = (b 1).flatMap (levels b 0)
    rw [h1]; rfl

/-- BUILDING ONE LEVEL DEEPER IS ONE ORDER OF THE REWRITE, once the string is in digits. -/
theorem levels_succ_step (b : ℕ → List ℕ) (h0 : b 0 = [0, 0, 0]) (h1 : b 1 = [0, 1, 0]) (d n : ℕ)
    (hd : ∀ x ∈ levels b d n, x ≤ 1) : levels b (d + 1) n = step (levels b d n) := by
  rw [levels_succ, step_eq_level b h0 h1 _ hd]

theorem blocks2_zero : blocks2 0 = [0, 0, 0] := rfl
theorem blocks2_one : blocks2 1 = [0, 1, 0] := rfl
theorem blocks3_zero : blocks3 0 = [0, 0, 0] := rfl
theorem blocks3_one : blocks3 1 = [0, 1, 0] := rfl

/-- The order of a digit string keeps its unit count and its mirror (the rewrite on the build). -/
theorem order_keeps_units (d n : ℕ) (hd : ∀ x ∈ levels blocks2 d n, x ≤ 1) :
    (step (levels blocks2 d n)).sum = n := by
  rw [step_sum _ hd, code_sum]

/-! ## 4. The centre of the ternary build -/

/-- The centre block of the ternary build, followed down: the unit or the hinge. -/
def centre : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => if (n + 2) % 3 = 1 then centre ((n + 2) / 3 + 1) else centre ((n + 2) / 3)
  decreasing_by all_goals omega

/-- A centre unit appears exactly when n is odd. -/
theorem centre_eq_parity (n : ℕ) : centre n = n % 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp [centre]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [centre]
      have h1 := ih ((m + 2) / 3) (by omega)
      have h2 := ih ((m + 2) / 3 + 1) (by omega)
      split_ifs <;> omega

/-! ## 5. One picture, three readings -/

/-- A picture a,b,a read at scale s: b + (s-1) a, with the halving convention a,0,a:2 = 2a. -/
def read (a b s : ℕ) : ℕ := if b = 0 ∧ s = 2 then 2 * a else b + (s - 1) * a

/-- The halving (reflection) forms read exactly n. -/
theorem read_halving_odd (k : ℕ) : read k (k + 1) 2 = 2 * k + 1 := by
  unfold read; rw [if_neg (by omega)]; norm_num <;> omega
theorem read_halving_even (k : ℕ) : read k 0 2 = 2 * k := by
  unfold read; rw [if_pos ⟨rfl, rfl⟩]

/-- The turn (thirding) forms read exactly n. -/
theorem read_turn (k : ℕ) :
    read k k 3 = 3 * k ∧ read k (k + 1) 3 = 3 * k + 1 ∧ read (k + 1) k 3 = 3 * k + 2 := by
  unfold read; refine ⟨?_, ?_, ?_⟩ <;> rw [if_neg (by omega)] <;> norm_num <;> omega

/-- Scale 1 is the centre alone. -/
theorem read_one (a b : ℕ) (hb : 1 ≤ b) : read a b 1 = b := by
  unfold read; rw [if_neg (by omega)]; simp

/-- One picture read at scales t+1, t+2 steps by one wing (filled centre). -/
theorem read_step (a b t : ℕ) (hb : 1 ≤ b) : read a b (t + 2) = read a b (t + 1) + a := by
  unfold read
  have h1 : ¬ (b = 0 ∧ t + 2 = 2) := by omega
  have h2 : ¬ (b = 0 ∧ t + 1 = 2) := by omega
  rw [if_neg h1, if_neg h2, show t + 2 - 1 = t + 1 by omega, show t + 1 - 1 = t by omega]
  ring

/-- 1,1,1 -> 1,2,3; 2,3,2 -> 3,5,7; 9,9,9 -> 9,18,27. -/
theorem read_examples :
    (read 1 1 1 = 1 ∧ read 1 1 2 = 2 ∧ read 1 1 3 = 3) ∧
    (read 2 3 1 = 3 ∧ read 2 3 2 = 5 ∧ read 2 3 3 = 7) ∧
    (read 9 9 1 = 9 ∧ read 9 9 2 = 18 ∧ read 9 9 3 = 27) := by decide

/-- Three primes b, b+2, b+4 (a wing-2 picture at scales 1, 2, 3) force b = 3: one of three steps of 2
is a multiple of 3, and a prime multiple of 3 is 3. -/
theorem wing_two_primes (b : ℕ) (h0 : b.Prime) (h2 : (b + 2).Prime) (h4 : (b + 4).Prime) : b = 3 := by
  have key : ∀ m, m.Prime → 3 ∣ m → m = 3 := fun m hm hd =>
    (((Nat.dvd_prime hm).1 hd).resolve_left (by norm_num)).symm
  rcases (by omega : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2) with h | h | h
  · exact key b h0 (Nat.dvd_of_mod_eq_zero h)
  · have := key (b + 2) h2 (Nat.dvd_of_mod_eq_zero (by omega))
    have hb : b = 1 := by omega
    subst hb
    exact absurd h0 Nat.not_prime_one
  · have := key (b + 4) h4 (Nat.dvd_of_mod_eq_zero (by omega))
    omega

/-! ## 6. Three faces in one code -/

/-- The counting rule on a product face: bare units are counted, otherwise the factors multiply. -/
def unitProd (l : List ℕ) : ℕ := if l.all (· = 1) then l.length else l.prod

/-- The add face w,c,w. -/
theorem face_add (n : ℕ) : n / 2 + n % 2 + n / 2 = n := by omega

/-- The copies face m,m,...,m (d copies). -/
theorem face_copies (d m : ℕ) : (List.replicate d m).sum = d * m := by simp

/-- The product face a,|b|,c when a factor holds the unit. -/
theorem face_product (a b c : ℕ) (h : ¬ (a = 1 ∧ b = 1 ∧ c = 1)) :
    unitProd [a, b, c] = a * b * c := by
  unfold unitProd
  split_ifs with hc
  · exfalso; apply h; simpa using hc
  · simp [mul_assoc]

/-- Bare units: 1,|1|,1 = 1 x 1 x 1 = 3. -/
theorem face_bare_units : unitProd [1, 1, 1] = 3 := by decide

/-- A prime's product face is the one around the unit: 1,|p|,1 = p. -/
theorem face_prime (p : ℕ) (hp : p ≠ 1) : unitProd [1, p, 1] = p := by
  unfold unitProd
  split_ifs with hc
  · exfalso; simp at hc; omega
  · simp

/-- The reflection face: centre plus one wing for odd n, wing plus wing for a hinge. -/
theorem face_reflection_odd (k : ℕ) : (k + 1) + k = 2 * k + 1 := by ring
theorem face_reflection_even (w : ℕ) : w + w = 2 * w := by ring

/-- The paper's 18: 9,0,9 = 6,6,6 = 2,|3|,3 = |9,0|,|9. -/
theorem eighteen_faces : 9 + 0 + 9 = 18 ∧ (List.replicate 3 6).sum = 18 ∧
    unitProd [2, 3, 3] = 18 ∧ 9 + 9 = 18 := by decide

/-! ## 7. The mark |^ -/

/-- |^ across k scale steps in base b: x mirrored, both kept, x (b^k + 1). -/
def mark (b k x : ℕ) : ℕ := x * (b ^ k + 1)

theorem mark_base_two (k : ℕ) : mark 2 k 1 = 2 ^ k + 1 := by simp [mark]

theorem mark_examples : mark 10 1 1 = 11 ∧ mark 10 2 1 = 101 ∧ mark 10 1 5 = 55 ∧
    mark 2 1 1 = 3 ∧ mark 2 2 1 = 5 ∧ mark 2 3 1 = 9 ∧ mark 2 4 1 = 17 ∧ mark 2 5 1 = 33 := by decide

/-- (|^1)^2 has the digits 1,2,1 in every base b >= 3. -/
theorem mark_sq_digits (b : ℕ) (hb : 3 ≤ b) : Nat.digits b ((b + 1) ^ 2) = [1, 2, 1] := by
  have h : (b + 1) ^ 2 = Nat.ofDigits b [1, 2, 1] := by
    simp [Nat.ofDigits]; ring
  rw [h]
  apply Nat.digits_ofDigits b (by omega)
  · intro l hl; simp at hl; omega
  · intro _; simp

/-- (|^1)^3 has the digits 1,3,3,1 in every base b >= 4. -/
theorem mark_cube_digits (b : ℕ) (hb : 4 ≤ b) : Nat.digits b ((b + 1) ^ 3) = [1, 3, 3, 1] := by
  have h : (b + 1) ^ 3 = Nat.ofDigits b [1, 3, 3, 1] := by
    simp [Nat.ofDigits]; ring
  rw [h]
  apply Nat.digits_ofDigits b (by omega)
  · intro l hl; simp at hl; omega
  · intro _; simp

/-- 9 = 3^2 is 1,2,1 in base 2; 121 = 11^2 and 1331 = 11^3 in base 10. -/
theorem mark_nine : (2 + 1) ^ 2 = 9 ∧ Nat.digits 2 9 = [1, 0, 0, 1] ∧
    Nat.digits 10 121 = [1, 2, 1] ∧ Nat.digits 10 1331 = [1, 3, 3, 1] := by norm_num

/-! ## 8. The class-by-8 weights of u -/

open TwoMirrors in
theorem u_8k1 (k : ℕ) (hk : 2 ≤ k) : u (8 * k + 1) = 14 * u k + u (k + 1) := by
  rw [show 8 * k + 1 = 2 * (4 * k) + 1 by ring, u_odd (4 * k) (by omega),
    show 4 * k = 2 * (2 * k) by ring, u_even (2 * k) (by omega), u_odd (2 * k) (by omega),
    u_even k (by omega), u_odd k hk]
  ring

open TwoMirrors in
theorem u_8k3 (k : ℕ) (hk : 2 ≤ k) : u (8 * k + 3) = 16 * u k + 4 * u (k + 1) := by
  rw [show 8 * k + 3 = 2 * (4 * k + 1) + 1 by ring, u_odd (4 * k + 1) (by omega),
    show 4 * k + 1 + 1 = 2 * (2 * k + 1) by ring, u_even (2 * k + 1) (by omega),
    show 4 * k + 1 = 2 * (2 * k) + 1 by ring, u_odd (2 * k) (by omega),
    u_even k (by omega), u_odd k hk]
  ring

open TwoMirrors in
theorem u_8k5 (k : ℕ) (hk : 2 ≤ k) : u (8 * k + 5) = 12 * u k + 8 * u (k + 1) := by
  rw [show 8 * k + 5 = 2 * (4 * k + 2) + 1 by ring, u_odd (4 * k + 2) (by omega),
    show 4 * k + 2 + 1 = 2 * (2 * k + 1) + 1 by ring, u_odd (2 * k + 1) (by omega),
    show 2 * k + 1 + 1 = 2 * (k + 1) by ring, u_even (k + 1) (by omega),
    show 4 * k + 2 = 2 * (2 * k + 1) by ring, u_even (2 * k + 1) (by omega), u_odd k hk]
  ring

open TwoMirrors in
theorem u_8k7 (k : ℕ) (hk : 2 ≤ k) : u (8 * k + 7) = 8 * u k + 12 * u (k + 1) := by
  rw [show 8 * k + 7 = 2 * (4 * k + 3) + 1 by ring, u_odd (4 * k + 3) (by omega),
    show 4 * k + 3 + 1 = 2 * (2 * (k + 1)) by ring, u_even (2 * (k + 1)) (by omega),
    show 4 * k + 3 = 2 * (2 * k + 1) + 1 by ring, u_odd (2 * k + 1) (by omega),
    show 2 * k + 1 + 1 = 2 * (k + 1) by ring, u_even (k + 1) (by omega), u_odd k hk]
  ring

/-! ## 9. Values and the 11-strands -/

open TwoMirrors in
theorem u5 : u 5 = 7 := by
  have := u_odd 2 le_rfl; norm_num at this; exact this
open TwoMirrors in
theorem u6 : u 6 = 6 := by
  have := u_even 3 (by norm_num); norm_num at this; exact this
open TwoMirrors in
theorem u7 : u 7 = 10 := by
  have := u_odd 3 (by norm_num); norm_num at this; exact this
open TwoMirrors in
theorem u8 : u 8 = 8 := by
  have := u_even 4 (by norm_num); norm_num at this; exact this
open TwoMirrors in
theorem u11 : u 11 = 20 := by
  have := u_odd 5 (by norm_num); norm_num [u5, u6] at this; exact this
open TwoMirrors in
theorem u15 : u 15 = 28 := by
  have := u_odd 7 (by norm_num); norm_num [u7, u8] at this; exact this
open TwoMirrors in
theorem u16 : u 16 = 16 := by
  have := u_pow 4; norm_num at this; exact this
open TwoMirrors in
theorem u17 : u 17 = 31 := by
  have := u_pow_add_one 4 (by norm_num); norm_num at this; exact this
open TwoMirrors in
theorem u33 : u 33 = 63 := by
  have := u_odd 16 (by norm_num); norm_num [u16, u17] at this; exact this

open TwoMirrors in
/-- u(n)/n is exactly 20/11 on 11 2^j and 21/11 on 33 2^j. -/
theorem u_eleven_pow (j : ℕ) : u (11 * 2 ^ j) = 20 * 2 ^ j := by
  induction j with
  | zero => simpa using u11
  | succ j ih =>
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    rw [show 11 * 2 ^ (j + 1) = 2 * (11 * 2 ^ j) by ring, u_even _ (by omega), ih]; ring

open TwoMirrors in
theorem u_thirtythree_pow (j : ℕ) : u (33 * 2 ^ j) = 63 * 2 ^ j := by
  induction j with
  | zero => simpa using u33
  | succ j ih =>
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    rw [show 33 * 2 ^ (j + 1) = 2 * (33 * 2 ^ j) by ring, u_even _ (by omega), ih]; ring

/-! ## 10. The octave sum -/

open TwoMirrors

/-- The units of the octave [2^k, 2^(k+1)). -/
def S (k : ℕ) : ℕ := ∑ i ∈ Finset.range (2 ^ k), u (2 ^ k + i)

theorem sum_range_two_mul (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- THE OCTAVE RECURSION: S(k+1) = 5 S(k) + 2^k for k >= 1 (five against four: the binary drift). -/
theorem S_succ (k : ℕ) (hk : 1 ≤ k) : S (k + 1) = 5 * S k + 2 ^ k := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  unfold S
  rw [pow_succ, mul_comm (2 ^ k) 2, sum_range_two_mul]
  have h1 : ∀ i ∈ Finset.range (2 ^ k),
      u (2 * 2 ^ k + 2 * i) + u (2 * 2 ^ k + (2 * i + 1)) = 4 * u (2 ^ k + i) + u (2 ^ k + (i + 1)) := by
    intro i _
    rw [show 2 * 2 ^ k + (2 * i + 1) = 2 * (2 ^ k + i) + 1 by ring,
      show 2 * 2 ^ k + 2 * i = 2 * (2 ^ k + i) by ring, u_even _ (by omega), u_odd _ (by omega),
      show 2 ^ k + i + 1 = 2 ^ k + (i + 1) by ring]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have e1 := Finset.sum_range_succ' (fun i => u (2 ^ k + i)) (2 ^ k)
  have e2 := Finset.sum_range_succ (fun i => u (2 ^ k + i)) (2 ^ k)
  rw [add_zero, u_pow] at e1
  rw [show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring, u_pow, pow_succ] at e2
  omega

/-- THE OCTAVE SUM: 3 S(k) + 2^k = 17 5^(k-1) for k >= 1, i.e. S(k) = (17 5^k - 5 2^k) / 15. -/
theorem octave_sum (j : ℕ) : 3 * S (j + 1) + 2 ^ (j + 1) = 17 * 5 ^ j := by
  induction j with
  | zero => simp [S, Finset.sum_range_succ]
  | succ j ih =>
    rw [S_succ (j + 1) (by omega), pow_succ 2 (j + 1), pow_succ 5 j]
    omega

theorem octave_sum' (j : ℕ) : 15 * S (j + 1) + 5 * 2 ^ (j + 1) = 17 * 5 ^ (j + 1) := by
  have := octave_sum j
  rw [pow_succ 5 j]
  omega

/-- The first octaves: S 1 = 5, S 2 = 27, S 3 = 139. -/
theorem octave_values : S 1 = 5 ∧ S 2 = 27 ∧ S 3 = 139 := by
  have a := octave_sum 0
  have b := octave_sum 1
  have c := octave_sum 2
  norm_num at a b c
  omega

end UnifiedCode
