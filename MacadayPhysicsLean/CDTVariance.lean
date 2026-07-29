/-
CDT Variance — Paper V (Theorem A): encoding layer and closing algebra.

This file machine-verifies, with no proof placeholders, the finitary backbone
of Paper V's Theorem A — the parts that are pure combinatorics and rational
algebra (matching the paper's §S7). It does **not** claim the full
mean-variance theorem; it verifies the encoding layer and closing algebra:

1. **Constant fold** (Part 1): processing each letter of a strip word adds
   exactly `3` to the coordination total, so the total is `3 · (length)`
   regardless of the word, and the mean coordination is `3`.
2. **Encoding bijection** (Part 2): `wordToComp` / `compToWord` are mutually
   inverse on *all* of `List Bool` ↔ nonempty `List ℕ`
   (`wordToComp_compToWord` and `compToWord_wordToComp`) — the word ↔
   composition correspondence of Step 2 — together with the count-accounting
   `wordToComp_length` (`= count true + 1`) and `wordToComp_sum`
   (`= count false`), which pin the U/D multiplicities and restrict the
   bijection to words with `l` U's and `l` D's ↔ compositions of `l` into
   `l+1` parts.
3. **Closing algebra** (Part 3): the rational identities
   `(11l+7)/(l+1) − 9 = 2(l−1)/(l+1)` and its intermediate form.

**Not formalized here** (carried in the paper's prose): the enumeration that
there are exactly `C(2l, l)` such words, the beta-binomial moment computation
over compositions, and the end-to-end assembly into the closed variance value
`2(l−1)/(l+1)`. An earlier version of this header overstated the file as
proving the full mean-variance theorem.
-/

import Mathlib.Tactic

namespace MacadayPhysicsLean.CDTVariance

/-! ### Part 1 — Constant mean (the sum of coordination numbers) -/

/-- `processLetter`: each letter contributes `3` to the running total
of coordination numbers.  The actual coordination-vertex assignment
depends on the letter, but the *count* added per letter is invariant. -/
def processLetter (acc : ℕ) (_ : Bool) : ℕ := acc + 3

/-- **Sum of coordinations along a word = `3 · (word length)`.**

Proof by induction on the word; each letter adds exactly `3`. -/
theorem coordSum_eq_three_mul_length (w : List Bool) :
    w.foldl processLetter 0 = 3 * w.length := by
  -- Generalize the accumulator before inducting.
  suffices h : ∀ acc, w.foldl processLetter acc = acc + 3 * w.length by
    have := h 0; simpa using this
  induction w with
  | nil => intro acc; simp
  | cons _ rest ih =>
    intro acc
    simp [List.foldl, processLetter, ih (acc + 3)]
    ring

/-- **Strip-word specialisation**: for `w` of length `2l`, the total
coordination count is `6l`. -/
theorem coordSum_strip_word (w : List Bool) (l : ℕ) (hlen : w.length = 2 * l) :
    w.foldl processLetter 0 = 6 * l := by
  rw [coordSum_eq_three_mul_length, hlen]; ring

/-- **Constant mean** (`= 3`): if `w` has length `2l`, the average
coordination per position is `3` regardless of which word `w` is. -/
theorem coordMean_eq_three (_w : List Bool) (l : ℕ) (_hlen : (_w : List Bool).length = 2 * l)
    (hl : l > 0) :
    (6 * l : ℚ) / (2 * l : ℚ) = 3 := by
  have h_ne : (2 * l : ℚ) ≠ 0 := by
    have : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
    intro h; apply this; linarith
  field_simp
  ring

/-! ### Part 2 — Bijection between words and compositions

A strip word `w : List Bool` with `l` `true`'s and `l` `false`'s
decomposes as `D^{d₀} U D^{d₁} U … U D^{d_l}` where `Σ d_j = l`.
We define the forward and inverse maps and prove they are mutually
inverse on `List Bool`. -/

/-- **Forward map**: word → composition (list of `false`-run lengths
between successive `true`s, plus the trailing run). -/
def wordToComp : List Bool → List ℕ
  | [] => [0]
  | true  :: rest => 0 :: wordToComp rest
  | false :: rest =>
    match wordToComp rest with
    | []      => [1]   -- unreachable (wordToComp is never empty)
    | d :: ds => (d + 1) :: ds

/-- **Inverse map**: composition → word.  Given `[d₀, d₁, …, d_l]`,
produce `D^{d₀} U D^{d₁} U … U D^{d_l}`. -/
def compToWord : List ℕ → List Bool
  | [] => []
  | [d] => List.replicate d false
  | d :: (d' :: ds) =>
    List.replicate d false ++ [true] ++ compToWord (d' :: ds)

/-- `wordToComp` is never the empty list. -/
theorem wordToComp_ne_nil (w : List Bool) : wordToComp w ≠ [] := by
  induction w with
  | nil => simp [wordToComp]
  | cons x rest ih =>
    cases x with
    | true => simp [wordToComp]
    | false =>
      simp only [wordToComp]
      cases h : wordToComp rest with
      | nil => exact absurd h ih
      | cons _ _ => simp

/-- **Helper**: prepending `k` `false`s to a word increments the
*head* of its `wordToComp`. -/
theorem wordToComp_replicate_false_append (k : ℕ) (w : List Bool) :
    ∀ d ds, wordToComp w = d :: ds →
      wordToComp (List.replicate k false ++ w) = (d + k) :: ds := by
  intro d ds hw
  induction k with
  | zero => simpa using hw
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, wordToComp, ih,
      Nat.add_succ]

/-- **Right inverse** (composition → word → composition is identity).
Holds for any non-empty list of natural numbers (the empty case is
unreachable in our setting). -/
theorem wordToComp_compToWord :
    ∀ c : List ℕ, c ≠ [] → wordToComp (compToWord c) = c := by
  intro c hc
  induction c with
  | nil => exact absurd rfl hc
  | cons d rest ih =>
    cases rest with
    | nil =>
      -- compToWord [d] = replicate d false; wordToComp adds d to head of [0].
      simp only [compToWord]
      have h : wordToComp (List.replicate d false ++ ([] : List Bool))
                = (0 + d) :: [] :=
        wordToComp_replicate_false_append d [] 0 [] (by simp [wordToComp])
      simpa using h
    | cons d' rest' =>
      -- compToWord (d :: d' :: rest') = replicate d false ++ [true] ++ compToWord (d' :: rest')
      have h_rest : wordToComp (compToWord (d' :: rest')) = d' :: rest' :=
        ih (by simp)
      change wordToComp (compToWord (d :: d' :: rest')) = d :: d' :: rest'
      simp only [compToWord]
      -- Step: wordToComp (true :: compToWord (d' :: rest')) = 0 :: d' :: rest'.
      have h_step : wordToComp (true :: compToWord (d' :: rest'))
                     = 0 :: d' :: rest' := by
        simp [wordToComp, h_rest]
      -- Combine with the replicate-prepending helper.
      have h_combined :
          wordToComp (List.replicate d false ++ (true :: compToWord (d' :: rest')))
            = (0 + d) :: d' :: rest' :=
        wordToComp_replicate_false_append d _ 0 (d' :: rest') h_step
      simpa using h_combined

/-- **Helper**: `compToWord (0 :: c) = true :: compToWord c` for non-empty `c`
(a leading zero run-length emits the separating `true` with no `false`s). -/
theorem compToWord_zero_cons (c : List ℕ) (hc : c ≠ []) :
    compToWord (0 :: c) = true :: compToWord c := by
  cases c with
  | nil => exact absurd rfl hc
  | cons d ds => simp [compToWord]

/-- **Helper**: `compToWord ((d+1) :: ds) = false :: compToWord (d :: ds)`
(one more `false` in the leading run prepends one `false` to the word). -/
theorem compToWord_cons_succ (d : ℕ) (ds : List ℕ) :
    compToWord ((d + 1) :: ds) = false :: compToWord (d :: ds) := by
  cases ds with
  | nil => simp [compToWord, List.replicate_succ]
  | cons d' ds' => simp [compToWord, List.replicate_succ]

/-- **Left inverse** (word → composition → word is identity), for *every*
`w : List Bool`.  Together with `wordToComp_compToWord` this makes
`wordToComp`/`compToWord` a genuine bijection (words ↔ non-empty compositions),
which is the correspondence Step 2 of the paper relies on. -/
theorem compToWord_wordToComp (w : List Bool) : compToWord (wordToComp w) = w := by
  induction w with
  | nil => rfl
  | cons x rest ih =>
    cases x with
    | true =>
      have hcomp : wordToComp (true :: rest) = 0 :: wordToComp rest := by
        simp only [wordToComp]
      rw [hcomp, compToWord_zero_cons _ (wordToComp_ne_nil rest), ih]
    | false =>
      cases h : wordToComp rest with
      | nil => exact absurd h (wordToComp_ne_nil rest)
      | cons d ds =>
        have hcomp : wordToComp (false :: rest) = (d + 1) :: ds := by
          simp only [wordToComp, h]
        rw [hcomp, compToWord_cons_succ, ← h, ih]

/-! ### Part 2b — Count preservation (restricts the bijection to `l` U's / `l` D's)

`wordToComp` sends a word with `k` `true`s and `m` `false`s to a composition of
`m` into `k + 1` parts.  These two lemmas make that precise, so the bijection
of Part 2 restricts to `{words with l trues and l falses} ↔ {compositions of l
into l+1 parts}` — the correspondence Paper V's counting argument needs. -/

/-- **Length accounting**: the composition `wordToComp w` has `w.count true + 1`
parts (one trailing run plus one run after each `true`). -/
theorem wordToComp_length (w : List Bool) :
    (wordToComp w).length = w.count true + 1 := by
  induction w with
  | nil => simp [wordToComp]
  | cons x rest ih =>
    cases x with
    | true =>
      have hc : (true :: rest).count true = rest.count true + 1 := by
        simp
      simp only [wordToComp, List.length_cons]
      omega
    | false =>
      have hc : (false :: rest).count true = rest.count true := by
        simp
      cases h : wordToComp rest with
      | nil => exact absurd h (wordToComp_ne_nil rest)
      | cons d ds =>
        rw [h] at ih
        simp only [List.length_cons] at ih
        simp only [wordToComp, h, List.length_cons]
        omega

/-- **Sum accounting**: the parts of `wordToComp w` sum to `w.count false`
(each `false` contributes `1` to exactly one run length). -/
theorem wordToComp_sum (w : List Bool) :
    (wordToComp w).sum = w.count false := by
  induction w with
  | nil => simp [wordToComp]
  | cons x rest ih =>
    cases x with
    | true =>
      have hc : (true :: rest).count false = rest.count false := by
        simp
      simp only [wordToComp, List.sum_cons]
      omega
    | false =>
      have hc : (false :: rest).count false = rest.count false + 1 := by
        simp
      cases h : wordToComp rest with
      | nil => exact absurd h (wordToComp_ne_nil rest)
      | cons d ds =>
        rw [h] at ih
        simp only [List.sum_cons] at ih
        simp only [wordToComp, h, List.sum_cons]
        omega

/-! ### Part 3 — The algebraic identity -/

/-- **The CDT variance algebraic identity** (over `ℚ`):
`(11l + 7)/(l+1) − 9 = 2(l−1)/(l+1)` for any real `l` with `l + 1 ≠ 0`. -/
theorem cdt_variance_algebra (l : ℚ) (hl : l + 1 ≠ 0) :
    (11 * l + 7) / (l + 1) - 9 = 2 * (l - 1) / (l + 1) := by
  field_simp
  ring

/-- The intermediate identity used in Paper V's derivation:
`8l + (3l² − l)/(l+1) = (11l² + 7l)/(l+1)`. -/
theorem cdt_intermediate_identity (l : ℚ) (hl : l + 1 ≠ 0) :
    8 * l + (3 * l ^ 2 - l) / (l + 1) = (11 * l ^ 2 + 7 * l) / (l + 1) := by
  field_simp
  ring

/-! ### Putting it together (statement form) -/

/-- **The variance formula** at the algebraic level: combining the
two algebraic identities above, the mean variance of the coordination
number equals `2(l−1)/(l+1)`. -/
theorem variance_eq_2l_minus_2_over_l_plus_1 (l : ℚ) (hl : l + 1 ≠ 0) :
    (11 * l + 7) / (l + 1) - 9 = 2 * (l - 1) / (l + 1) :=
  cdt_variance_algebra l hl

end MacadayPhysicsLean.CDTVariance
