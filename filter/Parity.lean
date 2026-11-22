import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace RHFilter

abbrev mu (n : ℕ) : ℤ := ArithmeticFunction.moebius n

/-- Inclusive partial sum over the positive integers. -/
def partialSum (a : ℕ → ℤ) (N : ℕ) : ℤ := ∑ i ∈ Finset.range N, a (i + 1)
def oddMu (n : ℕ) : ℤ := if n % 2 = 1 then mu n else 0
def pref := partialSum mu
def oddPref := partialSum oddMu
def grid (N : ℕ) : ℤ := -pref N + 5 * pref (N / 2) - 8 * pref (N / 4) + 4 * pref (N / 8)

theorem prefix_succ (a : ℕ → ℤ) (N : ℕ) :
    partialSum a (N+1) = partialSum a N + a (N+1) := Finset.sum_range_succ ..

theorem mu_two_mul (n : ℕ) : mu (2*n) = -oddMu n := by
  by_cases h : n % 2 = 1
  · have hn : Odd n := ⟨n/2, by omega⟩
    simp [mu, oddMu, h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      hn.coprime_two_left, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  · have hs : ¬Squarefree (2*n) := by
      intro hh
      have hc := (Nat.squarefree_mul_iff.mp hh).1
      have ho := Nat.coprime_two_left.mp hc
      obtain ⟨k,hk⟩ := ho
      omega
    simp [mu, oddMu, h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

theorem pref_eq_odd_sub_half (N : ℕ) : pref N = oddPref N - oddPref (N/2) := by
  induction N with
  | zero => simp [pref, oddPref, partialSum]
  | succ N ih =>
    change partialSum mu (N+1) = partialSum oddMu (N+1) - partialSum oddMu ((N+1)/2)
    rw [prefix_succ, prefix_succ]
    change pref N + mu (N+1) = oddPref N + oddMu (N+1) - oddPref ((N+1)/2)
    rw [ih]
    by_cases h : (N+1)%2 = 1
    · rw [show (N+1)/2 = N/2 by omega]
      simp [oddMu, h]
      ring
    · have hstep : oddPref ((N+1)/2) = oddPref (N/2) + oddMu ((N+1)/2) := by
        conv_lhs => rw [show (N+1)/2 = N/2+1 by omega]
        rw [show oddPref (N/2+1) = oddPref (N/2) + oddMu (N/2+1) from prefix_succ ..]
        congr 2
        omega
      have hm : mu (N+1) = -oddMu ((N+1)/2) := by
        convert mu_two_mul ((N+1)/2) using 1
        congr 1
        omega
      rw [hm, hstep, show oddMu (N+1) = 0 by simp [oddMu,h]]
      ring

theorem grid_eq_odd (N : ℕ) : grid N =
    -oddPref N + 6 * oddPref (N/2) - 13 * oddPref (N/4) +
    12 * oddPref (N/8) - 4 * oddPref (N/16) := by
  simp only [grid, pref_eq_odd_sub_half, Nat.div_div_eq_div_mul]
  norm_num
  ring

theorem grid_jump (N : ℕ) (h : 0 < N) : grid N - grid (N-1) =
    -mu N + 5*(if 2 ∣ N then mu (N/2) else 0) -
    8*(if 4 ∣ N then mu (N/4) else 0) + 4*(if 8 ∣ N then mu (N/8) else 0) := by
  have base : ∀ k : ℕ, 0 < k → pref k = pref (k-1) + mu k := by
    intro k hk
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact prefix_succ _ _
  have diff (k j : ℕ) (hkj : k = j+1) : pref k = pref j + mu k := by
    subst k
    exact prefix_succ _ _
  have part (d : ℕ) (hd : d=2 ∨ d=4 ∨ d=8) : pref (N/d) = pref ((N-1)/d) +
      (if d ∣ N then mu (N/d) else 0) := by
    rcases hd with rfl|rfl|rfl <;> split_ifs <;>
      first | apply diff; omega | simp only [add_zero]; congr 1; omega
  unfold grid
  linarith only [base N h,part 2 (by decide),part 4 (by decide),part 8 (by decide)]

end RHFilter
