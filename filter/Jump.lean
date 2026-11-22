import Parity

namespace RHFilter

/-- Signed jump multiplier at an integer whose 2-adic valuation is r. -/
def jumpCoefficient : ℕ → ℤ
  | 0 => -1
  | 1 => 6
  | 2 => -13
  | 3 => 12
  | 4 => -4
  | _ => 0

private theorem mu_multiple_four (n : ℕ) (h : 4 ∣ n) : mu n = 0 := by
  obtain ⟨k,rfl⟩ := h
  rw [show 4*k = 2*(2*k) by omega, mu_two_mul]
  simp [oddMu, Nat.mul_mod_right]

private theorem jump_multiple_32 (k : ℕ) (hk : 0 < k) :
    grid (32*k) - grid (32*k-1) = 0 := by
  rw [grid_jump _ (by omega)]
  simp only [ite_eq_left (show 2 ∣ 32*k by omega), ite_eq_left (show 4 ∣ 32*k by omega),
    ite_eq_left (show 8 ∣ 32*k by omega)]
  rw [mu_multiple_four _ (by omega), mu_multiple_four ((32*k)/2) (by omega),
    mu_multiple_four ((32*k)/4) (by omega), mu_multiple_four ((32*k)/8) (by omega)]
  decide

theorem grid_jump_valuation (r m : ℕ) (hm : m % 2 = 1) :
    grid (2^r*m) - grid (2^r*m-1) = jumpCoefficient r * mu m := by
  have hmpos : 0 < m := by omega
  have h2 : mu (2*m) = -mu m := by simp only [mu_two_mul, oddMu, hm, ite_true]
  have h4 : mu (4*m) = 0 := mu_multiple_four _ (by omega)
  have h8 : mu (8*m) = 0 := mu_multiple_four _ (by omega)
  have h16 : mu (16*m) = 0 := mu_multiple_four _ (by omega)
  have hcase : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ 5≤r := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | hlarge
  · simp only [pow_zero, one_mul, jumpCoefficient]
    rw [grid_jump _ hmpos]
    simp [show ¬2 ∣ m by omega, show ¬4 ∣ m by omega, show ¬8 ∣ m by omega]
  · change grid (2*m) - grid (2*m-1) = 6 * mu m
    rw [grid_jump _ (by omega)]
    simp only [ite_eq_left (show 2 ∣ 2*m by omega), ite_eq_right (show ¬4 ∣ 2*m by omega),
      ite_eq_right (show ¬8 ∣ 2*m by omega), show (2*m)/2=m by omega, h2]
    ring
  · change grid (4*m) - grid (4*m-1) = -13 * mu m
    rw [grid_jump _ (by omega)]
    simp only [ite_eq_left (show 2 ∣ 4*m by omega), ite_eq_left (show 4 ∣ 4*m by omega),
      ite_eq_right (show ¬8 ∣ 4*m by omega), show (4*m)/2=2*m by omega,
      show (4*m)/4=m by omega, h4, h2]
    ring
  · change grid (8*m) - grid (8*m-1) = 12 * mu m
    rw [grid_jump _ (by omega)]
    simp only [ite_eq_left (show 2 ∣ 8*m by omega), ite_eq_left (show 4 ∣ 8*m by omega),
      ite_eq_left (show 8 ∣ 8*m by omega), show (8*m)/2=4*m by omega,
      show (8*m)/4=2*m by omega, show (8*m)/8=m by omega, h8, h4, h2]
    ring
  · change grid (16*m) - grid (16*m-1) = -4 * mu m
    rw [grid_jump _ (by omega)]
    simp only [ite_eq_left (show 2 ∣ 16*m by omega), ite_eq_left (show 4 ∣ 16*m by omega),
      ite_eq_left (show 8 ∣ 16*m by omega), show (16*m)/2=8*m by omega,
      show (16*m)/4=4*m by omega, show (16*m)/8=2*m by omega, h16, h8, h4, h2]
    ring
  · obtain ⟨k,rfl⟩ : ∃ k, r = k+5 := ⟨r-5, by omega⟩
    change grid (2^(k+5)*m) - grid (2^(k+5)*m-1) = 0 * mu m
    rw [show (2:ℕ)^(k+5)*m=32*(2^k*m) by rw [pow_add]; ring, zero_mul]
    apply jump_multiple_32
    exact Nat.mul_pos (Nat.pow_pos (by decide)) hmpos

end RHFilter
