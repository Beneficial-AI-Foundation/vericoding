/-  numpy.fft.rfftfreq: Return the Discrete Fourier Transform sample frequencies for rfft.

    The function generates frequency bin centers in cycles per unit of sample spacing,
    with zero at the start. This is specifically designed for use with rfft and irfft.

    Parameters:
    - n: Window length (input size)
    - d: Sample spacing (defaults to 1.0)

    Returns:
    - f: Array of length n//2 + 1 containing sample frequencies

    The frequency calculation follows:
    - For any n: f = [0, 1, ..., n//2] / (d*n)
    - The result length is always n//2 + 1 (for both even and odd n)
-/

/-  Specification: numpy.fft.rfftfreq generates frequency sample points for rfft.

    The function returns a vector of frequencies from 0 to the Nyquist frequency.

    Precondition: n > 0 and d > 0 (positive sample spacing)
    Postcondition: 
    1. The result has length n//2 + 1
    2. The first element is always 0
    3. Each element i represents frequency i / (d * n)
    4. The last element is (n//2) / (d * n) (Nyquist frequency)
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_rfftfreq (n : Nat) (d : Float) (h : n > 0) : Id (Vector Float (n / 2 + 1)) :=
  sorry

theorem numpy_rfftfreq_spec (n : Nat) (d : Float) (h : n > 0) (hd : d > 0) :
    ⦃⌜n > 0 ∧ d > 0⌝⦄
    numpy_rfftfreq n d h
    ⦃⇓result => ⌜
      -- First element is always 0
      result.get ⟨0, by simp⟩ = 0 ∧
      -- Each element follows the frequency formula
      ∀ i : Fin (n / 2 + 1), result.get i = Float.ofNat i.val / (d * Float.ofNat n) ∧
      -- Last element is the Nyquist frequency
      result.get ⟨n / 2, by simp⟩ = Float.ofNat (n / 2) / (d * Float.ofNat n) ∧
      -- Monotonicity: frequencies are non-decreasing
      ∀ i j : Fin (n / 2 + 1), i.val ≤ j.val → result.get i ≤ result.get j
    ⌝⦄ := by
  sorry
