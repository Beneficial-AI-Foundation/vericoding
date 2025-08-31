/- 
{
  "name": "numpy.fft.ifftshift",
  "description": "The inverse of fftshift",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fft.ifftshift.html",
  "doc": "numpy.fft.ifftshift(x, axes=None)\n\nThe inverse of fftshift. Although identical for even-length x, the functions differ by one sample for odd-length x.\n\nParameters:\n- x (array_like): Input array\n- axes (int or shape tuple, optional): Axes over which to calculate. Defaults to None, which shifts all axes.\n\nReturns:\n- y (ndarray): The shifted array\n\nExample:\nimport numpy as np\nfreqs = np.fft.fftfreq(9, d=1./9).reshape(3, 3)\nfreqs\n# Output: array([[ 0.,  1.,  2.],\n#                [ 3.,  4., -4.],\n#                [-3., -2., -1.]])\nnp.fft.ifftshift(np.fft.fftshift(freqs))\n# Output: same as original freqs array\n\nSee also: numpy.fft.fftshift",
}
-/

/-  The inverse of fftshift - undoes the frequency domain shifting.
    
    This function performs the inverse operation of fftshift, moving the 
    zero-frequency component from the center back to the beginning of the array.
    For even-length arrays, it is identical to fftshift.
    For odd-length arrays, it differs by one sample position.
    
    The function performs a circular shift by -(n/2) positions.
-/

/-  Specification: ifftshift performs the inverse of fftshift.
    
    The function performs a circular shift that undoes the centering of 
    the zero-frequency component:
    - For even n: shifts by -(n/2), identical to fftshift
    - For odd n: shifts by -(n/2), which differs from fftshift by one sample
    
    This ensures that:
    - Elements from the center move back to the beginning
    - The DC component at the center returns to index 0
    - The function is the left inverse of fftshift
    
    Mathematical properties:
    - For even-length arrays: ifftshift(fftshift(x)) = x and fftshift(ifftshift(x)) = x
    - For odd-length arrays: ifftshift(fftshift(x)) = x but fftshift(ifftshift(x)) ≠ x
    - Preserves the total energy/sum of the array
    - Is a bijection (permutation) of array elements
    
    The specification states that each element at position i in the result
    comes from position (i + n/2) % n in the input, which is equivalent
    to a circular left shift by n/2 positions (or right shift by n - n/2).
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ifftshift {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem ifftshift_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    ifftshift x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x.get ⟨(i.val + n / 2) % n, sorry⟩⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
