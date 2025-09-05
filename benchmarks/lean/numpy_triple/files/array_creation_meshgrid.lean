/- 
{
  "name": "numpy.meshgrid",
  "category": "Numerical ranges",
  "description": "Return a list of coordinate matrices from coordinate vectors",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.meshgrid.html",
  "doc": "\nReturn a list of coordinate matrices from coordinate vectors.\n\nParameters\n----------\nx1, x2,..., xn : array_like\n    1-D arrays representing the coordinates of a grid.\nindexing : {'xy', 'ij'}, optional\n    Cartesian ('xy', default) or matrix ('ij') indexing of output.\nsparse : bool, optional\n    If True the shape of the returned coordinate array for dimension i is reduced from \n    (N1, ..., Ni, ... Nn) to (1, ..., Ni, ..., 1). Default is False.\ncopy : bool, optional\n    If False, a view into the original arrays are returned in order to conserve memory. \n    Default is True.\n\nReturns\n-------\nX1, X2,..., XN : list of ndarray\n    For vectors x1, x2,..., xn with lengths Ni=len(xi), returns (N1, N2, N3,..., Nn) shaped arrays \n    if indexing='ij' or (N2, N1, N3,..., Nn) shaped arrays if indexing='xy' with the elements of xi \n    repeated to fill the matrix along the first dimension for x1, the second for x2 and so on.\n\nExamples\n--------\n>>> nx, ny = (3, 2)\n>>> x = np.linspace(0, 1, nx)\n>>> y = np.linspace(0, 1, ny)\n>>> xv, yv = np.meshgrid(x, y)\n>>> xv\narray([[0. , 0.5, 1. ],\n       [0. , 0.5, 1. ]])\n>>> yv\narray([[0.,  0.,  0.],\n       [1.,  1.,  1.]])\n\nNotes\n-----\nIn the 2-D case with inputs of length M and N, the outputs are of shape (N, M) for 'xy' \nindexing and (M, N) for 'ij' indexing.\n",
  "signature": "numpy.meshgrid(*xi, copy=True, sparse=False, indexing='xy')"
}
-/

/-  Return coordinate matrices from two coordinate vectors using 'xy' (Cartesian) indexing.
    For inputs of length m and n, returns two matrices of shape (n, m) where:
    - The first matrix has x values repeated along rows
    - The second matrix has y values repeated along columns -/

/-  Specification: meshgrid creates coordinate matrices where x values are repeated 
    along rows and y values are repeated along columns in 'xy' indexing mode -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def meshgrid {m n : Nat} (x : Vector Float m) (y : Vector Float n) : 
    Id (Vector (Vector Float m) n × Vector (Vector Float m) n) :=
  sorry

theorem meshgrid_spec {m n : Nat} (x : Vector Float m) (y : Vector Float n) :
    ⦃⌜True⌝⦄
    meshgrid x y
    ⦃⇓result => 
      let (xv, yv) := result
      ⌜-- First matrix: x values repeated along each row
       (∀ i : Fin n, ∀ j : Fin m, (xv.get i).get j = x.get j) ∧
       -- Second matrix: y values repeated along each column  
       (∀ i : Fin n, ∀ j : Fin m, (yv.get i).get j = y.get i)⌝⦄ := by
  sorry
