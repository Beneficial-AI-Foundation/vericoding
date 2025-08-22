import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.histogramdd",
  "category": "Histograms",
  "description": "Compute the multidimensional histogram of some data",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.histogramdd.html",
  "doc": "numpy.histogramdd(sample, bins=10, range=None, density=None, weights=None)\n\nCompute the multidimensional histogram of some data.\n\nParameters\n----------\nsample : (N, D) array, or (N, D) list of arrays\n    The data to be histogrammed.\n    Note the unusual interpretation of sample when an array_like:\n    * When an array, each row is a coordinate in a D-dimensional space - such as histogramdd(np.array([p1, p2, p3])).\n    * When a list of arrays, each array is the list of values for single coordinate - such as histogramdd([X, Y, Z]).\nbins : sequence or int, optional\n    The bin specification:\n    * A sequence of arrays describing the monotonically increasing bin edges along each dimension.\n    * The number of bins for each dimension (nx, ny, ... =bins)\n    * The number of bins for all dimensions (nx=ny=...=bins).\nrange : sequence, optional\n    A sequence of length D, each an optional (lower, upper) tuple giving the outer bin edges to be used if the edges are not given explicitly in bins.\ndensity : bool, optional\n    If False, the default, returns the number of samples in each bin. If True, returns the probability density function at the bin.\nweights : (N,) array_like, optional\n    An array of values w_i weighing each sample (x_i, y_i, z_i, ...).\n\nReturns\n-------\nH : ndarray\n    The multidimensional histogram of sample x.\nedges : list\n    A list of D arrays describing the bin edges for each dimension.",
  "code": "# Implementation in numpy/lib/_histograms_impl.py\n@array_function_dispatch(_histogramdd_dispatcher)\ndef histogramdd(sample, bins=10, range=None, density=None, weights=None):\n    \"\"\"\n    Compute the multidimensional histogram of some data.\n    \"\"\"\n    \n    try:\n        # Sample is an ND-array.\n        N, D = sample.shape\n    except (AttributeError, ValueError):\n        # Sample is a sequence of 1D arrays.\n        sample = np.atleast_2d(sample).T\n        N, D = sample.shape\n    \n    nbin = np.empty(D, np.intp)\n    edges = D*[None]\n    dedges = D*[None]\n    if weights is not None:\n        weights = np.asarray(weights)\n    \n    try:\n        M = len(bins)\n        if M != D:\n            raise ValueError(\n                'The dimension of bins must be equal to the dimension of the '\n                ' sample x.')\n    except TypeError:\n        # bins is an integer\n        bins = D*[bins]\n    \n    # normalize the range argument\n    if range is None:\n        range = (None,) * D\n    elif len(range) != D:\n        raise ValueError('range argument must have one entry per dimension')\n    \n    # Create edge arrays\n    for i in _range(D):\n        if np.ndim(bins[i]) == 0:\n            if bins[i] < 1:\n                raise ValueError(\n                    f'\`bins[{i}]\` must be positive, when an integer')\n            smin, smax = _get_outer_edges(sample[:,i], range[i])\n            try:\n                n = operator.index(bins[i])\n            except TypeError as e:\n                raise TypeError(\n                    \"\`bins[{}]\` must be an integer, when a scalar\".format(i)\n                ) from e\n            \n            edges[i] = np.linspace(smin, smax, n + 1)\n        elif np.ndim(bins[i]) == 1:\n            edges[i] = np.asarray(bins[i])\n            if np.any(edges[i][:-1] > edges[i][1:]):\n                raise ValueError(\n                    f'\`bins[{i}]\` must be monotonically increasing, when an '\n                    f'array')\n        else:\n            raise ValueError(\n                f'\`bins[{i}]\` must be a scalar or 1d array')\n        \n        nbin[i] = len(edges[i]) - 1\n        dedges[i] = np.diff(edges[i])\n    \n    # Compute the bin number each sample falls into.\n    Ncount = tuple(\n        # avoid np.digitize to work around gh-11022\n        np.searchsorted(edges[i], sample[:, i], side='right')\n        for i in _range(D)\n    )\n    \n    # Using digitize, values that fall on an edge are put in the right bin.\n    # For the rightmost bin, we want values equal to the right edge to be\n    # counted in the last bin, and not as an outlier.\n    for i in _range(D):\n        # Find which points are on the rightmost edge.\n        on_edge = (sample[:, i] == edges[i][-1])\n        # Shift these points one bin to the left.\n        Ncount[i][on_edge] -= 1\n    \n    # Compute the sample indices in the flattened histogram.\n    # This raises an error if the array is too large.\n    xy = np.ravel_multi_index(Ncount, nbin)\n    \n    # Compute the number of repetitions in xy and assign it to the\n    # flattened histmat.\n    hist = np.bincount(xy, weights, minlength=nbin.prod())\n    \n    # Shape into a proper matrix\n    hist = hist.reshape(nbin)\n    \n    # This preserves the (bad) behavior observed in gh-7845, for now.\n    hist = hist.astype(float, casting='safe')\n    \n    # Remove outliers (indices 0 and -1 for each dimension).\n    core = D*(slice(1, -1),)\n    hist = hist[core]\n    \n    if density:\n        # calculate the probability density function\n        s = hist.sum()\n        for i in _range(D):\n            shape = [1]*D\n            shape[i] = nbin[i] - 2\n            hist = hist / dedges[i].reshape(shape)\n        hist /= s\n    \n    return hist, edges"
}
-/

/-- Compute the multidimensional histogram of some data.
    For simplicity, we focus on 2D histograms with fixed dimensions. -/
def histogramdd {n : Nat} (sample : Vector (Float × Float) n) (bins_x bins_y : Nat) : 
    Id (Vector (Vector Float bins_x) bins_y × Vector Float (bins_x + 1) × Vector Float (bins_y + 1)) :=
  sorry

/-- Specification: histogramdd computes a 2D histogram with correct bin counts and edges -/
theorem histogramdd_spec {n : Nat} (sample : Vector (Float × Float) n) (bins_x bins_y : Nat) 
    (h_bins_x_pos : bins_x > 0) (h_bins_y_pos : bins_y > 0) :
    ⦃⌜bins_x > 0 ∧ bins_y > 0⌝⦄
    histogramdd sample bins_x bins_y
    ⦃⇓result => 
      let (hist, edges_x, edges_y) := result
      ⌜-- The histogram has the correct dimensions
      (hist.toArray.size = bins_y) ∧
      (∀ i : Fin bins_y, (hist.get i).toArray.size = bins_x) ∧
      -- The edges have the correct sizes
      (edges_x.toArray.size = bins_x + 1) ∧
      (edges_y.toArray.size = bins_y + 1) ∧
      -- The edges are monotonically increasing
      (∀ i : Fin bins_x, edges_x.get ⟨i.val, by omega⟩ < edges_x.get ⟨i.val + 1, by omega⟩) ∧
      (∀ i : Fin bins_y, edges_y.get ⟨i.val, by omega⟩ < edges_y.get ⟨i.val + 1, by omega⟩) ∧
      -- The histogram counts are non-negative
      (∀ i : Fin bins_y, ∀ j : Fin bins_x, (hist.get i).get j ≥ 0) ∧
      -- Each sample point falls into exactly one bin
      (∀ p : Float × Float, p ∈ sample.toArray →
        ∃ i : Fin bins_y, ∃ j : Fin bins_x,
          edges_y.get ⟨i.val, by omega⟩ ≤ p.snd ∧ p.snd < edges_y.get ⟨i.val + 1, by omega⟩ ∧
          edges_x.get ⟨j.val, by omega⟩ ≤ p.fst ∧ p.fst < edges_x.get ⟨j.val + 1, by omega⟩)⌝⦄ := by
  sorry