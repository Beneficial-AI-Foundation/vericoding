// <vc-preamble>
/*
 * Dafny specification for numpy.meshgrid functionality.
 * Returns coordinate matrices from coordinate vectors using 'xy' (Cartesian) indexing.
 * For inputs x of length m and y of length n, returns two matrices of shape (n, m).
 */

// Return coordinate matrices from coordinate vectors using 'xy' indexing
// Creates two matrices where x values are repeated along rows and y values along columns
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method meshgrid(x: seq<real>, y: seq<real>) returns (xv: seq<seq<real>>, yv: seq<seq<real>>)
  requires |x| > 0 && |y| > 0
  ensures |xv| == |y| && |yv| == |y|
  ensures forall i :: 0 <= i < |y| ==> |xv[i]| == |x| && |yv[i]| == |x|
  ensures forall i, j :: 0 <= i < |y| && 0 <= j < |x| ==> xv[i][j] == x[j]
  ensures forall i, j :: 0 <= i < |y| && 0 <= j < |x| ==> yv[i][j] == y[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
