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
/* code modified by LLM (iteration 5): Added invariant ensuring yv_rows rows have correct length to prove index bounds. */
{
  var i := 0;
  var xv_rows: seq<seq<real>> := [];
  var yv_rows: seq<seq<real>> := [];
  while i < |y|
    invariant 0 <= i <= |y|
    invariant |xv_rows| == i
    invariant |yv_rows| == i
    invariant forall k :: 0 <= k < i ==> |xv_rows[k]| == |x|
    invariant forall k :: 0 <= k < i ==> |yv_rows[k]| == |x|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |x| ==> xv_rows[k][j] == x[j]
    invariant forall k, j :: 0 <= k < i && 0 <= j < |x| ==> yv_rows[k][j] == y[k]
  {
    xv_rows := xv_rows + [x];
    yv_rows := yv_rows + [seq(|x|, j => y[i])];
    i := i + 1;
  }
  xv := xv_rows;
  yv := yv_rows;
}
// </vc-code>
