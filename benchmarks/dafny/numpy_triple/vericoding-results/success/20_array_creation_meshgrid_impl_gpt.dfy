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
/* helper modified by LLM (iteration 2): replaced comprehension with recursive construction to avoid parser errors and ensure properties */
function constSeq(m: nat, v: real): seq<real>
  ensures |constSeq(m, v)| == m
  ensures forall j :: 0 <= j < m ==> constSeq(m, v)[j] == v
  decreases m
{
  if m == 0 then [] else constSeq(m - 1, v) + [v]
}
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
  /* code modified by LLM (iteration 2): build output matrices iteratively to satisfy ensures without using sequence comprehensions */
  xv := [];
  yv := [];
  var i := 0;
  while i < |y|
    invariant 0 <= i <= |y|
    invariant |xv| == i && |yv| == i
    invariant forall k :: 0 <= k < i ==> xv[k] == x
    invariant forall k :: 0 <= k < i ==> |xv[k]| == |x| && |yv[k]| == |x|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |x| ==> yv[k][j] == y[k]
  {
    xv := xv + [x];
    yv := yv + [constSeq(|x|, y[i])];
    i := i + 1;
  }
}
// </vc-code>
