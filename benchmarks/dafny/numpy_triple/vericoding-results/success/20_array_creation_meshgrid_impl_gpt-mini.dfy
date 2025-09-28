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
/* helper modified by LLM (iteration 5): return sequence of m copies of a value v */
function RepeatValue(v: real, m: int): seq<real>
  requires m >= 0
  decreases m
  ensures |RepeatValue(v, m)| == m
  ensures forall i :: 0 <= i < m ==> RepeatValue(v, m)[i] == v
{
  if m == 0 then [] else RepeatValue(v, m - 1) + [v]
}

/* helper modified by LLM (iteration 5): return sequence of n copies of row x */
function RepeatXRows(x: seq<real>, n: int): seq<seq<real>>
  requires n >= 0
  decreases n
  ensures |RepeatXRows(x, n)| == n
  ensures forall i :: 0 <= i < n ==> RepeatXRows(x, n)[i] == x
{
  if n == 0 then [] else RepeatXRows(x, n - 1) + [x]
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
  /* code modified by LLM (iteration 5): build xv and yv with explicit loops and invariants */
  var i := 0;
  xv := [];
  yv := [];
  while i < |y|
    invariant 0 <= i <= |y|
    invariant |xv| == i && |yv| == i
    invariant forall k :: 0 <= k < |xv| ==> |xv[k]| == |x|
    invariant forall k :: 0 <= k < |yv| ==> |yv[k]| == |x|
    invariant forall k, j :: 0 <= k < |xv| && 0 <= j < |x| ==> xv[k][j] == x[j]
    invariant forall k, j :: 0 <= k < |yv| && 0 <= j < |x| ==> yv[k][j] == y[k]
  {
    xv := xv + [x];
    var row := RepeatValue(y[i], |x|);
    yv := yv + [row];
    i := i + 1;
  }
}

// </vc-code>
