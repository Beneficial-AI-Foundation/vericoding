// <vc-preamble>
/* Matrix type definition: function from row,col indices to values */
type Matrix<T> = int -> int -> T

/* Get matrix element at position (i,j) */
function MatrixGet<T>(mat: Matrix<T>, i: int, j: int): T
{
    mat(i)(j)
}

/* Matrix size helper */
function MatrixSize(m: int, n: int): int
{
    m * n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma about indexing concatenation preserving prefix */
lemma SeqAppendPreservesPrefix<T>(s: seq<T>, v: T, k: int)
  requires 0 <= k < |s|
  ensures (s + [v])[k] == s[k]
{
  assert (s + [v])[k] == s[k];
}

// </vc-helpers>

// <vc-spec>
method Ravel(arr: Matrix<int>, m: int, n: int) returns (ret: seq<int>)
    requires m > 0 && n > 0
    ensures |ret| == m * n
    ensures forall i, j :: 0 <= i < m && 0 <= j < n && 0 <= i * n + j < |ret| ==> 
            ret[i * n + j] == MatrixGet(arr, i, j)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): row-major ravel using nested loops with safe bounds in invariants */
  ret := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |ret| == i * n
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> 0 <= ii * n + jj < |ret| && ret[ii * n + jj] == MatrixGet(arr, ii, jj)
    decreases m - i
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |ret| == i * n + j
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> 0 <= ii * n + jj < |ret| && ret[ii * n + jj] == MatrixGet(arr, ii, jj)
      invariant forall jj :: 0 <= jj < j ==> 0 <= i * n + jj < |ret| && ret[i * n + jj] == MatrixGet(arr, i, jj)
      decreases n - j
    {
      var v := MatrixGet(arr, i, j);
      var oldRet := ret;

      // Capture properties of oldRet from invariants before updating ret
      assert |oldRet| == i * n + j;
      assert forall ii0, jj0 :: 0 <= ii0 < i && 0 <= jj0 < n ==> 0 <= ii0 * n + jj0 < |oldRet| && oldRet[ii0 * n + jj0] == MatrixGet(arr, ii0, jj0);
      assert forall jj0 :: 0 <= jj0 < j ==> 0 <= i * n + jj0 < |oldRet| && oldRet[i * n + jj0] == MatrixGet(arr, i, jj0);

      // Append current value
      ret := oldRet + [v];

      // Re-establish invariants for previous rows
      if i > 0 {
        forall ii, jj | 0 <= ii < i && 0 <= jj < n
          ensures 0 <= ii * n + jj < |ret| && ret[ii * n + jj] == MatrixGet(arr, ii, jj)
        {
          var k := ii * n + jj;
          assert 0 <= k < |oldRet|; // from captured assertion above
          assert |ret| == |oldRet| + 1;
          assert k < |ret|;
          // Value preserved by append
          assert ret[k] == (oldRet + [v])[k];
          SeqAppendPreservesPrefix(oldRet, v, k);
          assert (oldRet + [v])[k] == oldRet[k];
          assert oldRet[k] == MatrixGet(arr, ii, jj);
        }
      }

      // Re-establish invariants for current row up to j
      if j > 0 {
        forall jj0 | 0 <= jj0 < j
          ensures 0 <= i * n + jj0 < |ret| && ret[i * n + jj0] == MatrixGet(arr, i, jj0)
        {
          var k0 := i * n + jj0;
          assert 0 <= k0 < |oldRet|; // from captured assertion above
          assert |ret| == |oldRet| + 1;
          assert k0 < |ret|;
          assert ret[k0] == (oldRet + [v])[k0];
          SeqAppendPreservesPrefix(oldRet, v, k0);
          assert (oldRet + [v])[k0] == oldRet[k0];
          assert oldRet[k0] == MatrixGet(arr, i, jj0);
        }
      }

      // New element position
      assert |ret| == |oldRet| + 1;
      assert i * n + j == |oldRet|;
      assert 0 <= i * n + j < |ret|;
      assert ret[i * n + j] == v;
      assert ret[i * n + j] == MatrixGet(arr, i, j);

      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
