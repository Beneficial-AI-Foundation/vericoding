// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(m: Matrix<T>): nat
{
    (|m| * (if |m| > 0 then |m[0]| else 0)) as nat
}
// </vc-preamble>

// <vc-helpers>


// </vc-helpers>

// <vc-spec>
method Tril(arr: Matrix<int>, k: int) returns (ret: Matrix<int>)
    requires 
        |arr| > 0 &&
        |arr[0]| > 0 &&
        (forall i :: 0 <= i < |arr| ==> |arr[i]| == |arr[0]|) &&
        -((|arr| as int) - 1) < k && k < (|arr[0]| as int) - 1
    ensures
        MatrixSize(ret) == MatrixSize(arr) &&
        |ret| == |arr| &&
        (forall i :: 0 <= i < |ret| ==> |ret[i]| == |arr[0]|) &&
        forall i: int, j: int :: 
            0 <= i < |arr| && 0 <= j < |arr[0]| ==> 
                if j - i > k then ret[i][j] == 0 else ret[i][j] == arr[i][j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Replaced the array-based logic with a sequence-based one, fixing compilation errors related to array initialization and null checks on sequences. */
  var m_rows := |arr|;
  var n_cols := |arr[0]|;
  ret := [];

  for i := 0 to m_rows
    invariant |ret| == i
    invariant forall r :: 0 <= r < i ==> |ret[r]| == n_cols
    invariant forall r, c :: 0 <= r < i && 0 <= c < n_cols ==> (if c - r > k then ret[r][c] == 0 else ret[r][c] == arr[r][c])
  {
    var new_row: seq<int> := [];
    for j := 0 to n_cols
      invariant |new_row| == j
      invariant forall c :: 0 <= c < j ==> (if c - i > k then new_row[c] == 0 else new_row[c] == arr[i][c])
    {
      if j - i > k {
        new_row := new_row + [0];
      } else {
        new_row := new_row + [arr[i][j]];
      }
    }
    ret := ret + [new_row];
  }
}
// </vc-code>
