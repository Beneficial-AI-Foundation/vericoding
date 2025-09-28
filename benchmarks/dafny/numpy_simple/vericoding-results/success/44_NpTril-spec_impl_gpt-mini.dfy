// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(m: Matrix<T>): nat
{
    (|m| * (if |m| > 0 then |m[0]| else 0)) as nat
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): SeqAppendLength proves length after appending an element */
lemma SeqAppendLength<T>(s: seq<T>, x: T)
  ensures |s + [x]| == |s| + 1
{
  assert |s + [x]| == |s| + |[x]|;
  assert |[x]| == 1;
  assert |s + [x]| == |s| + 1;
}

/* helper modified by LLM (iteration 2): SeqConcatLength proves length of concatenation */
lemma SeqConcatLength<T>(a: seq<T>, b: seq<T>)
  ensures |a + b| == |a| + |b|
  decreases |b|
{
  if |b| == 0 {
    assert b == [];
    assert a + b == a;
    assert |a + b| == |a|;
  } else {
    var x := b[|b| - 1];
    var b0 := b[0..|b|-1];
    SeqConcatLength(a, b0);
    SeqAppendLength(a + b0, x);
  }
}

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
/* code modified by LLM (iteration 2): Implement tril to zero out entries where j - i > k */
{
  ret := [];
  var n := |arr| as int;
  var m := |arr[0]| as int;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |ret| == i
    invariant forall ii :: 0 <= ii < i ==> |ret[ii]| == m
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < m ==> (if jj - ii > k then ret[ii][jj] == 0 else ret[ii][jj] == arr[ii][jj])
  {
    var row: seq<int> := [];
    var j := 0;
    while j < m
      invariant 0 <= j <= m
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==> (if jj - i > k then row[jj] == 0 else row[jj] == arr[i][jj])
    {
      if j - i > k {
        row := row + [0];
      } else {
        row := row + [arr[i][j]];
      }
      j := j + 1;
    }
    ret := ret + [row];
    i := i + 1;
  }
}

// </vc-code>
