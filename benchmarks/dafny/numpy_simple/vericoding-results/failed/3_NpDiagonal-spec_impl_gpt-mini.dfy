// <vc-preamble>
/* Matrix type represented as a sequence of sequences */
type Matrix<T> = seq<seq<T>>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): positive k range lemma */
lemma PositiveKRange(n: int, k: int)
  requires n > 0 && -n < k < n && k > 0
  ensures forall i {:trigger i} :: 0 <= i < n - k ==> 0 <= i < n && 0 <= i + k < n
{
  var m := n - k;
  forall i | 0 <= i < m {
    assert 0 <= i;
    assert i < m;
    // m = n - k and k > 0 implies m <= n - 1, so i < m ==> i < n
    assert i < n;
    // from i < n - k, adding k gives i + k < n
    assert i + k < n;
  }
}

/* helper modified by LLM (iteration 5): non-positive k range lemma */
lemma NegativeKRange(n: int, k: int)
  requires n > 0 && -n < k < n && k <= 0
  ensures forall i {:trigger i} :: 0 <= i < n + k ==> 0 <= i + (-k) < n && 0 <= i < n
{
  var m := n + k;
  forall i | 0 <= i < m {
    assert 0 <= i;
    assert i < m;
    // when k <= 0, m = n + k <= n, so i < m implies i < n
    assert i < n;
    // from i < n + k, adding -k yields i + (-k) < n
    assert i + (-k) < n;
  }
}

// </vc-helpers>

// <vc-spec>
method diagonal(arr: Matrix<int>, k: int) returns (result: seq<int>)
    requires 
        |arr| > 0 &&
        |arr| == |arr[0]| && /* square matrix */
        (forall i :: 0 <= i < |arr| ==> |arr[i]| == |arr|) &&
        -|arr| < k < |arr|
    ensures
        if k > 0 then
            |result| == |arr| - k &&
            forall i :: 0 <= i < |result| ==> 
                0 <= i < |arr| && 0 <= i + k < |arr| && result[i] == arr[i][i + k]
        else
            |result| == |arr| + (-k) &&
            forall i :: 0 <= i < |result| ==> 
                0 <= i + (-k) < |arr| && 0 <= i < |arr| && result[i] == arr[i + (-k)][i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): construct diagonal sequence respecting ranges */
  var n := |arr|;
  if k > 0 {
    var m := n - k;
    PositiveKRange(n, k);
    var r: seq<int> := [];
    var i := 0;
    while i < m
      invariant 0 <= i <= m
      invariant |r| == i
      invariant forall j :: 0 <= j < i ==> 0 <= j < n && 0 <= j + k < n && r[j] == arr[j][j + k]
    {
      r := r + [arr[i][i + k]];
      i := i + 1;
    }
    result := r;
  } else {
    var m := n + k;
    NegativeKRange(n, k);
    var kk := -k;
    var r: seq<int> := [];
    var i := 0;
    while i < m
      invariant 0 <= i <= m
      invariant |r| == i
      invariant forall j :: 0 <= j < i ==> 0 <= j + kk < n && 0 <= j < n && r[j] == arr[j + kk][j]
    {
      r := r + [arr[i + kk][i]];
      i := i + 1;
    }
    result := r;
  }
}

// </vc-code>
