// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BinarySearch(v: array<int>, k: int) returns (result: int)
    requires forall i, j :: 0 <= i <= j < v.Length ==> v[i] <= v[j]
    requires exists i :: 0 <= i < v.Length && k == v[i]
    ensures 0 <= result < v.Length
    ensures k == v[result]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): add early return when v[mid] == k to maintain invariant */
  var low := 0;
  var high := v.Length;
  while low < high
    invariant 0 <= low <= high <= v.Length
    invariant forall i :: 0 <= i < low ==> v[i] < k
    invariant forall i :: high <= i < v.Length ==> v[i] >= k
    invariant exists i :: low <= i < high && v[i] == k
  {
    var mid := (low + high) / 2;
    if v[mid] < k {
      low := mid + 1;
    } else if v[mid] == k {
      result := mid;
      return;
    } else {
      high := mid;
    }
  }
  result := low;
}
// </vc-code>
