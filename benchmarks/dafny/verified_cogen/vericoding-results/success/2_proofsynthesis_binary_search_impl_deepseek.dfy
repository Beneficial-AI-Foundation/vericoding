// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma BinarySearchLemma(v: array<int>, k: int, low: int, high: int)
  requires forall i, j :: 0 <= i <= j < v.Length ==> v[i] <= v[j]
  requires 0 <= low <= high <= v.Length
  requires exists i :: low <= i < high && k == v[i]
  ensures exists i :: low <= i < high && k == v[i]
{
}
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
  var low := 0;
  var high := v.Length;
  while low < high
    invariant 0 <= low <= high <= v.Length
    invariant exists i :: low <= i < high && k == v[i]
  {
    var mid := low + (high - low) / 2;
    if v[mid] == k {
      result := mid;
      return;
    } else if v[mid] < k {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  result := low;
}
// </vc-code>
