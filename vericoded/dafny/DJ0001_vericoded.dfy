// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate Sorted(v: array<int>)
  reads v
{
  forall i, j :: 0 <= i <= j < v.Length ==> v[i] <= v[j]
}

lemma BinarySearchInvariant(v: array<int>, k: int, lo: int, hi: int)
  requires Sorted(v)
  requires 0 <= lo <= hi <= v.Length
  requires exists i :: lo <= i < hi && v[i] == k
  ensures exists i :: lo <= i < hi && v[i] == k
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
  var lo := 0;
  var hi := v.Length;
  
  while lo < hi - 1
    invariant 0 <= lo < hi <= v.Length
    invariant exists i :: lo <= i < hi && v[i] == k
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if v[mid] <= k {
      lo := mid;
    } else {
      hi := mid;
    }
  }
  
  result := lo;
}
// </vc-code>
