// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(v: array<int>)
  reads v
{
  forall i, j :: 0 <= i <= j < v.Length ==> v[i] <= v[j]
}

lemma BinarySearchInvariant(v: array<int>, k: int, low: int, high: int)
  requires IsSorted(v)
  requires 0 <= low <= high < v.Length
  requires exists i :: low <= i <= high && v[i] == k
  ensures exists i :: low <= i <= high && v[i] == k
{}
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
  var high := v.Length - 1;
  
  while low <= high
    invariant 0 <= low <= high + 1 <= v.Length
    invariant exists i :: low <= i <= high && v[i] == k
  {
    var mid := (low + high) / 2;
    
    if v[mid] == k {
      result := mid;
      return;
    } else if v[mid] < k {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  result := 0;
}
// </vc-code>
