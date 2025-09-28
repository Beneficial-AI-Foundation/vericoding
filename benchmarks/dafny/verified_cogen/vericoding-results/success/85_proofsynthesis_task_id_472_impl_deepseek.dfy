// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ConsecutiveLemma(arr: array<int>, i: int, j: int)
  requires 0 <= i < j < arr.Length
  requires j == i + 1
  ensures arr[i] + 1 == arr[j] || !(forall k, l :: 0 <= k < l < arr.Length && l == k + 1 ==> (arr[k] + 1 == arr[l]))
{
  // If all consecutive pairs are consecutive numbers, then this specific pair must be
  if !(arr[i] + 1 == arr[j]) {
    var counterexample_k, counterexample_l := i, j;
    // This shows the existence of k,l that violate the condition
  }
}
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(arr: array<int>) returns (is_consecutive: bool)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> (0 <= arr[i] + 1 < 2147483647)
    ensures is_consecutive == (forall i, j :: 0 <= i < j < arr.Length && j == i + 1 ==> (arr[i] + 1 == arr[j]))
// </vc-spec>
// <vc-code>
{
  is_consecutive := true;
  var i := 0;
  while i < arr.Length - 1
    invariant 0 <= i <= arr.Length - 1
    invariant forall k :: 0 <= k < i ==> (arr[k] + 1 == arr[k + 1])
  {
    if arr[i] + 1 != arr[i + 1] {
      is_consecutive := false;
      return;
    }
    i := i + 1;
  }
  is_consecutive := is_consecutive;
}
// </vc-code>
