// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    invariant is_consecutive == (forall k, l :: 0 <= k < l <= i && l == k + 1 ==> arr[k] + 1 == arr[l])
  {
    if arr[i] + 1 != arr[i + 1] {
      is_consecutive := false;
    }
    i := i + 1;
  }
}
// </vc-code>
