// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
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
  while i + 1 < arr.Length
    invariant 0 <= i <= arr.Length
    invariant i + 1 <= arr.Length
    invariant is_consecutive == (forall p, q :: 0 <= p < q < i + 1 && q == p + 1 ==> arr[p] + 1 == arr[q])
    decreases arr.Length - i
  {
    if arr[i] + 1 != arr[i + 1] {
      is_consecutive := false;
    }
    i := i + 1;
  }
  assert i + 1 == arr.Length;
  assert is_consecutive == (forall p, q :: 0 <= p < q < arr.Length && q == p + 1 ==> arr[p] + 1 == arr[q]);
}
// </vc-code>
