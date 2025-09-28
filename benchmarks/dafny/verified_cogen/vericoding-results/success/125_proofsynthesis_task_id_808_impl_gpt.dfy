// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method ContainsK(arr: array<int>, k: int) returns (result: bool)
    ensures result == (exists i :: 0 <= i < arr.Length && arr[i] == k)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var found := false;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant found == (exists j :: 0 <= j < i && arr[j] == k)
    decreases arr.Length - i
  {
    found := found || arr[i] == k;
    i := i + 1;
  }
  result := found;
}
// </vc-code>
