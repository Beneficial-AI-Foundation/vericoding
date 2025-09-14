

// <vc-helpers>
helper method IsPrefixConstant(a: array<int>, k: int, n: int) returns (b: bool)
  requires 0 <= k <= a.Length
  ensures b <==> (forall j :: 0 <= j < k ==> a[j] == n)
{
  if k == 0 then return true;
  if k < 0 then return false; // Should not happen given precondition k >= 0
  return IsPrefixConstant(a, k - 1, n) && a[k-1] == n;
}
// </vc-helpers>

// <vc-spec>
method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
// </vc-spec>
// <vc-code>
{
  if a.Length == 0 {
    return true; // An empty array trivially has "all elements equal to n"
  }

  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant (forall j :: 0 <= j < i ==> a[j] == n)
  {
    if a[i] != n {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

