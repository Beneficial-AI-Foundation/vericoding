predicate IsOdd(x: int)
{
    x % 2 != 0
}

// <vc-helpers>
// The duplicate predicate IsOdd is removed. The one in the preamble is sufficient.
// </vc-helpers>

// <vc-spec>
method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
    requires a != null
    ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> !IsOdd(a[k])
  {
    if IsOdd(a[i]) {
      return true, i;
    }
    i := i + 1;
  }
  return false, 0;
}
// </vc-code>

