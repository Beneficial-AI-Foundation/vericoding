predicate IsOdd(x: int)
{
    x % 2 != 0
}

// <vc-helpers>

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
  found := false;
  index := -1;
  while i < a.Length && !found
    invariant 0 <= i <= a.Length
    invariant !found ==> forall k :: 0 <= k < i ==> !IsOdd(a[k])
    invariant found ==> 0 <= index < i && IsOdd(a[index]) && forall k :: 0 <= k < index ==> !IsOdd(a[k])
  {
    if IsOdd(a[i])
    {
      found := true;
      index := i;
    }
    i := i + 1;
  }
}
// </vc-code>

