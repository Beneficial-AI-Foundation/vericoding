predicate IsOdd(n: int)
{
    n % 2 == 1
}

// <vc-helpers>
// (no helpers required)
// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := true;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result <==> forall j :: 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a[j]))
    decreases a.Length - i
  {
    if IsOdd(i) && !IsOdd(a[i]) {
      assert 0 <= i < a.Length && IsOdd(i) && !IsOdd(a[i]);
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

