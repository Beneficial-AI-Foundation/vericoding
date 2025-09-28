// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (result: int)
    requires 
        a.Length > 1 &&
        (exists x :: 0 <= x < a.Length && IsEven(a[x])) &&
        (exists x :: 0 <= x < a.Length && IsOdd(a[x]))
    ensures 
        exists i, j :: 
            0 <= i < a.Length && 0 <= j < a.Length &&
            IsEven(a[i]) && IsOdd(a[j]) &&
            result == a[i] - a[j] &&
            (forall k :: 0 <= k < i ==> IsOdd(a[k])) &&
            (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>

{
  var i := 0;
  while i < a.Length && !IsEven(a[i])
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
  {
    i := i + 1;
  }
  var j := 0;
  while j < a.Length && !IsOdd(a[j])
    invariant 0 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> IsEven(a[k])
  {
    j := j + 1;
  }
  result := a[i] - a[j];
}

// </vc-code>
