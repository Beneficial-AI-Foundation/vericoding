predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
pragma options "--allow-warnings true"
// </vc-helpers>

// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>
{
  var e0 :| 0 <= e0 < a.Length && IsEven(a[e0]);
  var i := 0;
  while i < a.Length && !IsEven(a[i])
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
    invariant i <= e0
    decreases a.Length - i
  {
    i := i + 1;
  }
  assert 0 <= i < a.Length && IsEven(a[i]);

  var o0 :| 0 <= o0 < a.Length && IsOdd(a[o0]);
  var j := 0;
  while j < a.Length && !IsOdd(a[j])
    invariant 0 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> IsEven(a[k])
    invariant j <= o0
    decreases a.Length - j
  {
    j := j + 1;
  }
  assert 0 <= j < a.Length && IsOdd(a[j]);

  diff := a[i] - a[j];
}
// </vc-code>

