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
/* helper modified by LLM (iteration 2): FindFirstEven finds index of first even element */
method FindFirstEven(a: array<int>) returns (i: int)
  requires a.Length > 0 && (exists k :: 0 <= k < a.Length && IsEven(a[k]))
  ensures 0 <= i < a.Length && IsEven(a[i]) && (forall k :: 0 <= k < i ==> IsOdd(a[k]))
{
  var idx := 0;
  while idx < a.Length && !IsEven(a[idx])
    invariant 0 <= idx <= a.Length
    invariant forall k :: 0 <= k < idx ==> IsOdd(a[k])
    decreases a.Length - idx
  {
    idx := idx + 1;
  }
  if idx == a.Length {
    assert false;
  }
  i := idx;
}

/* helper modified by LLM (iteration 2): FindFirstOdd finds index of first odd element */
method FindFirstOdd(a: array<int>) returns (j: int)
  requires a.Length > 0 && (exists k :: 0 <= k < a.Length && IsOdd(a[k]))
  ensures 0 <= j < a.Length && IsOdd(a[j]) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
{
  var idx := 0;
  while idx < a.Length && !IsOdd(a[idx])
    invariant 0 <= idx <= a.Length
    invariant forall k :: 0 <= k < idx ==> IsEven(a[k])
    decreases a.Length - idx
  {
    idx := idx + 1;
  }
  if idx == a.Length {
    assert false;
  }
  j := idx;
}

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
  /* code modified by LLM (iteration 2): call helpers to get indices and compute difference */
  var ie := FindFirstEven(a);
  var jo := FindFirstOdd(a);
  result := a[ie] - a[jo];
}

// </vc-code>
