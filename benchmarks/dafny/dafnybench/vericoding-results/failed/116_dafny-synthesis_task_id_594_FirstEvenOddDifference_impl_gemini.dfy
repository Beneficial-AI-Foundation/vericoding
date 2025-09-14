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
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Replaced recursive functions with an iterative implementation to avoid a potential toolchain warning. */
  var i := 0;
  while i < a.Length && IsOdd(a[i])
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
    decreases a.Length - i
  {
    i := i + 1;
  }
  var evenIndex := i;

  var j := 0;
  while j < a.Length && IsEven(a[j])
    invariant 0 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> IsEven(a[k])
    decreases a.Length - j
  {
    j := j + 1;
  }
  var oddIndex := j;

  diff := a[evenIndex] - a[oddIndex];
}
// </vc-code>
