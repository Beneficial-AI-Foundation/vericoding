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
/* helper modified by LLM (iteration 2): parity complement lemma */
lemma ParityComplement(n: int) ensures (IsEven(n) <==> !IsOdd(n)) { }
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
  /* code modified by LLM (iteration 2): find first even and first odd using witnesses and loops */
  ghost var wEven :| 0 <= wEven < a.Length && IsEven(a[wEven]);
  ghost var wOdd :| 0 <= wOdd < a.Length && IsOdd(a[wOdd]);

  var i := 0;
  while i < a.Length && !IsEven(a[i])
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
    invariant i <= wEven
    decreases wEven - i
  {
    i := i + 1;
  }
  assert i < a.Length;
  assert IsEven(a[i]);

  var j := 0;
  while j < a.Length && !IsOdd(a[j])
    invariant 0 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> IsEven(a[k])
    invariant j <= wOdd
    decreases wOdd - j
  {
    j := j + 1;
  }
  assert j < a.Length;
  assert IsOdd(a[j]);

  result := a[i] - a[j];

  assert (exists ii, jj :: ii == i && jj == j && 0 <= ii < a.Length && 0 <= jj < a.Length && IsEven(a[ii]) && IsOdd(a[jj]) && result == a[ii] - a[jj] && (forall k :: 0 <= k < ii ==> IsOdd(a[k])) && (forall k :: 0 <= k < jj ==> IsEven(a[k])));
}

// </vc-code>
