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
/* helper modified by LLM (iteration 3): restated parity total lemma */
lemma ParityTotal(n: int)
  ensures IsEven(n) || IsOdd(n)
{
  if n % 2 == 0 {
    assert IsEven(n);
  } else {
    assert IsOdd(n);
  }
}

/* helper modified by LLM (iteration 3): removed redundant null requirement and preserved existence past odd at i */
lemma ExistsEvenAfterIncrement(a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires (exists x :: i <= x < a.Length && IsEven(a[x]))
  requires IsOdd(a[i])
  ensures (exists x :: i + 1 <= x < a.Length && IsEven(a[x]))
{
  var x: int :| i <= x < a.Length && IsEven(a[x]);
  if i < x {
    assert i + 1 <= x;
    assert exists x' :: i + 1 <= x' < a.Length && IsEven(a[x']);
  } else {
    assert i == x; // since i <= x and not i < x
    assert IsEven(a[i]); // from IsEven(a[x]) and i == x
    assert IsOdd(a[i]);
    assert false; // contradiction, branch unreachable
  }
}

/* helper modified by LLM (iteration 3): removed redundant null requirement and preserved existence past even at j */
lemma ExistsOddAfterIncrement(a: array<int>, j: int)
  requires 0 <= j < a.Length
  requires (exists x :: j <= x < a.Length && IsOdd(a[x]))
  requires IsEven(a[j])
  ensures (exists x :: j + 1 <= x < a.Length && IsOdd(a[x]))
{
  var x: int :| j <= x < a.Length && IsOdd(a[x]);
  if j < x {
    assert j + 1 <= x;
    assert exists x' :: j + 1 <= x' < a.Length && IsOdd(a[x']);
  } else {
    assert j == x; // since j <= x and not j < x
    assert IsOdd(a[j]); // from IsOdd(a[x]) and j == x
    assert IsEven(a[j]);
    assert false; // contradiction, branch unreachable
  }
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
  /* code modified by LLM (iteration 3): derive first even/odd via loop exit conditions and avoid null-related warnings */
  var i := 0;
  // Find first even index i
  while i < a.Length && !IsEven(a[i])
    invariant 0 <= i <= a.Length
    invariant (forall k :: 0 <= k < i ==> IsOdd(a[k]))
    invariant (exists x :: i <= x < a.Length && IsEven(a[x]))
    decreases a.Length - i
  {
    assert IsOdd(a[i]); // since !IsEven(a[i]) and parity is total
    ExistsEvenAfterIncrement(a, i);
    i := i + 1;
  }
  // At exit, the existential invariant forces i < a.Length, hence IsEven(a[i])
  assert (exists x :: i <= x < a.Length && IsEven(a[x]));
  assert i < a.Length;
  assert IsEven(a[i]);

  var j := 0;
  // Find first odd index j
  while j < a.Length && !IsOdd(a[j])
    invariant 0 <= j <= a.Length
    invariant (forall k :: 0 <= k < j ==> IsEven(a[k]))
    invariant (exists x :: j <= x < a.Length && IsOdd(a[x]))
    decreases a.Length - j
  {
    assert IsEven(a[j]); // since !IsOdd(a[j])
    ExistsOddAfterIncrement(a, j);
    j := j + 1;
  }
  assert (exists x :: j <= x < a.Length && IsOdd(a[x]));
  assert j < a.Length;
  assert IsOdd(a[j]);

  result := a[i] - a[j];
}
// </vc-code>
