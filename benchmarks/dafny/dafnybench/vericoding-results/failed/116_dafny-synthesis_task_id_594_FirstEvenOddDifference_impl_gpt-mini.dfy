predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
// Helper lemmas to discharge impossible cases when loops reach the end despite existence preconditions.
lemma ContradictionEven(a: array<int>, ie: int)
  requires 0 <= ie <= a.Length
  requires forall k :: 0 <= k < ie ==> IsOdd(a[k])
  requires ie == a.Length
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  ensures false
{
  // Pick a witness for the existential that there exists an even entry.
  var i :| 0 <= i < a.Length && IsEven(a[i]);
  // From forall k < ie and ie == a.Length we know a[i] is odd.
  assert i < ie by {
    calc {
      i;
      <=;
      a.Length;
      ==;
      ie;
    }
  }
  assert IsOdd(a[i]);
  // But by choice a[i] is also even: contradiction.
  assert IsEven(a[i]);
  assert false;
}

lemma ContradictionOdd(a: array<int>, io: int)
  requires 0 <= io <= a.Length
  requires forall k :: 0 <= k < io ==> IsEven(a[k])
  requires io == a.Length
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures false
{
  var i :| 0 <= i < a.Length && IsOdd(a[i]);
  assert i < io by {
    calc {
      i;
      <=;
      a.Length;
      ==;
      io;
    }
  }
  assert IsEven(a[i]);
  assert IsOdd(a[i]);
  assert false;
}
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
  var ie := 0;
  while ie < a.Length && !IsEven(a[ie])
    invariant 0 <= ie <= a.Length
    invariant forall k :: 0 <= k < ie ==> IsOdd(a[k])
    decreases a.Length - ie
  {
    ie := ie + 1;
  }
  if ie == a.Length {
    ContradictionEven(a, ie);
  }
  assert ie < a.Length;
  assert IsEven(a[ie]);

  var io := 0;
  while io < a.Length && !IsOdd(a[io])
    invariant 0 <= io <= a.Length
    invariant forall k :: 0 <= k < io ==> IsEven(a[k])
    decreases a.Length - io
  {
    io := io + 1;
  }
  if io == a.Length {
    ContradictionOdd(a, io);
  }
  assert io < a.Length;
  assert IsOdd(a[io]);

  diff := a[ie] - a[io];

  assert 0 <= ie < a.Length && 0 <= io < a.Length && IsEven(a[ie]) && IsOdd(a[io]) && diff == a[ie] - a[io] && (forall k :: 0 <= k < ie ==> IsOdd(a[k])) && (forall k :: 0 <= k < io ==> IsEven(a[k]));
}
// </vc-code>

