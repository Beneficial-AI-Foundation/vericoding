function min(x: int, y: int): int
{
    if x <= y then x else y
}

predicate ValidInput(k: int, a: int, b: int, v: int)
{
    2 <= k <= 1000 && 1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= v <= 1000
}

function BoxCapacity(numBoxes: int, k: int, b: int, v: int): int
    requires numBoxes >= 0
{
    v * (numBoxes + min(b, (k - 1) * numBoxes))
}

predicate CanStoreNuts(numBoxes: int, k: int, a: int, b: int, v: int)
    requires numBoxes >= 0
{
    a <= BoxCapacity(numBoxes, k, b, v)
}

predicate IsMinimalSolution(result: int, k: int, a: int, b: int, v: int)
    requires result >= 1
{
    CanStoreNuts(result, k, a, b, v) &&
    (result == 1 || !CanStoreNuts(result - 1, k, a, b, v))
}

// <vc-helpers>
lemma MinAtLeastOne(k: int, n: int, b: int)
  requires 2 <= k
  requires 1 <= n
  requires 1 <= b
  ensures min(b, (k - 1) * n) >= 1
{
  if b <= (k - 1) * n {
  } else {
  }
}

lemma CapacityLowerBound(n: int, k: int, b: int, v: int)
  requires 1 <= n
  requires 2 <= k
  requires 1 <= b
  requires 1 <= v
  ensures BoxCapacity(n, k, b, v) >= n + 1
{
  var m := min(b, (k - 1) * n);
  MinAtLeastOne(k, n, b);
  assert m >= 1;
  assert n + m >= n + 1;
  assert v - 1 >= 0;
  assert n + m >= 0;
  assert (v - 1) * (n + m) >= 0;
  assert v * (n + m) - (n + m) == (v - 1) * (n + m);
  assert v * (n + m) >= n + m;
  assert v * (n + m) >= n + 1;
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int, v: int) returns (result: int)
    requires ValidInput(k, a, b, v)
    ensures result >= 1
    ensures result <= 1009
    ensures IsMinimalSolution(result, k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && result == i && 
            (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v))
// </vc-spec>
// <vc-code>
{
  var i := 1;
  while (!CanStoreNuts(i, k, a, b, v))
    invariant ValidInput(k, a, b, v)
    invariant 1 <= i
    invariant i <= a
    invariant forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v)
    decreases a - i + 1
  {
    CapacityLowerBound(i, k, b, v);
    assert a > BoxCapacity(i, k, b, v);
    assert i + 1 <= a;
    assert forall j :: 1 <= j < i + 1 ==> !CanStoreNuts(j, k, a, b, v) {
      if j < i {
      } else {
        assert j == i;
      }
    }
    i := i + 1;
  }
  result := i;
  assert result >= 1;
  assert result <= a;
  assert result <= 1009;
  assert CanStoreNuts(result, k, a, b, v);
  assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v);
}
// </vc-code>

