function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}


ghost function minFunction(a: int, b: int): int
    ensures minFunction(a, b) <= a && minFunction(a, b) <= b
    ensures minFunction(a, b) == a || minFunction(a, b) == b
{
    if a < b then a else b
}


// Return a minimum of a.

// <vc-helpers>
lemma MinLemma(a: array<int>, i: int, j: int)
  requires a != null
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures min(a[i], a[j]) <= a[i] && min(a[i], a[j]) <= a[j]
{
}

lemma ExistsMinLemma(a: array<int>, i: int)
  requires a != null && a.Length > 0
  requires 0 <= i < a.Length
  ensures exists k | 0 <= k < a.Length :: min(a[i], a[k]) == a[k]
{
  var k := i;
}

lemma MinPreservation(a: array<int>, m: int, i: int)
  requires a != null
  requires 0 <= i < a.Length
  requires forall k | 0 <= k < i :: m <= a[k]
  requires exists k | 0 <= k < i :: m == a[k]
  ensures forall k | 0 <= k <= i :: min(m, a[i]) <= a[k]
  ensures exists k | 0 <= k <= i :: min(m, a[i]) == a[k]
{
  var new_m := min(m, a[i]);
  // Show that new_m is <= all elements up to i
  forall k | 0 <= k < i ensures new_m <= a[k] {
    assert m <= a[k];
    assert new_m <= m;
  }
  assert new_m <= a[i];
  
  // Show that new_m exists in the array
  if a[i] < m {
    assert new_m == a[i];
  } else {
    assert exists k | 0 <= k < i :: m == a[k];
  }
}
// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 
    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
// </vc-spec>
// <vc-code>
{
  m := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k | 0 <= k < i :: m <= a[k]
    invariant exists k | 0 <= k < i :: m == a[k]
  {
    MinPreservation(a, m, i);
    m := min(m, a[i]);
    i := i + 1;
  }
}
// </vc-code>

