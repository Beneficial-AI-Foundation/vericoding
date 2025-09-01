

// <vc-helpers>
lemma divisor_exists(n: int)
  requires n > 1
  ensures exists d :: 1 <= d < n && n % d == 0
{
  assert n % 1 == 0;
  assert 1 < n;
}

lemma largest_divisor_unique(n: int, d1: int, d2: int)
  requires n > 1
  requires 1 <= d1 < n && n % d1 == 0
  requires 1 <= d2 < n && n % d2 == 0
  requires forall k :: d1 < k < n ==> n % k != 0
  requires forall k :: d2 < k < n ==> n % k != 0
  ensures d1 == d2
{
  if d1 < d2 {
    assert d1 < d2 < n;
    assert n % d2 != 0;
    assert false;
  } else if d2 < d1 {
    assert d2 < d1 < n;
    assert n % d1 != 0;
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)
  // pre-conditions-start
  requires n > 1
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  d := n - 1;
  while d > 1 && n % d != 0
    invariant 1 <= d < n
    invariant forall k :: d < k < n ==> n % k != 0
    decreases d
  {
    d := d - 1;
  }
}
// </vc-code>

