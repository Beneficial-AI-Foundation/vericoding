

// <vc-helpers>
module {:options "--allow-warnings"} __opts {}
// </vc-helpers>

// <vc-spec>
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0;
    requires n <= a.Length;
    requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
    ensures r <= max * n;
// </vc-spec>
// <vc-code>
{
  var s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s <= i * max
    decreases n - i
  {
    assert 0 <= i && i < n;
    assert i < a.Length;
    assert a[i] <= max;
    var t := s + a[i];
    assert t <= i * max + max;
    assert i * max + max == (i + 1) * max;
    s := t;
    i := i + 1;
  }
  r := s;
}
// </vc-code>

