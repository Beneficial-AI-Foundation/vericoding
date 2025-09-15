// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
predicate IsCubeOf(n: int, r: int) { n == cube(r) }
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)

  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var found: bool := false;
  var w: nat := 0;
  while i <= n && !found
    invariant i <= n + 1
    invariant !found ==> forall j: int :: 0 <= j < i ==> n != cube(j)
    invariant found ==> 0 <= w < i && n == cube(w)
    decreases n + 1 - i
  {
    if cube(i) == n {
      found := true;
      w := i;
    }
    i := i + 1;
  }
  r := found;
  if r {
    assert 0 <= w;
    assert w < i;
    assert i <= n + 1;
    assert w < n + 1;
    assert w <= n;
    assert n == cube(w);
  } else {
    assert i > n;
    assert !found;
    forall rr: int | 0 <= rr <= n
      ensures n != cube(rr)
    {
      assert rr < i;
      assert 0 <= rr < i;
      assert n != cube(rr);
    }
  }
}
// </vc-code>
