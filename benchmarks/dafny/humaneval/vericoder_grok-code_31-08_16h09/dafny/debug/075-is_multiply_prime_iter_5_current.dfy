function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var factors: seq<nat> := [];
  var cp := x;
  var cand := 2;
  while cand * cand <= cp
    invariant cp >= 1
    invariant forall f :: f in factors ==> Prime(f) && f * f <= x
  {
    if Prime(cand) && cp % cand == 0
    {
      while cp % cand == 0
        decreases cp
      {
        factors := factors + [cand];
        cp := cp / cand;
      }
    }
    cand := cand + 1;
  }
  if cp > 1 && Prime(cp)
  {
    factors := factors + [cp];
  }
  ans := |factors| == 3;
}
// </vc-code>

