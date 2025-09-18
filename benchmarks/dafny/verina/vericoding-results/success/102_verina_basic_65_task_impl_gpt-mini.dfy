// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma InitInvariant(n: nat)
  ensures 0*0 <= n
  ensures n < (n+1)*(n+1)
{
  assert 0 <= n;
  assert n+1 > n;
  assert (n+1)*(n+1) - (n+1) == (n+1)*n;
  assert (n+1)*n >= 0;
  assert (n+1)*(n+1) >= n+1;
  assert n < (n+1)*(n+1);
}

lemma MidBounds(lo: nat, hi: nat, mid: nat)
  requires lo < hi
  requires mid == lo + (hi - lo + 1) / 2
  ensures lo < mid <= hi
{
  var d := hi - lo;
  assert d >= 1;
  assert mid - lo == (d + 1) / 2;
  assert (d + 1) / 2 >= 1;
  assert (d + 1) / 2 <= d;
  assert mid > lo;
  assert mid <= hi;
}

// </vc-helpers>

// <vc-spec>
method SquareRoot(n: nat) returns (result: nat)
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := n;
  while lo < hi
    invariant 0 <= lo <= hi <= n
    invariant lo*lo <= n && n < (hi + 1) * (hi + 1)
    decreases hi - lo
  {
    var mid := lo + (hi - lo + 1) / 2;
    assert mid > lo && mid <= hi;
    if mid * mid <= n {
      lo := mid;
    } else {
      hi := mid - 1;
    }
  }
  result := lo;
}
// </vc-code>
