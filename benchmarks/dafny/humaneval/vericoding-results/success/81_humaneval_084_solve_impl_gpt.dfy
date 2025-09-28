// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// </vc-preamble>

// <vc-helpers>
lemma popcount_step(n: nat)
  ensures n > 0 ==> popcount(n) == n % 2 + popcount(n / 2)
{
}

lemma popcount_zero()
  ensures popcount(0) == 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)

  ensures r == popcount(n)
// </vc-spec>
// <vc-code>
{
  var acc: nat := 0;
  var x: nat := n;
  while x > 0
    invariant acc + popcount(x) == popcount(n)
    decreases x
  {
    assert popcount(x) == x % 2 + popcount(x / 2);
    acc := acc + x % 2;
    x := x / 2;
  }
  assert popcount(0) == 0;
  r := acc;
}
// </vc-code>
