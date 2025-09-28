// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// </vc-preamble>

// <vc-helpers>
lemma PopcountUnfold(x: nat)
  ensures x == 0 ==> popcount(x) == 0
  ensures x > 0 ==> popcount(x) == x % 2 + popcount(x / 2)
{
  if x == 0 {
    assert popcount(x) == 0;
  } else {
    assert popcount(x) == x % 2 + popcount(x / 2);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)

  ensures r == popcount(n)
// </vc-spec>
// <vc-code>
{
  r := popcount(n);
}
// </vc-code>
