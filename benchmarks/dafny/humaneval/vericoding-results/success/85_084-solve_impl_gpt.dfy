// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// </vc-preamble>

// <vc-helpers>
lemma UnfoldPopcountPositive(m: nat)
  requires m > 0
  ensures popcount(m) == m % 2 + popcount(m / 2)
{ }

lemma Div2Lt(m: nat)
  requires m > 0
  ensures m / 2 < m
{ }
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)

  ensures r == popcount(n)
// </vc-spec>
// <vc-code>
{
  var m := n;
  var c: nat := 0;
  while m > 0
    invariant c + popcount(m) == popcount(n)
    decreases m
  {
    var t := m;
    UnfoldPopcountPositive(t);
    c := c + t % 2;
    Div2Lt(t);
    m := t / 2;
  }
  r := c;
}
// </vc-code>
