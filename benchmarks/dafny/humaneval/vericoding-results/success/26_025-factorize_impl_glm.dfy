// <vc-preamble>
function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method factorize(n: nat) returns (factors: seq<nat>)

  requires n > 0

  ensures prod(factors) == n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added decreases clause to inner loop */
  factors := [];
  var m := n;
  var d := 2;
  while d * d <= m
    invariant prod(factors) * m == n
    invariant m >= 1
  {
    while m % d == 0
      invariant prod(factors) * m == n
      invariant m >= 1
      decreases m
    {
      factors := factors + [d];
      m := m / d;
    }
    d := d + 1;
  }
  if m > 1 {
    factors := factors + [m];
  }
}
// </vc-code>
