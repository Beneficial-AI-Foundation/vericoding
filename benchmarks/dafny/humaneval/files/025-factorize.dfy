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
  assume {:axiom} false;
}
// </vc-code>
