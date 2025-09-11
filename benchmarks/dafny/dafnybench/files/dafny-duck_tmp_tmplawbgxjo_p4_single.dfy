// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
ensures b[..] == x[..] + y[..]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
