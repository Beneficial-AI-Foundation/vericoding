// <vc-preamble>
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
// </vc-spec>
// <vc-code>
{
  var y1 := x1;
  var y2 := x2;
  while (y1 != y2)
    invariant 1 <= y1 && 1 <= y2;
    decreases y1 + y2;
  {
    while (y1 > y2)
      invariant 1 <= y1 && 1 <= y2;
    {
      y1 := y1 - y2;
    }
    while (y2 > y1)
      invariant 1 <= y1 && 1 <= y2;
    {
      y2 := y2 - y1;
    }
  }
}
// </vc-code>
