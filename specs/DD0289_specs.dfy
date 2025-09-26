// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Fact(x: int) returns (y: int)
  requires x >= 0;
// </vc-spec>
// <vc-code>
{
    y := 1;
    var z := 0;
    while(z != x)
     decreases x - z;
     invariant 0 <= x-z;
    {
        z := z + 1;
        y := y * z;
    }
}
// </vc-code>
