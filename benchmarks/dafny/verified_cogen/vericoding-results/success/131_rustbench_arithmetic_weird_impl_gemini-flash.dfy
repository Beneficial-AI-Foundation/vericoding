// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Helper(x: int): int { x - 2 }
// </vc-helpers>

// <vc-spec>
method ArithmeticWeird() returns (result: int)
    ensures result < 10
// </vc-spec>
// <vc-code>
{
  result := 5;
}
// </vc-code>
