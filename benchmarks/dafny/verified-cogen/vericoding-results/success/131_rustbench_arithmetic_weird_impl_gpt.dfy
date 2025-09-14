// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ConstBelowTen(): int { 0 }
// </vc-helpers>

// <vc-spec>
method ArithmeticWeird() returns (result: int)
    ensures result < 10
// </vc-spec>
// <vc-code>
{
  result := 0;
}
// </vc-code>
