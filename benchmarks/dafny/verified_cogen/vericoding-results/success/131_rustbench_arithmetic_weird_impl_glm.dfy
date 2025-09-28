// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function GetFive(): int { 5 }
// </vc-helpers>

// <vc-spec>
method ArithmeticWeird() returns (result: int)
    ensures result < 10
// </vc-spec>
// <vc-code>
{
  result := GetFive();
}
// </vc-code>
