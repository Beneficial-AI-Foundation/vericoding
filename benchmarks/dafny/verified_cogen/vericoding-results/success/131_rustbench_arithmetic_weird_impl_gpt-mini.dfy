// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function getNine(): int { 9 }
// </vc-helpers>

// <vc-spec>
method ArithmeticWeird() returns (result: int)
    ensures result < 10
// </vc-spec>
// <vc-code>
{
  result := getNine();
}
// </vc-code>
