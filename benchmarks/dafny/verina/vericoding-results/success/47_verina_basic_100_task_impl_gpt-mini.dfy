// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function mul3(x: int): int { 3 * x }
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result == 3 * x
// </vc-spec>
// <vc-code>
{
  result := mul3(x);
}
// </vc-code>
