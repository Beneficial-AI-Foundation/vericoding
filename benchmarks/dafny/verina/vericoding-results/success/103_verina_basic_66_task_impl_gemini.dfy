// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeIsEven(x: int) returns (result: bool)
    ensures result == true <==> x % 2 == 0
// </vc-spec>
// <vc-code>
{
  result := x % 2 == 0;
}
// </vc-code>
