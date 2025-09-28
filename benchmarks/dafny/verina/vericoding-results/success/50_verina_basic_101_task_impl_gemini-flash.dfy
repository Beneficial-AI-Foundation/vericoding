// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isMultipleOf3(n: int): bool {
  n % 3 == 0
}
// </vc-helpers>

// <vc-spec>
method triple(x: int) returns (result: int)
    ensures
        result / 3 == x &&
        result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  result := x * 3;
}
// </vc-code>
