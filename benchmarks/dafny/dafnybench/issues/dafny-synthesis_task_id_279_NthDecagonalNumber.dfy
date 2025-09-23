// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method NthDecagonalNumber(n: int) returns (decagonal: int)
    requires n >= 0
    ensures decagonal == 4 * n * n - 3 * n
// </vc-spec>
// <vc-code>
{
    decagonal := 4 * n * n - 3 * n;
}
// </vc-code>
