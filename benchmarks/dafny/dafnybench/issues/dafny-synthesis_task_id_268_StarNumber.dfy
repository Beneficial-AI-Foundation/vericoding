// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
// </vc-spec>
// <vc-code>
{
    star := 6 * n * (n - 1) + 1;
}
// </vc-code>
