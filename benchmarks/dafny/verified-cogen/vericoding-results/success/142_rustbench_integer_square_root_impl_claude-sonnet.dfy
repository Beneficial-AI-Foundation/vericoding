// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IntegerSquareRoot(n: int) returns (result: int)
    requires n >= 1
    ensures 0 <= result * result
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
    result := 0;
    while (result + 1) * (result + 1) <= n
        invariant result >= 0
        invariant result * result <= n
    {
        result := result + 1;
    }
}
// </vc-code>
