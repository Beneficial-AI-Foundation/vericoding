// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SquareOfSuccIsLarger(x: int)
    requires x >= 1
    ensures x < (x + 1) * (x + 1)
{ }
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
    var low := 0;
    var high := n + 1;

    if n >= 1 {
        SquareOfSuccIsLarger(n);
    }

    while low < high
        invariant 0 <= low <= high <= n + 1
        invariant low == 0 || (low - 1) * (low - 1) <= n
        invariant high == n + 1 || high * high > n
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        if mid * mid > n {
            high := mid;
        } else {
            low := mid + 1;
        }
    }

    result := low - 1;
}
// </vc-code>
