// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SumAndAverage(n: int) returns (result: (int, real))
    requires n < 100000  // reasonable bound to prevent overflow
    ensures
        n == 0 ==> result.0 == 0
    ensures
        n > 0 ==> result.0 == (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    var sum: int := 0;
    if n > 0 {
        var i: int := 1;
        while i <= n
            invariant 1 <= i <= n + 1
            invariant sum == ((i - 1) * i) / 2
        {
            sum := sum + i;
            i := i + 1;
        }
    }
    var avg: real := if n > 0 then (sum as real) / (n as real) else 0.0;
    result := (sum, avg);
}
// </vc-code>
