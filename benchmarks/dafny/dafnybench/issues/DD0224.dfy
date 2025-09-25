// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method main(n: int, k: int) returns (k_out: int)
    requires n > 0;
    requires k > n;
    ensures k_out >= 0;
// </vc-spec>
// <vc-code>
{
    k_out := k;
    var j: int := 0;
    while(j < n)
        invariant 0 <= j <= n;
        invariant k_out == k - j;
    {
        j := j + 1;
        k_out := k_out - 1;
    }
}
// </vc-code>
