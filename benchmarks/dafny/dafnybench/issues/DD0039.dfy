// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method fillK(a: array<int>, n: int, k: int, c: int) returns (b: bool)
    requires 0 <= c <= n
    requires n == a.Length
// </vc-spec>
// <vc-code>
{
    if c == 0 {
        return true;
    }

    var p := 0;
    while p < c
        invariant 0 <= p <= c

        {
            if a[p] != k
            {
                return false;
            }

            p := p + 1;
        }
    return true;
}
// </vc-code>
