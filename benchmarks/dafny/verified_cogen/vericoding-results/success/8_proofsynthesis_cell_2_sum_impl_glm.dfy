// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix bound_item to always return <= 2 */
function bound_item(x: int): int { if x < 0 then 2 else if x <= 2 then x else 2 }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int) returns (sum: int)
    requires 
        a.Length == N &&
        N <= 0x7FFF_FFFF

    ensures
        sum <= 2*N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fix assertion by ensuring bound_item <= 2 */
{
    var i := 0;
    sum := 0;
    while i < N
        invariant 0 <= i <= N
        invariant sum <= 2 * i
    {
        sum := sum + bound_item(a[i]);
        assert sum <= 2 * (i + 1);
        i := i + 1;
    }
    assert sum <= 2 * N;
}
// </vc-code>
