// <vc-preamble>

function fibfib_spec(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else if n == 1 then 0
    else if n == 2 then 1
    else fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No changes needed as there are no helper functions. */

// </vc-helpers>

// <vc-spec>
method fibfib(n: int) returns (result: int)
    requires n >= 0
    ensures result == fibfib_spec(n)
    ensures n == 0 ==> result == 0
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 1
    ensures n >= 3 ==> result == fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed parsing error by correcting 'if n == 0 then {' to 'if n == 0 {'. */
{
    if n == 0 {
        result := 0;
    } else if n == 1 {
        result := 0;
    } else if n == 2 {
        result := 1;
    } else {
        var a0: int := 0;
        var a1: int := 0;
        var a2: int := 1;
        var i: int := 3;
        while i <= n
            invariant 3 <= i <= n + 1
            invariant a0 == fibfib_spec(i-3)
            invariant a1 == fibfib_spec(i-2)
            invariant a2 == fibfib_spec(i-1)
        {
            var next_fibfib := a0 + a1 + a2;
            a0 := a1;
            a1 := a2;
            a2 := next_fibfib;
            i := i + 1;
        }
        result := a2;
    }
}
// </vc-code>
