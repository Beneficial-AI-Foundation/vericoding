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
/* helper modified by LLM (iteration 3): Remove helper function as it's not needed and caused resolution errors */
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
/* code modified by LLM (iteration 3): Use iterative approach to avoid recursive method calls in expressions */
{
    if n == 0 {
        result := 0;
    } else if n == 1 {
        result := 0;
    } else if n == 2 {
        result := 1;
    } else {
        var a := 0;
        var b := 0;
        var c := 1;
        var i := 3;
        while i <= n
            invariant 3 <= i <= n + 1
            invariant a == fibfib_spec(i - 3)
            invariant b == fibfib_spec(i - 2)
            invariant c == fibfib_spec(i - 1)
        {
            var next := a + b + c;
            a := b;
            b := c;
            c := next;
            i := i + 1;
        }
        result := c;
    }
}
// </vc-code>
