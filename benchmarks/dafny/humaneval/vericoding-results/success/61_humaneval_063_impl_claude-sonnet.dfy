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
{
    if n == 0 {
        result := 0;
    } else if n == 1 {
        result := 0;
    } else if n == 2 {
        result := 1;
    } else {
        var f1 := fibfib(n-1);
        var f2 := fibfib(n-2);
        var f3 := fibfib(n-3);
        result := f1 + f2 + f3;
    }
}
// </vc-code>
