// <vc-preamble>

predicate ValidInput(n: int)
{
    n >= 1
}

function SumFromOneToN(n: int): int
    requires n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == SumFromOneToN(n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed precondition violation by handling i-1=0 case */
    result := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant i == 1 ==> result == 0
        invariant i > 1 ==> result == SumFromOneToN(i - 1)
    {
        result := result + i;
        i := i + 1;
    }
}
// </vc-code>
