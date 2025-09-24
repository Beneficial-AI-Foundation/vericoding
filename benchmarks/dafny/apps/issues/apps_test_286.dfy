// <vc-preamble>
predicate ValidInput(n: int) {
    1 <= n <= 1000000000
}

function DistinctWeights(n: int): int
    requires ValidInput(n)
{
    1 + n / 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountDistinctWeights(n: int) returns (count: int)
    requires ValidInput(n)
    ensures count == DistinctWeights(n)
    ensures count >= 1
// </vc-spec>
// <vc-code>
{
    count := 1 + n / 2;
}
// </vc-code>
