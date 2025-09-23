// <vc-preamble>
predicate ValidInput(N: int) {
    N >= 1
}

predicate ValidOutput(result: int) {
    result >= 0 && result < 1000000007
}

function CountValidPairs(n: int): int
    requires n >= 0
    ensures CountValidPairs(n) > 0
    decreases n
{
    if n == 0 then 1
    else if n == 1 then 2
    else CountValidPairs(n / 2) + CountValidPairs((n - 1) / 2) + CountValidPairs((n - 2) / 2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
// </vc-code>
