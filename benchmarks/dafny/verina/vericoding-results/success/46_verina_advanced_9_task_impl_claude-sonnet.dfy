// <vc-preamble>
function SumOfDigits(x: nat): nat
    decreases x
{
    if x == 0 then 0 else (x % 10) + SumOfDigits(x / 10)
}

predicate IsSumDivisibleBy(x: nat, d: nat)
    requires d > 0
{
    (SumOfDigits(x) % d) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountSumDivisibleBy(n: nat, d: nat) returns (result: nat)
    requires d > 0
    ensures result <= n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed loop bound to ensure result <= n */
    result := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result <= i
    {
        if IsSumDivisibleBy(i, d) {
            result := result + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
