// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
function SumOfFourthPowerOfOddNumbers(n: nat): nat
// </vc-spec>
// <vc-code>
{
    // impl-start
    0
    // impl-end
}

lemma SumOfFourthPowerOfOddNumbersSpec(n: nat)
    ensures
        15 * SumOfFourthPowerOfOddNumbers(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
{
    assume {:axiom} false; // TODO: Remove this line and implement the proof
}
// </vc-code>
