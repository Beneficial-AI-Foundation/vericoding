function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

// <vc-helpers>
lemma lemma_CountOnesInOctalNonNegative(a: int)
    requires a >= 0
    ensures CountOnesInOctal(a) >= 0
{
    if a == 0 {
    } else {
        lemma_CountOnesInOctalNonNegative(a / 8);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int) returns (count: int)
    requires a >= 0
    ensures count >= 0
    ensures count == CountOnesInOctal(a)
// </vc-spec>
// <vc-code>
{
    lemma_CountOnesInOctalNonNegative(a);
    return CountOnesInOctal(a);
}
// </vc-code>

