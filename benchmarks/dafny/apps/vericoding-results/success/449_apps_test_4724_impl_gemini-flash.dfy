predicate ValidInput(R: int, G: int) {
    0 <= R <= 4500 && 0 <= G <= 4500
}

function RequiredPerformance(R: int, G: int): int {
    2 * G - R
}

predicate CorrectResult(R: int, G: int, P: int) {
    (R + P) == 2 * G
}

// <vc-helpers>
lemma Lemma_RequiredPerformance_CorrectResult(R: int, G: int)
    requires ValidInput(R, G)
    ensures CorrectResult(R, G, RequiredPerformance(R, G))
{
    // CorrectResult(R, G, P) is (R + P) == 2 * G
    // RequiredPerformance(R, G) is 2 * G - R
    // We need to show (R + (2 * G - R)) == 2 * G
    // R + 2 * G - R simplifies to 2 * G
    // So 2 * G == 2 * G, which is true.
}
// </vc-helpers>

// <vc-spec>
method solve(R: int, G: int) returns (result: int)
    requires ValidInput(R, G)
    ensures result == RequiredPerformance(R, G)
    ensures CorrectResult(R, G, result)
// </vc-spec>
// <vc-code>
{
    var P := RequiredPerformance(R, G);
    Lemma_RequiredPerformance_CorrectResult(R, G);
    return P;
}
// </vc-code>

