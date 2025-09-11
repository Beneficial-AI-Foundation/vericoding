// <vc-preamble>
predicate ValidInput(R: int, G: int) {
    0 <= R <= 4500 && 0 <= G <= 4500
}

function RequiredPerformance(R: int, G: int): int {
    2 * G - R
}

predicate CorrectResult(R: int, G: int, P: int) {
    (R + P) == 2 * G
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(R: int, G: int) returns (result: int)
    requires ValidInput(R, G)
    ensures result == RequiredPerformance(R, G)
    ensures CorrectResult(R, G, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
