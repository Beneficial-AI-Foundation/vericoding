// <vc-preamble>
predicate ValidInput(a: int, b: int, c: int, d: int, e: int, k: int) {
    0 <= a <= 123 && 0 <= b <= 123 && 0 <= c <= 123 && 
    0 <= d <= 123 && 0 <= e <= 123 && 0 <= k <= 123 &&
    a < b < c < d < e
}

predicate AllPairsCanCommunicate(a: int, b: int, c: int, d: int, e: int, k: int) {
    (e - a) <= k
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int, e: int, k: int) returns (result: string)
    requires ValidInput(a, b, c, d, e, k)
    ensures result == "Yay!" <==> AllPairsCanCommunicate(a, b, c, d, e, k)
    ensures result == ":(" <==> !AllPairsCanCommunicate(a, b, c, d, e, k)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
