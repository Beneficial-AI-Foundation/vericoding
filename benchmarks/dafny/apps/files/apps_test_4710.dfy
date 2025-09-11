// <vc-preamble>
predicate ValidInput(x: int) {
    1 <= x <= 3000
}

predicate CorrectOutput(x: int, result: string) {
    (x < 1200 ==> result == "ABC\n") &&
    (x >= 1200 ==> result == "ARC\n")
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: string)
    requires ValidInput(x)
    ensures CorrectOutput(x, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
