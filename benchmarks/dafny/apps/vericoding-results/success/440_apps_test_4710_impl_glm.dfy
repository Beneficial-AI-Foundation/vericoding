predicate ValidInput(x: int) {
    1 <= x <= 3000
}

predicate CorrectOutput(x: int, result: string) {
    (x < 1200 ==> result == "ABC\n") &&
    (x >= 1200 ==> result == "ARC\n")
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: string)
    requires ValidInput(x)
    ensures CorrectOutput(x, result)
// </vc-spec>
// <vc-code>
{
    return if x < 1200 then "ABC\n" else "ARC\n";
}
// </vc-code>

