// <vc-preamble>
predicate ValidInput(r: int, g: int, b: int) {
    r >= 0 && g >= 0 && b >= 0
}

function MaxTables(r: int, g: int, b: int): int
    requires ValidInput(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

function min(a: int, b: int): int {
    if a <= b then a else b
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(r: int, g: int, b: int) returns (result: int)
    requires ValidInput(r, g, b)
    ensures result == MaxTables(r, g, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
