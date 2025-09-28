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
function min3(a: int, b: int, c: int): int { min(a, min(b, c)) }
// </vc-helpers>

// <vc-spec>
method solve(r: int, g: int, b: int) returns (result: int)
    requires ValidInput(r, g, b)
    ensures result == MaxTables(r, g, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := min3((r + g + b) / 3, r + g, r + b);
  result := min(result, g + b);
}
// </vc-code>
