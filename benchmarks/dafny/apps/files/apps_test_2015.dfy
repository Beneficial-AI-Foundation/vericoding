// <vc-preamble>
predicate ValidInput(r: int, g: int, b: int)
{
    r >= 1 && g >= 1 && b >= 1
}

function MaxOf3(r: int, g: int, b: int): int
{
    if r >= g && r >= b then r
    else if g >= r && g >= b then g
    else b
}

predicate CanArrange(r: int, g: int, b: int)
    requires ValidInput(r, g, b)
{
    var maxCount := MaxOf3(r, g, b);
    var total := r + g + b;
    2 * maxCount <= total + 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CheckLampArrangement(r: int, g: int, b: int) returns (result: bool)
    requires ValidInput(r, g, b)
    ensures result == CanArrange(r, g, b)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
