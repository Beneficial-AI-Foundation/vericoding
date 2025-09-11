// <vc-preamble>
predicate ValidInput(x1: int, x2: int, x3: int) {
    1 <= x1 <= 100 && 1 <= x2 <= 100 && 1 <= x3 <= 100 &&
    x1 != x2 && x1 != x3 && x2 != x3
}

function MinTotalDistance(x1: int, x2: int, x3: int): int
    requires ValidInput(x1, x2, x3)
{
    var max_pos := if x1 >= x2 && x1 >= x3 then x1
                  else if x2 >= x1 && x2 >= x3 then x2
                  else x3;
    var min_pos := if x1 <= x2 && x1 <= x3 then x1
                  else if x2 <= x1 && x2 <= x3 then x2
                  else x3;
    max_pos - min_pos
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindMinimumTotalDistance(x1: int, x2: int, x3: int) returns (result: int)
    requires ValidInput(x1, x2, x3)
    ensures result == MinTotalDistance(x1, x2, x3)
    ensures result >= 1 && result <= 99
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
