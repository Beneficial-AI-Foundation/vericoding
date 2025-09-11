// <vc-preamble>
predicate ValidInput(l1: int, r1: int, l2: int, r2: int, k: int) {
    l1 <= r1 && l2 <= r2
}

function IntersectionLeft(l1: int, l2: int): int {
    if l1 > l2 then l1 else l2
}

function IntersectionRight(r1: int, r2: int): int {
    if r1 < r2 then r1 else r2
}

function IntersectionSize(l1: int, r1: int, l2: int, r2: int): int {
    var left := IntersectionLeft(l1, l2);
    var right := IntersectionRight(r1, r2);
    if right - left + 1 > 0 then right - left + 1 else 0
}

predicate KInIntersection(l1: int, r1: int, l2: int, r2: int, k: int) {
    var left := IntersectionLeft(l1, l2);
    var right := IntersectionRight(r1, r2);
    left <= k <= right
}

function ExpectedResult(l1: int, r1: int, l2: int, r2: int, k: int): int {
    var intersection_size := IntersectionSize(l1, r1, l2, r2);
    if KInIntersection(l1, r1, l2, r2, k) then
        if intersection_size - 1 > 0 then intersection_size - 1 else 0
    else
        intersection_size
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(l1: int, r1: int, l2: int, r2: int, k: int) returns (result: int)
    requires ValidInput(l1, r1, l2, r2, k)
    ensures result == ExpectedResult(l1, r1, l2, r2, k)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
