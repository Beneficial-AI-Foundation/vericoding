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

// <vc-helpers>
lemma KInIntersectionImpliesNonEmpty(l1: int, r1: int, l2: int, r2: int, k: int)
    requires KInIntersection(l1, r1, l2, r2, k)
    ensures IntersectionSize(l1, r1, l2, r2) > 0
{
    var left := IntersectionLeft(l1, l2);
    var right := IntersectionRight(r1, r2);
    assert left <= k <= right;
    calc {
        IntersectionSize(l1, r1, l2, r2);
        == { definition of IntersectionSize }
        if right - left + 1 > 0 then right - left + 1 else 0;
        == { right - left + 1 >= 1 > 0 }
        right - left + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(l1: int, r1: int, l2: int, r2: int, k: int) returns (result: int)
    requires ValidInput(l1, r1, l2, r2, k)
    ensures result == ExpectedResult(l1, r1, l2, r2, k)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var inter_size := IntersectionSize(l1, r1, l2, r2);
    if KInIntersection(l1, r1, l2, r2, k) then {
        KInIntersectionImpliesNonEmpty(l1, r1, l2, r2, k);
        if inter_size - 1 > 0 then
            result := inter_size - 1;
        else
            result := 0;
    } else {
        result := inter_size;
    }
}
// </vc-code>

