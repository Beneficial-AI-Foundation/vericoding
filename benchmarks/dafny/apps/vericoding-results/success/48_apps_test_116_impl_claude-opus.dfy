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
lemma IntersectionSizeNonNegative(l1: int, r1: int, l2: int, r2: int)
    ensures IntersectionSize(l1, r1, l2, r2) >= 0
{
    var left := IntersectionLeft(l1, l2);
    var right := IntersectionRight(r1, r2);
    if right - left + 1 > 0 {
        assert IntersectionSize(l1, r1, l2, r2) == right - left + 1;
        assert IntersectionSize(l1, r1, l2, r2) >= 0;
    } else {
        assert IntersectionSize(l1, r1, l2, r2) == 0;
        assert IntersectionSize(l1, r1, l2, r2) >= 0;
    }
}

lemma ExpectedResultNonNegative(l1: int, r1: int, l2: int, r2: int, k: int)
    ensures ExpectedResult(l1, r1, l2, r2, k) >= 0
{
    IntersectionSizeNonNegative(l1, r1, l2, r2);
    var intersection_size := IntersectionSize(l1, r1, l2, r2);
    if KInIntersection(l1, r1, l2, r2, k) {
        if intersection_size - 1 > 0 {
            assert ExpectedResult(l1, r1, l2, r2, k) == intersection_size - 1;
            assert ExpectedResult(l1, r1, l2, r2, k) >= 0;
        } else {
            assert ExpectedResult(l1, r1, l2, r2, k) == 0;
            assert ExpectedResult(l1, r1, l2, r2, k) >= 0;
        }
    } else {
        assert ExpectedResult(l1, r1, l2, r2, k) == intersection_size;
        assert ExpectedResult(l1, r1, l2, r2, k) >= 0;
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
    var left := if l1 > l2 then l1 else l2;
    var right := if r1 < r2 then r1 else r2;
    
    var intersection_size := if right - left + 1 > 0 then right - left + 1 else 0;
    
    if left <= k <= right {
        result := if intersection_size - 1 > 0 then intersection_size - 1 else 0;
    } else {
        result := intersection_size;
    }
    
    assert left == IntersectionLeft(l1, l2);
    assert right == IntersectionRight(r1, r2);
    assert intersection_size == IntersectionSize(l1, r1, l2, r2);
    assert (left <= k <= right) == KInIntersection(l1, r1, l2, r2, k);
    assert result == ExpectedResult(l1, r1, l2, r2, k);
    
    ExpectedResultNonNegative(l1, r1, l2, r2, k);
}
// </vc-code>

