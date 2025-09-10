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
lemma IntersectionLeftLemma(l1: int, l2: int, k: int)
  ensures (l1 > l2 ==> IntersectionLeft(l1, l2) == l1)
  ensures (l1 <= l2 ==> IntersectionLeft(l1, l2) == l2)
{
}

lemma IntersectionRightLemma(r1: int, r2: int, k: int)
  ensures (r1 < r2 ==> IntersectionRight(r1, r2) == r1)
  ensures (r1 >= r2 ==> IntersectionRight(r1, r2) == r2)
{
}

lemma IntersectionSizeLemma(l1: int, r1: int, l2: int, r2: int)
  ensures IntersectionSize(l1, r1, l2, r2) == (
    var left := IntersectionLeft(l1, l2);
    var right := IntersectionRight(r1, r2);
    if right - left + 1 > 0 then right - left + 1 else 0
  )
{
}

lemma KInIntersectionLemma(l1: int, r1: int, l2: int, r2: int, k: int)
  ensures KInIntersection(l1, r1, l2, r2, k) == (
    var left := IntersectionLeft(l1, l2);
    var right := IntersectionRight(r1, r2);
    left <= k <= right
  )
{
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
    var left_intersect := IntersectionLeft(l1, l2);
    var right_intersect := IntersectionRight(r1, r2);

    var current_intersection_size := 0;
    if right_intersect - left_intersect + 1 > 0 then
        current_intersection_size := right_intersect - left_intersect + 1;

    var k_in_intersection := false;
    if left_intersect <= k && k <= right_intersect then
        k_in_intersection := true;

    if k_in_intersection then
        if current_intersection_size - 1 > 0 then
            result := current_intersection_size - 1;
        else
            result := 0;
    else
        result := current_intersection_size;

    // Proofs that intermediate variables match function definitions
    IntersectionLeftLemma(l1, l2, k);
    IntersectionRightLemma(r1, r2, k);
    IntersectionSizeLemma(l1, r1, l2, r2);
    KInIntersectionLemma(l1, r1, l2, r2, k);
}
// </vc-code>

