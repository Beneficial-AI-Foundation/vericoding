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
lemma IntersectionLeftLemma(l1: int, l2: int)
  ensures IntersectionLeft(l1, l2) == (if l1 > l2 then l1 else l2)
{
}

lemma IntersectionRightLemma(r1: int, r2: int)
  ensures IntersectionRight(r1, r2) == (if r1 < r2 then r1 else r2)
{
}

lemma IntersectionSizeLemma(l1: int, r1: int, l2: int, r2: int)
  ensures IntersectionSize(l1, r1, l2, r2) == (
    var left := IntersectionLeft(l1, l2);
    var right := IntersectionRight(r1, r2);
    if right - left + 1 > 0 then right - left + 1 else 0
  )
{
  var left := IntersectionLeft(l1, l2);
  var right := IntersectionRight(r1, r2);
  calc {
    var res := IntersectionSize(l1, r1, l2, r2);
    res;
  }
}

lemma KInIntersectionLemma(l1: int, r1: int, l2: int, r2: int, k: int)
  ensures KInIntersection(l1, r1, l2, r2, k) == (
    var left := IntersectionLeft(l1, l2);
    var right := IntersectionRight(r1, r2);
    left <= k <= right
  )
{
  var left := IntersectionLeft(l1, l2);
  var right := IntersectionRight(r1, r2);
  calc {
    var res := KInIntersection(l1, r1, l2, r2, k);
    res;
  }
}

lemma ExpectedResultLemma(l1: int, r1: int, l2: int, r2: int, k: int)
    ensures ExpectedResult(l1, r1, l2, r2, k) == (
        var intersection_size := IntersectionSize(l1, r1, l2, r2);
        if KInIntersection(l1, r1, l2, r2, k) then
            if intersection_size - 1 > 0 then intersection_size - 1 else 0
        else
            intersection_size
    )
{
    var intersection_size := IntersectionSize(l1, r1, l2, r2);
    if KInIntersection(l1, r1, l2, r2, k) {
        if intersection_size - 1 > 0 {
             assert ExpectedResult(l1,r1,l2,r2,k) == intersection_size - 1;
        } else {
             assert ExpectedResult(l1,r1,l2,r2,k) == 0;
        }
    } else {
        assert ExpectedResult(l1,r1,l2,r2,k) == intersection_size;
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
    var left_intersect := IntersectionLeft(l1, l2);
    var right_intersect := IntersectionRight(r1, r2);

    var current_intersection_size := 0;
    if right_intersect - left_intersect + 1 > 0 {
        current_intersection_size := right_intersect - left_intersect + 1;
    }

    var k_in_intersection := false;
    if left_intersect <= k && k <= right_intersect {
        k_in_intersection := true;
    }

    if k_in_intersection {
        if current_intersection_size - 1 > 0 {
            result := current_intersection_size - 1;
        } else {
            result := 0;
        }
    } else {
        result := current_intersection_size;
    }

    // Proofs that intermediate variables match function definitions
    IntersectionLeftLemma(l1, l2);
    IntersectionRightLemma(r1, r2);
    IntersectionSizeLemma(l1, r1, l2, r2);
    KInIntersectionLemma(l1, r1, l2, r2, k);
    ExpectedResultLemma(l1, r1, l2, r2, k);

    // Relate method result to ExpectedResult
    var expected_size_check := IntersectionSize(l1,r1,l2,r2);
    var k_in_intersection_check := KInIntersection(l1,r1,l2,r2,k);

    if k_in_intersection_check {
        if expected_size_check - 1 > 0 {
            assert result == expected_size_check - 1;
        } else {
            assert result == 0;
        }
    } else {
        assert result == expected_size_check;
    }

}
// </vc-code>

