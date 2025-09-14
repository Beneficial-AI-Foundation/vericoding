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

// <vc-helpers>
lemma MinTotalDistanceLemma(x1: int, x2: int, x3: int)
    requires ValidInput(x1, x2, x3)
    ensures MinTotalDistance(x1, x2, x3) >= 1 && MinTotalDistance(x1, x2, x3) <= 99
{
    var max_pos := if x1 >= x2 && x1 >= x3 then x1
                  else if x2 >= x1 && x2 >= x3 then x2
                  else x3;
    var min_pos := if x1 <= x2 && x1 <= x3 then x1
                  else if x2 <= x1 && x2 <= x3 then x2
                  else x3;
    
    // Show that the difference is at least 1
    // Since all values are distinct integers, the maximum must be at least min_pos + 1
    if max_pos == x1 {
        if min_pos == x2 {
            assert x1 != x2;
            assert x1 > x2;
        } else if min_pos == x3 {
            assert x1 != x3;
            assert x1 > x3;
        }
    } else if max_pos == x2 {
        if min_pos == x1 {
            assert x2 != x1;
            assert x2 > x1;
        } else if min_pos == x3 {
            assert x2 != x3;
            assert x2 > x3;
        }
    } else {
        if min_pos == x1 {
            assert x3 != x1;
            assert x3 > x1;
        } else if min_pos == x2 {
            assert x3 != x2;
            assert x3 > x2;
        }
    }
    assert max_pos - min_pos >= 1;
    
    // Show that the difference is at most 99
    // The maximum possible difference between two values in [1, 100] is 100 - 1 = 99
    assert max_pos <= 100;
    assert min_pos >= 1;
    // Since max_pos - min_pos is an integer, the maximum value is 99
    assert max_pos - min_pos <= 99;
}
// </vc-helpers>

// <vc-spec>
method FindMinimumTotalDistance(x1: int, x2: int, x3: int) returns (result: int)
    requires ValidInput(x1, x2, x3)
    ensures result == MinTotalDistance(x1, x2, x3)
    ensures result >= 1 && result <= 99
// </vc-spec>
// <vc-code>
{
    result := MinTotalDistance(x1, x2, x3);
    MinTotalDistanceLemma(x1, x2, x3);
}
// </vc-code>

