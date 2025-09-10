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
lemma MinTotalDistanceBounds(x1: int, x2: int, x3: int)
    requires ValidInput(x1, x2, x3)
    ensures 1 <= MinTotalDistance(x1, x2, x3) <= 99
{
    var max_pos := if x1 >= x2 && x1 >= x3 then x1
                  else if x2 >= x1 && x2 >= x3 then x2
                  else x3;
    var min_pos := if x1 <= x2 && x1 <= x3 then x1
                  else if x2 <= x1 && x2 <= x3 then x2
                  else x3;
    
    // max_pos is one of x1, x2, x3, so it's between 1 and 100
    assert max_pos == x1 || max_pos == x2 || max_pos == x3;
    assert 1 <= max_pos <= 100;
    
    // min_pos is one of x1, x2, x3, so it's between 1 and 100
    assert min_pos == x1 || min_pos == x2 || min_pos == x3;
    assert 1 <= min_pos <= 100;
    
    // Since x1, x2, x3 are all distinct, max_pos != min_pos
    assert max_pos != min_pos;
    assert max_pos > min_pos;
    
    // Therefore the difference is at least 1
    assert max_pos - min_pos >= 1;
    
    // And at most 99 (100 - 1)
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
    var max_pos := if x1 >= x2 && x1 >= x3 then x1
                  else if x2 >= x1 && x2 >= x3 then x2
                  else x3;
    var min_pos := if x1 <= x2 && x1 <= x3 then x1
                  else if x2 <= x1 && x2 <= x3 then x2
                  else x3;
    
    result := max_pos - min_pos;
    
    MinTotalDistanceBounds(x1, x2, x3);
}
// </vc-code>

