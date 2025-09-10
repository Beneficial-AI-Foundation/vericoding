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
function Max(a: int, b: int): int {
    if a >= b then a else b
}

function Min(a: int, b: int): int {
    if a <= b then a else b
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
    var max_val := Max(Max(x1, x2), x3);
    var min_val := Min(Min(x1, x2), x3);
    result := max_val - min_val;

    // Proofs for the maximum and minimum values against the original definition
    assert max_val == (if x1 >= x2 && x1 >= x3 then x1
                      else if x2 >= x1 && x2 >= x3 then x2
                      else x3);
    assert min_val == (if x1 <= x2 && x1 <= x3 then x1
                      else if x2 <= x1 && x2 <= x3 then x2
                      else x3);

    // Proof for the postconditions
    assert min_val >= 1;
    assert max_val <= 100;
    assert min_val < max_val by (
      duplicate(x1, x2, x3);
      if x1 == min_val {
        assert x2 != x1; assert x3 != x1;
        assert x2 > x1 || x3 > x1;
        if x2 == max_val { assert x2 > x1; }
        if x3 == max_val { assert x3 > x1; }
      } else if x2 == min_val {
        assert x1 != x2; assert x3 != x2;
        assert x1 > x2 || x3 > x2;
        if x1 == max_val { assert x1 > x2; }
        if x3 == max_val { assert x3 > x2; }
      } else { // x3 == min_val
        assert x1 != x3; assert x2 != x3;
        assert x1 > x3 || x2 > x3;
        if x1 == max_val { assert x1 > x3; }
        if x2 == max_val { assert x2 > x3; }
      }
    );
    assert result == MinTotalDistance(x1, x2, x3);
    assert result >= 1 && result <= 99;
}
// </vc-code>

