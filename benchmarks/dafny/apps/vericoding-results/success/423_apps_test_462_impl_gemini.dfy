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
lemma MinTotalDistanceProperties(x1: int, x2: int, x3: int)
    requires ValidInput(x1, x2, x3)
    ensures MinTotalDistance(x1, x2, x3) >= 1
    ensures MinTotalDistance(x1, x2, x3) <= 99
{
    var max_pos := if x1 >= x2 && x1 >= x3 then x1 else if x2 >= x1 && x2 >= x3 then x2 else x3;
    var min_pos := if x1 <= x2 && x1 <= x3 then x1 else if x2 <= x1 && x2 <= x3 then x2 else x3;

    assert MinTotalDistance(x1, x2, x3) == max_pos - min_pos;

    // Establish that max_pos and min_pos are chosen from the inputs
    assert max_pos in {x1, x2, x3};
    assert min_pos in {x1, x2, x3};

    // Prove the lower bound: result >= 1
    // This relies on the inputs being distinct.
    if max_pos == min_pos {
        // If max and min are equal, all inputs must be equal to that value.
        assert x1 == max_pos;
        assert x2 == max_pos;
        assert x3 == max_pos;
        assert x1 == x2 && x2 == x3;
        assert false; // This contradicts the precondition x1 != x2.
    }
    assert max_pos > min_pos;
    assert max_pos - min_pos >= 1;

    // Prove the upper bound: result <= 99
    // This relies on the range of the inputs [1, 100].
    assert 1 <= min_pos <= max_pos <= 100;
    assert max_pos - min_pos <= 100 - 1;
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
  var max_pos: int;
  var min_pos: int;

  if x1 >= x2 && x1 >= x3 {
    max_pos := x1;
  } else if x2 >= x1 && x2 >= x3 {
    max_pos := x2;
  } else {
    max_pos := x3;
  }

  if x1 <= x2 && x1 <= x3 {
    min_pos := x1;
  } else if x2 <= x1 && x2 <= x3 {
    min_pos := x2;
  } else {
    min_pos := x3;
  }

  result := max_pos - min_pos;
  MinTotalDistanceProperties(x1, x2, x3);
}
// </vc-code>

