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
// No helper lemmas needed for this proof.
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

  // input range facts
  assert 1 <= x1 && x1 <= 100;
  assert 1 <= x2 && x2 <= 100;
  assert 1 <= x3 && x3 <= 100;

  // max/min are one of the inputs, hence within range
  assert 1 <= max_pos && max_pos <= 100;
  assert 1 <= min_pos && min_pos <= 100;

  // max_pos is >= each xi, min_pos is <= each xi
  assert max_pos >= x1 && max_pos >= x2 && max_pos >= x3;
  assert min_pos <= x1 && min_pos <= x2 && min_pos <= x3;

  // show max_pos > min_pos (strict because all inputs are pairwise distinct)
  if max_pos == min_pos {
    // if max == min then for each xi we have max >= xi and min <= xi,
    // and with max==min this forces xi == max for all i, contradicting distinctness
    assert max_pos >= x1 && min_pos <= x1;
    assert x1 == max_pos;
    assert max_pos >= x2 && min_pos <= x2;
    assert x2 == max_pos;
    assert max_pos >= x3 && min_pos <= x3;
    assert x3 == max_pos;
    // contradicts the precondition that values are pairwise distinct
    assert x1 != x2;
    assert false;
  }
  assert max_pos > min_pos;

  result := max_pos - min_pos;

  // final bounds
  assert 1 <= result && result <= 99;
}
// </vc-code>

