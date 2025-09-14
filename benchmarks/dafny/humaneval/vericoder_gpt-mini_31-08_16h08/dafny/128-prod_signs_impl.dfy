function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
  ensures x >= 0 ==> abs(x) == x
  ensures x < 0 ==> abs(x) == -x
{
  if x >= 0 then x else -x
}
function sum_abs(s: seq<int>) : int
  ensures sum_abs(s) >= 0
{
  if |s| == 0 then 0 else abs(s[0]) + sum_abs(s[1..])
}

// <vc-helpers>
lemma AbsNeg(x: int)
  requires x >= 0
  ensures abs(-x) == x
{
  if x == 0 {
    assert -x >= 0;
    assert abs(-x) == -x;
    assert -x == x;
  } else {
    assert x > 0;
    assert -x < 0;
    assert abs(-x) == -(-x);
    assert -(-x) == x;
  }
}
// </vc-helpers>

// <vc-spec>
method prod_signs(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
// </vc-spec>
// <vc-code>
{
  var total := sum_abs(numbers);
  var negCount := |set i | 0 <= i < |numbers| && numbers[i] < 0|;
  assert total >= 0;
  if negCount % 2 == 1 {
    AbsNeg(total);
    s := -total;
  } else {
    s := total;
  }
}
// </vc-code>

