predicate ValidInput(m: int, d: int)
{
    1 <= m <= 12 && 1 <= d <= 7
}

function DaysInMonth(m: int): int
    requires 1 <= m <= 12
{
    [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m-1]
}

function ColumnsNeeded(m: int, d: int): int
    requires ValidInput(m, d)
{
    1 + (d - 1 + DaysInMonth(m) - 1) / 7
}

// <vc-helpers>
lemma DaysInMonth_bounds(m: int)
  requires 1 <= m <= 12
  ensures 28 <= DaysInMonth(m) <= 31
{
  var v := DaysInMonth(m);
  if m == 2 {
    assert v == 28;
  } else if m == 4 || m == 6 || m == 9 || m == 11 {
    assert v == 30;
  } else {
    assert v == 31;
  }
}

lemma ColumnsNeeded_range(m: int, d: int)
  requires ValidInput(m, d)
  ensures 4 <= ColumnsNeeded(m, d) <= 6
{
  DaysInMonth_bounds(m);
  var days := DaysInMonth(m);
  var num := d + days - 2; // equals d-1 + days-1
  // min: d=1, days=28 -> num = 27; max: d=7, days=31 -> num = 36
  assert num >= 27;
  assert num <= 36;
  // integer division by 7 yields between 3 and 5
  assert num / 7 >= 27 / 7;
  assert num / 7 <= 36 / 7;
  // 27/7 == 3 and 36/7 == 5 in integer division
  assert 1 + num / 7 >= 4;
  assert 1 + num / 7 <= 6;
}
// </vc-helpers>

// <vc-spec>
method solve(m: int, d: int) returns (result: int)
    requires ValidInput(m, d)
    ensures result == ColumnsNeeded(m, d)
    ensures 4 <= result <= 6
// </vc-spec>
// <vc-code>
{
  result := ColumnsNeeded(m, d);
  ColumnsNeeded_range(m, d);
}
// </vc-code>

