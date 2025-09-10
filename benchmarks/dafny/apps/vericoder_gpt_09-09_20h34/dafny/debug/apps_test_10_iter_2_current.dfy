predicate ValidInput(n: int)
{
  n >= 1
}

function MinDaysOff(n: int): int
  requires ValidInput(n)
{
  var completeWeeks := n / 7;
  var remainingDays := n % 7;
  var minAdditional := if remainingDays > 5 then remainingDays - 5 else 0;
  2 * completeWeeks + minAdditional
}

function MaxDaysOff(n: int): int
  requires ValidInput(n)
{
  var completeWeeks := n / 7;
  var remainingDays := n % 7;
  var maxAdditional := if remainingDays < 2 then remainingDays else 2;
  2 * completeWeeks + maxAdditional
}

predicate ValidOutput(result: seq<int>, n: int)
  requires ValidInput(n)
{
  |result| == 2 &&
  result[0] >= 0 && result[1] >= 0 &&
  result[0] <= result[1] &&
  result[0] <= n && result[1] <= n &&
  result[0] == MinDaysOff(n) &&
  result[1] == MaxDaysOff(n)
}

// <vc-helpers>
lemma MinMaxProperties(n: int)
  requires ValidInput(n)
  ensures MinDaysOff(n) >= 0
  ensures MaxDaysOff(n) >= 0
  ensures MinDaysOff(n) <= MaxDaysOff(n)
  ensures MinDaysOff(n) <= n
  ensures MaxDaysOff(n) <= n
{
  var q := n / 7;
  var r := n % 7;
  assert 0 <= r < 7;
  assert n == 7 * q + r;

  // q >= 0
  if q < 0 {
    assert 7 * q <= -7;
    assert r <= 6;
    assert 7 * q + r <= -1;
    assert n == 7 * q + r;
    assert n <= -1;
    assert n >= 1;
    assert false;
  }
  assert q >= 0;

  // Expand function bodies
  assert MinDaysOff(n) == 2 * q + (if r > 5 then r - 5 else 0);
  assert MaxDaysOff(n) == 2 * q + (if r < 2 then r else 2);

  // Non-negativity
  if r > 5 {
    assert r - 5 >= 1;
  }
  assert (if r > 5 then r - 5 else 0) >= 0;
  assert MinDaysOff(n) >= 0;

  if r < 2 {
    assert r >= 0;
  } else {
    assert 2 >= 0;
  }
  assert MaxDaysOff(n) >= 0;

  // MinDaysOff <= MaxDaysOff
  if r < 2 {
    assert (if r > 5 then r - 5 else 0) == 0;
    assert (if r < 2 then r else 2) == r;
    assert 0 <= r;
  } else if r <= 5 {
    assert (if r > 5 then r - 5 else 0) == 0;
    assert (if r < 2 then r else 2) == 2;
    assert 0 <= 2;
  } else {
    assert r == 6;
    assert (if r > 5 then r - 5 else 0) == 1;
    assert (if r < 2 then r else 2) == 2;
    assert 1 <= 2;
  }
  assert MinDaysOff(n) <= MaxDaysOff(n);

  // MinDaysOff <= n
  var tMin := if r > 5 then r - 5 else 0;
  if r <= 5 {
    assert tMin == 0;
    assert r - tMin == r;
    assert r - tMin >= 0;
  } else {
    assert r == 6;
    assert tMin == 1;
    assert r - tMin == 5;
    assert r - tMin >= 0;
  }
  assert n - MinDaysOff(n) == (7 * q + r) - (2 * q + tMin);
  assert n - MinDaysOff(n) == 5 * q + (r - tMin);
  assert 0 <= 5 * q;
  assert n - MinDaysOff(n) >= 0;
  assert MinDaysOff(n) <= n;

  // MaxDaysOff <= n
  var tMax := if r < 2 then r else 2;
  if r < 2 {
    assert tMax == r;
    assert r - tMax == 0;
    assert r - tMax >= 0;
  } else {
    assert r >= 2;
    assert tMax == 2;
    assert r - tMax >= 0;
  }
  assert n - MaxDaysOff(n) == (7 * q + r) - (2 * q + tMax);
  assert n - MaxDaysOff(n) == 5 * q + (r - tMax);
  assert 0 <= 5 * q;
  assert n - MaxDaysOff(n) >= 0;
  assert MaxDaysOff(n) <= n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
// </vc-spec>
// <vc-code>
{
  MinMaxProperties(n);
  result := [MinDaysOff(n), MaxDaysOff(n)];
}
// </vc-code>

