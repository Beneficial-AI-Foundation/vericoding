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
  assert 0 <= r;
  assert r < 7;
  assert n == 7 * q + r;

  // Show q >= 0
  if q < 0 {
    assert 7 * q <= -7;
    assert r <= 6;
    assert 7 * q + r <= -1;
    assert n <= -1;
    assert n >= 1;
    assert false;
  }
  assert q >= 0;

  // Unfold function bodies
  assert MinDaysOff(n) == 2 * q + (if r > 5 then r - 5 else 0);
  assert MaxDaysOff(n) == 2 * q + (if r < 2 then r else 2);

  // Non-negativity
  if r
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
// </vc-spec>
// <vc-code>
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
  assert 0 <= r;
  assert r < 7;
  assert n == 7 * q + r;

  // Show q >= 0
  if q < 0 {
    assert 7 * q <= -7;
    assert r <= 6;
    assert 7 * q + r <= -1;
    assert n <= -1;
    assert n >= 1;
    assert false;
  }
  assert q >= 0;

  // Unfold function bodies
  assert MinDaysOff(n) == 2 * q + (if r > 5 then r - 5 else 0);
  assert MaxDaysOff(n) == 2 * q + (if r < 2 then r else 2);

  // Non-negativity
  if r
// </vc-code>

