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
lemma MinMaxProps(n: int)
  requires ValidInput(n)
  ensures MinDaysOff(n) >= 0
  ensures MaxDaysOff(n) >= 0
  ensures MinDaysOff(n) <= MaxDaysOff(n)
  ensures MinDaysOff(n) <= n
  ensures MaxDaysOff(n) <= n
{
  var c := n / 7;
  var r := n % 7;

  assert 0 <= r;
  assert r < 7;
  assert c >= 0;

  var minAdd := if r > 5 then r - 5 else 0;
  var maxAdd := if r < 2 then r else 2;

  assert MinDaysOff(n) == 2 * c + minAdd;
  assert MaxDaysOff(n) == 2 * c + maxAdd;

  assert 2 * c >= 0;
  assert minAdd >= 0;
  assert maxAdd >= 0;
  assert MinDaysOff(n) >= 0;
  assert MaxDaysOff(n) >= 0;

  if r < 2 {
    assert minAdd == 0;
    assert maxAdd == r;
  } else if r <= 5 {
    assert 2 <= r;
    assert r <= 5;
    assert minAdd == 0;
    assert maxAdd == 2;
  } else {
    assert r == 6;
    assert minAdd == 1;
    assert maxAdd == 2;
  }
  assert minAdd <= maxAdd;
  assert MinDaysOff(n) <= MaxDaysOff(n);

  assert n == 7 * c + r;

  assert n - MaxDaysOff(n) == 7 * c + r - (2 * c + maxAdd);
  assert n - MaxDaysOff(n) == 5 * c + (r - maxAdd);
  if r < 2 {
    assert r - maxAdd == 0;
  } else {
    assert r >= 2;
    assert maxAdd == 2;
    assert r - maxAdd >= 0;
  }
  assert 5 * c >= 0;
  assert n - MaxDaysOff(n) >= 0;
  assert MaxDaysOff(n) <= n;

  assert n - MinDaysOff(n) == 7 * c + r - (2 * c + minAdd);
  assert n - MinDaysOff(n) == 5 * c + (r - minAdd);
  if r <= 5 {
    assert minAdd == 0;
    assert r - minAdd == r;
    assert r - minAdd >= 0;
  } else {
    assert r == 6;
    assert minAdd == 1;
    assert r - minAdd == 5;
    assert r - minAdd >= 0;
  }
  assert n - MinDaysOff(n) >= 0;
  assert MinDaysOff(n) <= n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
// </vc-spec>
// <vc-code>
{
  MinMaxProps(n);
  result := [MinDaysOff(n), MaxDaysOff(n)];
}
// </vc-code>

