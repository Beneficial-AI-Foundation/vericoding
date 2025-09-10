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
lemma MinDaysOffLemma(n: int)
  requires ValidInput(n)
  ensures MinDaysOff(n) == 2 * (n / 7) + (if n % 7 > 5 then n % 7 - 5 else 0)
{
}

lemma MaxDaysOffLemma(n: int)
  requires ValidInput(n)
  ensures MaxDaysOff(n) == 2 * (n / 7) + (if n % 7 < 2 then n % 7 else 2)
{
}

lemma DaysOffBounds(n: int)
  requires ValidInput(n)
  ensures 0 <= MinDaysOff(n) <= MaxDaysOff(n) <= n
  ensures MinDaysOff(n) % 2 == 0
  ensures MaxDaysOff(n) % 2 == 0 || MaxDaysOff(n) % 2 == 1
{
  var completeWeeks := n / 7;
  var remainingDays := n % 7;
  
  // MinDaysOff bounds
  assert 2 * completeWeeks >= 0;
  assert (if remainingDays > 5 then remainingDays - 5 else 0) >= 0;
  assert 2 * completeWeeks + (if remainingDays > 5 then remainingDays - 5 else 0) <= n;
  
  // MaxDaysOff bounds
  assert 2 * completeWeeks >= 0;
  assert (if remainingDays < 2 then remainingDays else 2) >= 0;
  assert 2 * completeWeeks + (if remainingDays < 2 then remainingDays else 2) <= n;
  
  // Min <= Max
  assert (if remainingDays > 5 then remainingDays - 5 else 0) <= (if remainingDays < 2 then remainingDays else 2);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
// </vc-spec>
// <vc-code>
{
  var completeWeeks := n / 7;
  var remainingDays := n % 7;
  var minDays := 2 * completeWeeks + (if remainingDays > 5 then remainingDays - 5 else 0);
  var maxDays := 2 * completeWeeks + (if remainingDays < 2 then remainingDays else 2);
  result := [minDays, maxDays];
}
// </vc-code>

