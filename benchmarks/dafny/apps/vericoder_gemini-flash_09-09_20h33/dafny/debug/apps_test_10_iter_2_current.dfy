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
lemma CalculateMinMaxDaysOff(n: int)
  requires ValidInput(n)
  ensures MinDaysOff(n) <= n
  ensures MaxDaysOff(n) <= n
{
  var completeWeeks := n / 7;
  var remainingDays := n % 7;

  // Proof for MinDaysOff(n) <= n
  // MinDaysOff is 2 * completeWeeks + minAdditional
  // where minAdditional is (remainingDays - 5) if remainingDays > 5, else 0
  // n = 7 * completeWeeks + remainingDays

  // Case 1: remainingDays <= 5
  // minAdditional = 0
  // MinDaysOff(n) = 2 * completeWeeks
  // We want to show 2 * completeWeeks <= n
  // 2 * completeWeeks = 2 * (n / 7)
  // Since n / 7 <= n / 2 for n >= 1 (as 7 >= 2)
  // And 2 * (n / 7) <= n when n >= 0 (as 2/7 <= 1)
  // So, 2 * completeWeeks <= n holds.

  // Case 2: remainingDays > 5 (i.e., remainingDays is 6)
  // minAdditional = remainingDays - 5 = 6 - 5 = 1
  // MinDaysOff(n) = 2 * completeWeeks + 1
  // We want to show 2 * completeWeeks + 1 <= n
  // n = 7 * completeWeeks + 6
  // We need to show 2 * completeWeeks + 1 <= 7 * completeWeeks + 6
  // This simplifies to 0 <= 5 * completeWeeks + 5, which is true since completeWeeks >= 0.

  // Proof for MaxDaysOff(n) <= n
  // MaxDaysOff is 2 * completeWeeks + maxAdditional
  // where maxAdditional is remainingDays if remainingDays < 2, else 2
  // n = 7 * completeWeeks + remainingDays

  // Case 1: remainingDays < 2 (i.e., 0 or 1)
  // maxAdditional = remainingDays
  // MaxDaysOff(n) = 2 * completeWeeks + remainingDays
  // We want to show 2 * completeWeeks + remainingDays <= n
  // n = 7 * completeWeeks + remainingDays
  // We need to show 2 * completeWeeks + remainingDays <= 7 * completeWeeks + remainingDays
  // This simplifies to 0 <= 5 * completeWeeks, which is true since completeWeeks >= 0.

  // Case 2: remainingDays >= 2 (i.e., 2, 3, 4, 5, 6)
  // maxAdditional = 2
  // MaxDaysOff(n) = 2 * completeWeeks + 2
  // We want to show 2 * completeWeeks + 2 <= n
  // n = 7 * completeWeeks + remainingDays
  // We need to show 2 * completeWeeks + 2 <= 7 * completeWeeks + remainingDays
  // This simplifies to 0 <= 5 * completeWeeks + remainingDays - 2.
  // Since remainingDays >= 2, remainingDays - 2 >= 0.
  // Since completeWeeks >= 0, 5 * completeWeeks >= 0.
  // Therefore, 5 * completeWeeks + remainingDays - 2 >= 0, which is true.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
// </vc-spec>
// <vc-code>
{
    var min_days := MinDaysOff(n);
    var max_days := MaxDaysOff(n);
    var res_array := new int[2];
    res_array[0] := min_days;
    res_array[1] := max_days;
    result := res_array[..];

    // Prove postconditions related to result[0] <= n and result[1] <= n
    // These are encapsulated in the lemma CalculateMinMaxDaysOff
    CalculateMinMaxDaysOff(n);
}
// </vc-code>

