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
  // Since completeWeeks is n/7, 2 * completeWeeks = 2 * (n/7)
  // We need to show 2 * (n/7) <= n. This is true for n >= 1.
  // 2 * completeWeeks = 2 * (n / 7) <= 2 * n / 7 <= n (since 2/7 <= 1)
  // More precisely: 2 * completeWeeks <= 2 * (7 * completeWeeks + remainingDays) / 7 = 2 * n / 7 <= n

  // Case 2: remainingDays > 5 (i.e., remainingDays is 6)
  // minAdditional = remainingDays - 5 = 6 - 5 = 1
  // MinDaysOff(n) = 2 * completeWeeks + 1
  // We need to show 2 * completeWeeks + 1 <= n
  // n = 7 * completeWeeks + 6
  // 2 * completeWeeks + 1 <= 7 * completeWeeks + 6 (clearly true for completeWeeks >= 0)
  // Specifically, if completeWeeks = 0, n = 6. MinDaysOff(6) = 2*0 + (6-5) = 1. 1 <= 6.
  // If completeWeeks = 1, n = 13. MinDaysOff(13) = 2*1 + (6-5) = 3. 3 <= 13.

  // Proof for MaxDaysOff(n) <= n
  // MaxDaysOff is 2 * completeWeeks + maxAdditional
  // where maxAdditional is remainingDays if remainingDays < 2, else 2
  // n = 7 * completeWeeks + remainingDays

  // Case 1: remainingDays < 2 (i.e., 0 or 1)
  // maxAdditional = remainingDays
  // MaxDaysOff(n) = 2 * completeWeeks + remainingDays
  // We need to show 2 * completeWeeks + remainingDays <= n
  // n = 7 * completeWeeks + remainingDays
  // Since completeWeeks >= 0, 2 * completeWeeks <= 7 * completeWeeks.
  // So, 2 * completeWeeks + remainingDays <= 7 * completeWeeks + remainingDays = n.

  // Case 2: remainingDays >= 2 (i.e., 2, 3, 4, 5, 6)
  // maxAdditional = 2
  // MaxDaysOff(n) = 2 * completeWeeks + 2
  // We need to show 2 * completeWeeks + 2 <= n
  // n = 7 * completeWeeks + remainingDays
  // Since remainingDays >= 2, we have:
  // 2 * completeWeeks + 2 <= 7 * completeWeeks + remainingDays
  // This holds for completeWeeks >= 0.
  // Example: If completeWeeks = 0, n = remainingDays. MaxDaysOff(n) = 2.
  // 2 <= remainingDays (true since remainingDays >= 2 for this case).
  // Example: If completeWeeks = 1, n = 7 + remainingDays. MaxDaysOff(n) = 2*1 + 2 = 4.
  // 4 <= 7 + remainingDays (true since remainingDays >= 2).
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
    result := new int[2];
    result[0] := min_days;
    result[1] := max_days;

    // Prove postconditions related to result[0] <= n and result[1] <= n
    // These are encapsulated in the lemma CalculateMinMaxDaysOff
    CalculateMinMaxDaysOff(n);
}
// </vc-code>

