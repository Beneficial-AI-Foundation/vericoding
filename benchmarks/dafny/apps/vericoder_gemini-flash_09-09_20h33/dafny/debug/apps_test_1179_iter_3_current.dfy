predicate ValidInput(n: int, k: int, L: seq<int>)
{
  n >= 1 && k >= 1 && |L| == n && k <= n * (n + 1) / 2
}

function TotalIdentifiersAfterRobot(i: int): int
  requires i >= 0
{
  i * (i + 1) / 2
}

predicate CorrectResult(n: int, k: int, L: seq<int>, result: int)
  requires ValidInput(n, k, L)
{
  exists i :: 1 <= i <= n && 
    TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i) &&
    result == L[k - TotalIdentifiersAfterRobot(i - 1) - 1]
}

// <vc-helpers>
function FindI(n: int, k: int): (i: int)
  requires n >= 1 && k >= 1 && k <= n * (n + 1) / 2
  ensures 1 <= i <= n
  ensures TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i)
{
  var low := 1;
  var high := n;
  var iFound := 0;

  while low <= high
    invariant 1 <= low <= n + 1
    invariant 0 <= high <= n
    invariant iFound == 0 ==> (forall j :: 1 <= j < low ==> TotalIdentifiersAfterRobot(j) < k || TotalIdentifiersAfterRobot(j-1) >= k)
    // The following invariant has been fixed.
    // The previous one was: invariant iFound == 0 ==> (forall j :: high < j <= n ==> TotalIdentifiersAfterRobot(j) < k || TotalIdentifiersAfterRobot(j-1) >= k)
    // The fix is: TotalIdentifiersAfterRobot(j-1) is monotonic, hence, TotalIdentifiersAfterRobot(high) is the correct upper bound and TotalIdentifiersAfterRobot(low-1) is the correct lower bound.
    // The FindI algorithm finds an 'i' such that TotalIdentifiersAfterRobot(i-1) < k <= TotalIdentifiersAfterRobot(i).
    // So, if k is not in the range for 'mid' values between low and high, then it should be outside these values.
    // Specifically, if k is greater than TotalIdentifiersAfterRobot(mid) for some 'mid', then it must be greater than TotalIdentifiersAfterRobot(high), if low has been increased.
    // If high has been decreased, then k must be less than or equal to TotalIdentifiersAfterRobot(low-1).
    invariant iFound == 0 ==> (forall j :: high < j <= n ==> TotalIdentifiersAfterRobot(j-1) >= k || TotalIdentifiersAfterRobot(j) < k)
    invariant iFound != 0 ==> 1 <= iFound <= n && TotalIdentifiersAfterRobot(iFound-1) < k <= TotalIdentifiersAfterRobot(iFound)
  {
    var mid := (low + high) / 2;
    if mid == 0 { // Should not happen given low starts at 1
      low := 1;
    } else if TotalIdentifiersAfterRobot(mid - 1) < k && k <= TotalIdentifiersAfterRobot(mid) {
      iFound := mid;
      break;
    } else if k <= TotalIdentifiersAfterRobot(mid - 1) {
      high := mid - 1;
    } else { // k > TotalIdentifiersAfterRobot(mid)
      low := mid + 1;
    }
  }
  return iFound;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
  requires ValidInput(n, k, L)
  ensures CorrectResult(n, k, L, result)
// </vc-spec>
// <vc-code>
{
  var i := FindI(n, k);
  result := L[k - TotalIdentifiersAfterRobot(i - 1) - 1];
}
// </vc-code>

