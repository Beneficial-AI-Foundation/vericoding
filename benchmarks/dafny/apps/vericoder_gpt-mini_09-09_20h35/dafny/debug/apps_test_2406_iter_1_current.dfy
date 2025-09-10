predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n &&
    (forall i :: 0 <= i < n ==> heights[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> heights[i] < heights[i+1])
}

predicate ValidOutput(n: int, result: seq<int>)
{
    |result| == n &&
    (forall i :: 0 <= i < n ==> result[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> result[i] <= result[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> result[i+1] - result[i] <= 1)
}

predicate IsStable(result: seq<int>)
{
    forall i :: 0 <= i < |result|-1 ==> !(result[i] + 2 <= result[i+1])
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

// <vc-helpers>
function sum_sq(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0]*s[0] + sum_sq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, heights)
    ensures ValidOutput(n, result)
    ensures sum_seq(result) == sum_seq(heights)
    ensures IsStable(result)
// </vc-spec>
// <vc-code>
{
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    arr[i] := heights[i];
    i := i + 1;
  }

  var pot := sum_sq(heights);
  // loop invariant: arr is non-decreasing, non-negative, sum preserved, pot >= 0
  while true
    invariant forall k :: 0 <= k < n ==> arr[k] >= 0
    invariant forall k :: 0 <= k < n-1 ==> arr[k] <= arr[k+1]
    invariant sum_seq(arr[..]) == sum_seq(heights)
    invariant pot >= 0
    decreases pot
  {
    var found := false;
    var idx := 0;
    while idx < n-1 && !found
      invariant 0 <= idx <= n-1
      invariant !found ==> (forall k :: 0 <= k < idx ==> !(arr[k+1] - arr[k] >= 2))
      decreases n-1 - idx
    {
      if arr[idx+1] - arr[idx] >= 2 {
        found := true;
        break;
      }
      idx := idx + 1;
    }
    if !found {
      break;
    }

    // perform transfer at idx
    var ai := arr[idx];
    var bi := arr[idx+1];
    assert bi - ai >= 2;
    // bi >= 2 because ai >= 0 and bi - ai >= 2
    assert ai >= 0 by {
      // from loop invariant non-negativity
      assert 0 <= idx < n;
    }
    assert bi >= 2 by {
      assert bi - ai >= 2;
      assert ai >= 0;
      calc {
        bi;
        >= bi - ai;
        >= 2;
      }
    }

    var oldPot := pot;
    // update array
    arr[idx] := ai + 1;
    arr[idx+1] := bi - 1;

    // update pot by local computation of changed squares
    var delta := (ai+1)*(ai+1) + (bi-1)*(bi-1) - (ai*ai + bi*bi);
    pot := pot + delta;
    // show pot decreased
    assert delta <= -2;
    assert pot < oldPot;

    // sum preserved
    assert sum_seq(arr[..]) == sum_seq(heights) by {
      // only modified two entries by +1 and -1
    }

    // non-negativity preserved: arr[idx+1] = bi-1 >= 0
    assert arr[idx+1] >= 0;

    // non-decreasing preserved:
    // For k not in {idx-1, idx, idx+1} relations unchanged.
    // Check k = idx: arr[idx] <= arr[idx+1]
    assert arr[idx] <= arr[idx+1] by {
      // new diff = (ai+1) <= (bi-1) <=> bi - ai >= 2 implies ai+1 <= bi-1? actually bi-1 - (ai+1) = bi - ai -2 >= 0
      assert (arr[idx+1] - arr[idx]) == (bi - ai - 2);
      assert bi - ai - 2 >= 0;
    }
    // Check k = idx-1 if exists: arr[idx-1] <= arr[idx] holds because arr[idx] increased
    if idx - 1 >= 0 {
      assert arr[idx-1] <= arr[idx];
    }
    // Check k = idx+1 if exists: arr[idx+1] <= arr[idx+2] holds because arr[idx+1] decreased
    if idx + 2 < n {
      assert arr[idx+1] <= arr[idx+2];
    }
  }

  result := arr[..];
}
// </vc-code>

