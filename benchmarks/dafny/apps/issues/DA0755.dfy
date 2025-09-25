// <vc-preamble>
predicate ValidInput(n: int, s: int, k: int, amounts: seq<int>, colors: string)
{
  n >= 1 &&
  s >= 1 && s <= n &&
  k >= 1 &&
  |amounts| == n &&
  |colors| == n &&
  (forall i :: 0 <= i < n ==> amounts[i] >= 1) &&
  (forall i :: 0 <= i < n ==> colors[i] in ['R', 'G', 'B'])
}

predicate ValidEatingSequence(sequence: seq<int>, startPos: int, targetCandies: int, amounts: seq<int>, colors: string)
  requires |amounts| == |colors|
  requires 1 <= startPos <= |amounts|
{
  (forall i :: 0 <= i < |sequence| ==> 0 <= sequence[i] < |amounts|) &&
  (Sum(sequence, amounts) >= targetCandies) &&
  (forall i :: 0 <= i < |sequence| - 1 ==> amounts[sequence[i]] < amounts[sequence[i+1]]) &&
  (forall i :: 0 <= i < |sequence| - 1 ==> colors[sequence[i]] != colors[sequence[i+1]])
}

function Sum(sequence: seq<int>, amounts: seq<int>): int
  requires forall i :: 0 <= i < |sequence| ==> 0 <= sequence[i] < |amounts|
{
  if |sequence| == 0 then 0
  else amounts[sequence[0]] + Sum(sequence[1..], amounts)
}

function TimeToExecuteSequence(sequence: seq<int>, startPos: int): int
  requires 1 <= startPos
  requires forall i :: 0 <= i < |sequence| ==> sequence[i] >= 0
{
  if |sequence| == 0 then 0
  else Abs(startPos - 1 - sequence[0]) + MovementTime(sequence)
}

function MovementTime(sequence: seq<int>): int
  requires forall i :: 0 <= i < |sequence| ==> sequence[i] >= 0
{
  if |sequence| <= 1 then 0
  else Abs(sequence[0] - sequence[1]) + MovementTime(sequence[1..])
}

function Abs(x: int): int {
  if x < 0 then -x else x
}
// </vc-preamble>

// <vc-helpers>
method getAns(dp: array2<int>, n: int, amounts: seq<int>, colors: string, nth: int, left: int) returns (ret: int)
  requires dp.Length0 == n
  requires dp.Length1 >= left + 1
  requires 0 <= nth < n
  requires left >= 0
  requires |amounts| == n
  requires |colors| == n
  requires forall i :: 0 <= i < n ==> amounts[i] >= 1
  requires forall i :: 0 <= i < n ==> colors[i] in ['R', 'G', 'B']
  modifies dp
  ensures ret >= 0
  decreases left
{
  if left <= 0 {
    ret := 0;
    return;
  }

  if dp[nth, left] >= 0 {
    ret := dp[nth, left];
    return;
  }

  ret := 1000000;
  var i := 0;
  while i < n {
    if amounts[i] > amounts[nth] && colors[i] != colors[nth] && left >= amounts[i] {
      var subResult := getAns(dp, n, amounts, colors, i, left - amounts[i]);
      var tmpCall2 := Abs(nth - i);
      var totalCost := tmpCall2 + subResult;
      assert totalCost >= 0;
      if totalCost < ret {
        ret := totalCost;
      }
    }
    i := i + 1;
  }

  assert ret >= 0;
  dp[nth, left] := ret;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: int, k: int, amounts: seq<int>, colors: string) returns (result: int)
  requires ValidInput(n, s, k, amounts, colors)
  ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
  var dp := new int[n, k+1];
  var i := 0;
  while i < n {
    var j := 0;
    while j <= k {
      dp[i, j] := -1;
      j := j + 1;
    }
    i := i + 1;
  }

  var ans := 1000000;
  var found := false;
  i := 0;
  while i < n {
    if k >= amounts[i] {
      var timeFromI := getAns(dp, n, amounts, colors, i, k - amounts[i]);
      var tmpCall1 := Abs(s - 1 - i);
      var totalTime := timeFromI + tmpCall1;
      assert totalTime >= 0;
      if totalTime < ans {
        ans := totalTime;
        found := true;
      }
    }
    i := i + 1;
  }

  if !found {
    result := -1;
  } else {
    assert found && ans >= 0;
    result := ans;
  }
}
// </vc-code>
