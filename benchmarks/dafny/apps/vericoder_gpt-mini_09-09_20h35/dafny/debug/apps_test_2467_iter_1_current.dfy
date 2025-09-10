function sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

predicate isDistinct(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate isSorted(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i + 1]
}

predicate isValidCombination(combo: seq<int>, k: int, n: int)
{
    |combo| == k &&
    sum(combo) == n &&
    (forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9) &&
    isDistinct(combo) &&
    isSorted(combo)
}

predicate isValidExtension(temp: seq<int>, combo: seq<int>, k: int, n: int, start: int)
{
    |combo| == k &&
    sum(combo) == n &&
    (forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9) &&
    isDistinct(combo) &&
    isSorted(combo) &&
    |combo| >= |temp| &&
    (forall i :: 0 <= i < |temp| ==> temp[i] == combo[i]) &&
    (forall i :: |temp| <= i < |combo| ==> combo[i] >= start)
}

// <vc-helpers>
method dfs(temp: seq<int>, k: int, n: int, start: int) returns (out: seq<seq<int>>)
  requires k >= |temp|
  requires sum(temp) <= n
  requires forall j :: 0 <= j < |temp| ==> 1 <= temp[j] <= 9
  requires isDistinct(temp)
  requires isSorted(temp)
  // ensures that next chosen element will be strictly larger than the last element of temp (if any)
  requires |temp| == 0 || temp[|temp|-1] < start
  decreases k - |temp|
  ensures forall i :: 0 <= i < |out| ==> isValidExtension(temp, out[i], k, n, start)
  ensures forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in out
{
  if |temp| == k {
    if sum(temp) == n {
      out := [temp];
    } else {
      out := [];
    }
    return;
  }

  var remK := k - |temp|;
  var remSum := n - sum(temp);
  out := [];
  var i := start;
  // iterate candidates for the next element
  while i <= 9
    invariant start <= i <= 10
    invariant forall s :: s in out ==> isValidExtension(temp, s, k, n, start)
    invariant forall combo :: isValidExtension(temp, combo, k, n, start) && |combo| > |temp| && combo[|temp|] < i ==> combo in out
  {
    if i > remSum {
      break;
    }
    var newTemp := temp + [i];
    // preconditions for recursive call:
    //  - newTemp length <= k (since remK >= 1)
    //  - sum(newTemp) <= n (since i <= remSum)
    //  - newTemp elements are in 1..9, distinct and sorted, and last element < i+1
    var tails := dfs(newTemp, k, n, i + 1);
    out := out + tails;
    i := i + 1;
  }
  return;
}
// </vc-helpers>

// <vc-spec>
method combinationSum3(k: int, n: int) returns (result: seq<seq<int>>)
    requires k > 0 && n > 0 && k <= 9
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == k
    ensures forall i :: 0 <= i < |result| ==> sum(result[i]) == n
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> 1 <= result[i][j] <= 9
    ensures forall i :: 0 <= i < |result| ==> isDistinct(result[i])
    ensures forall i :: 0 <= i < |result| ==> isSorted(result[i])
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures forall combo :: isValidCombination(combo, k, n) ==> combo in result
    ensures forall combo :: combo in result ==> isValidCombination(combo, k, n)
// </vc-spec>
// <vc-code>
{
  result := dfs([], k, n, 1);
}
// </vc-code>

