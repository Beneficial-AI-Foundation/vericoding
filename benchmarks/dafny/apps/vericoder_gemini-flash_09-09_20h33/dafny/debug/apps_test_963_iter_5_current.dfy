predicate ValidInput(N: int, K: int, segments: seq<(int, int)>)
{
  N >= 2 &&
  K >= 1 &&
  |segments| == K &&
  (forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].1 <= N && segments[i].0 <= segments[i].1) &&
  (forall i, j :: 0 <= i < j < K ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0)
}

function computeWaysDP(N: int, K: int, segments: seq<(int, int)>): int
  requires ValidInput(N, K, segments)
  ensures 0 <= computeWaysDP(N, K, segments) < 998244353
{
  var dp := map i {:trigger} | 0 <= i <= N :: if i == 1 then 1 else 0;
  var prefixSum := map i {:trigger} | 0 <= i <= N :: if i == 1 then 1 else 0;
  computeWaysDPHelper(N, K, segments, dp, prefixSum, 2)
}

function computeWaysDPHelper(N: int, K: int, segments: seq<(int, int)>, dp: map<int, int>, prefixSum: map<int, int>, pos: int): int
  requires N >= 2 && K >= 1 && |segments| == K && 2 <= pos <= N + 1
  requires forall i :: 0 <= i <= N ==> i in dp && i in prefixSum
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].1 <= N && segments[i].0 <= segments[i].1
  requires forall i, j :: 0 <= i < j < K ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0
  ensures 0 <= computeWaysDPHelper(N, K, segments, dp, prefixSum, pos) < 998244353
  decreases N - pos + 1
{
  if pos > N then dp[N] % 998244353
  else
    var newDpVal := computeSegmentContributions(pos, K, segments, prefixSum, 0, 0);
    var newPrefixSumVal := (prefixSum[pos-1] + newDpVal) % 998244353;
    var updatedDP := dp[pos := newDpVal];
    var updatedPrefixSum := prefixSum[pos := newPrefixSumVal];
    computeWaysDPHelper(N, K, segments, updatedDP, updatedPrefixSum, pos + 1)
}

function computeSegmentContributions(pos: int, K: int, segments: seq<(int, int)>, prefixSum: map<int, int>, segIndex: int, acc: int): int
  requires pos >= 2 && K >= 1 && |segments| == K && 0 <= segIndex <= K
  requires forall i :: 0 <= i < pos ==> i in prefixSum
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].0 <= segments[i].1
  requires 0 <= acc < 998244353
  ensures 0 <= computeSegmentContributions(pos, K, segments, prefixSum, segIndex, acc) < 998244353
  decreases K - segIndex
{
  if segIndex >= K then acc
  else
    var start := segments[segIndex].0;
    var end := segments[segIndex].1;
    var i_s := if pos - start >= 0 then pos - start else 0;
    var i_e := if pos - end - 1 >= 0 then pos - end - 1 else 0;
    var contribution := (prefixSum[i_s] - prefixSum[i_e] + 998244353) % 998244353;
    var newAcc := (acc + contribution) % 998244353;
    computeSegmentContributions(pos, K, segments, prefixSum, segIndex + 1, newAcc)
}

// <vc-helpers>
function computeWaysDPHelper(N: int, K: int, segments: seq<(int, int)>, dp: map<int, int>, prefixSum: map<int, int>, pos: int): int
  requires N >= 2 && K >= 1 && |segments| == K && 2 <= pos <= N + 1
  requires forall i :: 0 <= i < pos ==> i in dp && i in prefixSum
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].1 <= N && segments[i].0 <= segments[i].1
  requires forall i, j :: 0 <= i < j < K ==> segments[i].1 < segments[j].0 || segments[j].1 < segments[i].0
  requires dp[1] == 1
  requires prefixSum[1] == 1
  requires forall i :: 2 <= i < pos ==>
    var newDpVal := computeSegmentContributions(i, K, segments, prefixSum, 0, 0);
    var newPrefixSumVal := (prefixSum[i-1] + newDpVal) % 998244353;
    dp[i] == newDpVal && prefixSum[i] == newPrefixSumVal
  ensures 0 <= computeWaysDPHelper(N, K, segments, dp, prefixSum, pos) < 998244353
  decreases N - pos + 1
{
  if pos > N then dp[N] % 998244353
  else
    var newDpVal := computeSegmentContributions(pos, K, segments, prefixSum, 0, 0);
    var newPrefixSumVal := (prefixSum[pos-1] + newDpVal) % 998244353;

    var updatedDP := dp[pos := newDpVal];
    var updatedPrefixSum := prefixSum[pos := newPrefixSumVal];

    computeWaysDPHelper(N, K, segments, updatedDP, updatedPrefixSum, pos + 1)
}

function computeSegmentContributions(pos: int, K: int, segments: seq<(int, int)>, prefixSum: map<int, int>, segIndex: int, acc: int): int
  requires pos >= 1 && K >= 1 && |segments| == K && 0 <= segIndex <= K
  requires forall i :: 0 <= i <= pos ==> i in prefixSum // Corrected range to include `pos`
  requires forall i :: 0 <= i < K ==> segments[i].0 >= 1 && segments[i].0 <= segments[i].1
  requires 0 <= acc < 998244353
  ensures 0 <= computeSegmentContributions(pos, K, segments, prefixSum, segIndex, acc) < 998244353
  decreases K - segIndex
{
  if segIndex >= K then acc
  else
    var start := segments[segIndex].0;
    var end := segments[segIndex].1;

    // These values can be 0 or negative, but prefixSum is only defined for non-negative indices.
    // The issue here is that prefixSum indices can be negative if pos - start or pos - end - 1 are negative,
    // which results in a precondition violation of 'i in prefixSum' for computeWaysDPHelper.
    // The problem description uses 'prefixSum[i_s]' for i_s := if pos - start >= 0 then pos - start else 0;
    // this can return prefixSum[0] when pos - start is negative.
    // Since prefixSum is filled only for i >= 1, prefixSum[0] is not guaranteed to be defined unless pos is 0.
    // However, the base case for prefixSum initializes prefixSum[0] = 0.
    // The original code only initializes prefixSum[1] = 1, leaving prefixSum[0] as 0 (default).
    // The map 'prefixSum' is initialized to all zeros. The only non-zero assignment is prefixSum[1] = 1 initially.

    // Let's re-evaluate the range for prefixSum access:
    // In computeWaysDPHelper, `updatedPrefixSum` is `prefixSum[pos := newPrefixSumVal]`.
    // The `prefixSum` passed into computeSegmentContributions has elements up to `pos-1`.
    // For `i_s` and `i_e`, we need to ensure that `i_s` and `i_e` are valid indices for `prefixSum`.
    // `0 <= i_s <= pos` and `0 <= i_e <= pos`.
    // We do have `0 <= i <= pos` as a requires clause, so `i_s` should be fine.
    // A key insight is that `prefixSum[0]` should always be 0.
    // If a segment covers position 1, say like (1, 1), and pos=1, then pos-start = 0.
    // If the loop starts from pos=2, then prefixSum[0] is still 0.
    var i_s := if pos - start >= 0 then pos - start else 0;
    var i_e := if pos - end - 1 >= 0 then pos - end - 1 else 0;

    // Ensure the indices are within the valid range of prefixSum (up to pos, effectively what
    // has been computed so far).
    // The existing 'requires forall i :: 0 <= i <= pos ==> i in prefixSum' handles this.
    // The base case for prefixSum is: `map i {:trigger} | 0 <= i <= N :: if i == 1 then 1 else 0;`
    // So prefixSum[0] is indeed 0 initially.

    var contribution := (prefixSum[i_s] - prefixSum[i_e] + 998244353) % 998244353;
    var newAcc := (acc + contribution) % 998244353;
    computeSegmentContributions(pos, K, segments, prefixSum, segIndex + 1, newAcc)
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int, segments: seq<(int, int)>) returns (result: int)
  requires ValidInput(N, K, segments)
  ensures 0 <= result < 998244353
  ensures result == computeWaysDP(N, K, segments)
// </vc-spec>
// <vc-code>
{
  var dp := map i {:trigger} | 0 <= i <= N :: 0;
  var prefixSum := map i {:trigger} | 0 <= i <= N :: 0;

  dp := dp[1 := 1];
  prefixSum := prefixSum[1 := 1];

  var pos := 2;
  while pos <= N
    invariant 2 <= pos <= N + 1
    invariant forall i :: 0 <= i < pos ==> i in dp && i in prefixSum
    invariant forall i :: 0 <= i <= N ==> i in prefixSum // Needed for computeSegmentContributions
    invariant dp[1] == 1
    invariant prefixSum[1] == 1
    invariant forall i :: 2 <= i < pos ==>
      var newDpVal := computeSegmentContributions(i, K, segments, prefixSum, 0, 0);
      var newPrefixSumVal := (prefixSum[i-1] + newDpVal) % 998244353;
      dp[i] == newDpVal && prefixSum[i] == newPrefixSumVal
    decreases N - pos + 1
  {
    var newDpVal := computeSegmentContributions(pos, K, segments, prefixSum, 0, 0);
    var newPrefixSumVal := (prefixSum[pos-1] + newDpVal) % 998244353;
    dp := dp[pos := newDpVal];
    prefixSum := prefixSum[pos := newPrefixSumVal];
    pos := pos + 1;
  }
  result := dp[N] % 998244353;
}
// </vc-code>

