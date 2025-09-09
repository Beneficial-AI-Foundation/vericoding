Given N cells numbered 1 to N, find the number of ways to move from cell 1 to cell N.
You have K non-intersecting integer segments [L₁,R₁], [L₂,R₂], ..., [Lₖ,Rₖ].
Let S be the union of all integers in these segments.
From cell i, you can move to cell i+d where d ∈ S, provided i+d ≤ N.
Return the count modulo 998244353.

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

method solve(N: int, K: int, segments: seq<(int, int)>) returns (result: int)
  requires ValidInput(N, K, segments)
  ensures 0 <= result < 998244353
  ensures result == computeWaysDP(N, K, segments)
{
  var dp := new int[N+1];
  var prefixSum := new int[N+1];

  // Initialize arrays
  var i := 0;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant forall k :: 0 <= k < i ==> dp[k] == 0 && prefixSum[k] == 0
  {
    dp[i] := 0;
    prefixSum[i] := 0;
    i := i + 1;
  }

  // Base case
  dp[1] := 1;
  prefixSum[1] := 1;

  // Fill dp table
  i := 2;
  while i <= N
    invariant 2 <= i <= N + 1
    invariant dp[1] == 1 && prefixSum[1] == 1
    invariant forall k :: 0 <= k < i ==> 0 <= dp[k] < 998244353 && 0 <= prefixSum[k] < 998244353
    invariant forall k :: 2 <= k < i ==> 
      dp[k] == computeSegmentContributions(k, K, segments, 
        (map j | 0 <= j <= N :: if j == 0 then 0 else if j == 1 then 1 else if j < k then prefixSum[j] else 0), 0, 0)
    invariant forall k :: 2 <= k < i ==> prefixSum[k] == (prefixSum[k-1] + dp[k]) % 998244353
  {
    var j := 0;
    dp[i] := 0;
    while j < K
      invariant 0 <= j <= K
      invariant 0 <= dp[i] < 998244353
    {
      var start := segments[j].0;
      var end := segments[j].1;
      var i_s := if i - start >= 0 then i - start else 0;
      var i_e := if i - end - 1 >= 0 then i - end - 1 else 0;
      var contribution := (prefixSum[i_s] - prefixSum[i_e] + 998244353) % 998244353;
      dp[i] := (dp[i] + contribution) % 998244353;
      j := j + 1;
    }
    prefixSum[i] := (prefixSum[i-1] + dp[i]) % 998244353;
    i := i + 1;
  }

  result := dp[N];
}
