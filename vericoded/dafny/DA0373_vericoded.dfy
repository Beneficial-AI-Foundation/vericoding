predicate ValidInput(n: int, x: int, edges: seq<(int, int)>)
{
  n > 0 && 1 <= x <= n && |edges| == n - 1 &&
  forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
}

predicate ValidDistances(wayA: seq<int>, wayB: seq<int>, n: int, x: int)
{
  |wayA| == n && |wayB| == n && n > 0 && 1 <= x <= n &&
  wayA[0] == 0 && wayB[x-1] == 0 &&
  forall i :: 0 <= i < n ==> wayA[i] >= 0 && wayB[i] >= 0
}

predicate ValidLeaves(leaves: seq<int>, edges: seq<(int, int)>, n: int)
  requires ValidInput(n, 1, edges)
{
  (forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < n) &&
  (forall i :: 0 <= i < |leaves| ==> IsLeafNode(leaves[i], edges, n)) &&
  (forall i :: 0 <= i < n ==> IsLeafNode(i, edges, n) ==> i in leaves) &&
  NoDuplicates(leaves)
}

function OptimalMoves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, x: int): int
  requires ValidDistances(wayA, wayB, |wayA|, x)
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
{
  2 * ComputeOptimalMoves(wayA, wayB, leaves, x-1)
}

// <vc-helpers>
function ComputeOptimalMoves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, idx: int): int
  requires |wayA| == |wayB|
  requires 0 <= idx < |wayA|
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  requires forall i :: 0 <= i < |wayA| ==> wayA[i] >= 0 && wayB[i] >= 0
{
  if |leaves| == 0 then
    wayA[idx]
  else
    MinOverLeaves(wayA, wayB, leaves, idx, 0)
}

function MinOverLeaves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, idx: int, leafIdx: int): int
  requires |wayA| == |wayB|
  requires 0 <= idx < |wayA|
  requires |leaves| > 0
  requires 0 <= leafIdx <= |leaves|
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  requires forall i :: 0 <= i < |wayA| ==> wayA[i] >= 0 && wayB[i] >= 0
  decreases |leaves| - leafIdx
{
  if leafIdx == |leaves| then
    wayA[idx]
  else
    var currentCost := wayA[idx] + wayB[leaves[leafIdx]];
    var restMin := MinOverLeaves(wayA, wayB, leaves, idx, leafIdx + 1);
    if currentCost < restMin then currentCost else restMin
}

predicate IsLeafNode(node: int, edges: seq<(int, int)>, n: int)
  requires n > 0
  requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
{
  0 <= node < n && CountConnections(node, edges) == 1
}

function CountConnections(node: int, edges: seq<(int, int)>): int
{
  if |edges| == 0 then 0
  else
    var count := if edges[0].0 == node || edges[0].1 == node then 1 else 0;
    count + CountConnections(node, edges[1..])
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma ComputeOptimalMovesProperties(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, idx: int)
  requires |wayA| == |wayB| > 0
  requires 0 <= idx < |wayA|
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  requires forall i :: 0 <= i < |wayA| ==> wayA[i] >= 0 && wayB[i] >= 0
  ensures ComputeOptimalMoves(wayA, wayB, leaves, idx) >= wayA[idx]
{
  if |leaves| == 0 {
    assert ComputeOptimalMoves(wayA, wayB, leaves, idx) == wayA[idx];
  } else {
    MinOverLeavesLowerBound(wayA, wayB, leaves, idx, 0);
  }
}

lemma MinOverLeavesLowerBound(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, idx: int, leafIdx: int)
  requires |wayA| == |wayB| > 0
  requires 0 <= idx < |wayA|
  requires |leaves| > 0
  requires 0 <= leafIdx <= |leaves|
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  requires forall i :: 0 <= i < |wayA| ==> wayA[i] >= 0 && wayB[i] >= 0
  ensures MinOverLeaves(wayA, wayB, leaves, idx, leafIdx) >= wayA[idx]
  decreases |leaves| - leafIdx
{
  if leafIdx == |leaves| {
    assert MinOverLeaves(wayA, wayB, leaves, idx, leafIdx) == wayA[idx];
  } else {
    MinOverLeavesLowerBound(wayA, wayB, leaves, idx, leafIdx + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, x: int, edges: seq<(int, int)>, leaves: seq<int>, wayA: seq<int>, wayB: seq<int>) returns (result: int)
  requires ValidInput(n, x, edges)
  requires ValidDistances(wayA, wayB, n, x)
  requires ValidLeaves(leaves, edges, n)
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  ensures result >= 0
  ensures result == OptimalMoves(wayA, wayB, leaves, x)
  ensures result % 2 == 0
  ensures result >= 2 * wayA[x-1]
// </vc-spec>
// <vc-code>
{
  var optimalMoves := ComputeOptimalMoves(wayA, wayB, leaves, x-1);
  result := 2 * optimalMoves;
  
  // Verify postconditions
  assert result == 2 * ComputeOptimalMoves(wayA, wayB, leaves, x-1);
  assert result == OptimalMoves(wayA, wayB, leaves, x);
  assert result % 2 == 0;
  
  ComputeOptimalMovesProperties(wayA, wayB, leaves, x-1);
  assert ComputeOptimalMoves(wayA, wayB, leaves, x-1) >= wayA[x-1];
  assert result >= 2 * wayA[x-1];
}
// </vc-code>

