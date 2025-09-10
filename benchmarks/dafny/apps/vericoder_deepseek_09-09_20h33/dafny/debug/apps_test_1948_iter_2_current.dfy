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
function ComputeOptimalMoves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, i: int): int
  requires ValidDistances(wayA, wayB, |wayA|, i+1)
  requires forall j :: 0 <= j < |leaves| ==> 0 <= leaves[j] < |wayA| && 0 <= leaves[j] < |wayB|
{
  if |leaves| == 0 then
    wayA[i]
  else
    min(wayA, wayB, leaves)
}

function min(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>): int
  requires |leaves| > 0
  requires forall j :: 0 <= j < |leaves| ==> 0 <= leaves[j] < |wayA| && 0 <= leaves[j] < |wayB|
  ensures exists j :: 0 <= j < |leaves| && result == wayA[leaves[j]] + wayB[leaves[j]]
{
  var min_val := wayA[leaves[0]] + wayB[leaves[0]];
  var idx := 1;
  while idx < |leaves|
    invariant 1 <= idx <= |leaves|
    invariant exists j :: 0 <= j < idx && min_val == wayA[leaves[j]] + wayB[leaves[j]]
    invariant forall j :: 0 <= j < idx ==> min_val <= wayA[leaves[j]] + wayB[leaves[j]]
  {
    var current := wayA[leaves[idx]] + wayB[leaves[idx]];
    if current < min_val {
      min_val := current;
    }
    idx := idx + 1;
  }
  min_val
}

predicate IsLeafNode(node: int, edges: seq<(int, int)>, n: int)
  requires 0 <= node < n
{
  var count : int := 0;
  for e in edges {
    if e.0 == node || e.1 == node {
      count := count + 1;
    }
  }
  count == 1
}

predicate NoDuplicates(seq: seq<int>)
{
  forall i, j :: 0 <= i < j < |seq| ==> seq[i] != seq[j]
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
  result := 2 * ComputeOptimalMoves(wayA, wayB, leaves, x-1);
}
// </vc-code>

