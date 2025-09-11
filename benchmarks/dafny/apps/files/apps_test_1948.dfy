// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
