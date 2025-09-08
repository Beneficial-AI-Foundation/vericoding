Given an undirected tree with n vertices rooted at vertex 1, Alice starts at vertex 1 and Bob starts at vertex x.
Players alternate turns with Bob going first. Each turn a player can stay at current vertex or move to adjacent vertex.
Game ends when Alice reaches Bob's vertex. Alice minimizes total moves, Bob maximizes total moves.
Find the total number of moves in optimal play.

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

predicate IsLeafNode(node: int, edges: seq<(int, int)>, n: int)
  requires 0 <= node < n
  requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
{
  CountEdgesForNode(node, edges, 0) <= 1
}

function CountEdgesForNode(node: int, edges: seq<(int, int)>, index: int): int
  requires 0 <= index <= |edges|
  requires forall e :: e in edges ==> 0 <= e.0 && 0 <= e.1
  decreases |edges| - index
{
  if index >= |edges| then 0
  else if edges[index].0 == node || edges[index].1 == node then
    1 + CountEdgesForNode(node, edges, index + 1)
  else
    CountEdgesForNode(node, edges, index + 1)
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function ComputeOptimalMoves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, bobStart: int): int
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  requires forall i :: 0 <= i < |wayA| ==> wayA[i] >= 0
  requires forall i :: 0 <= i < |wayB| ==> wayB[i] >= 0
  requires 0 <= bobStart < |wayA|
  requires |wayA| == |wayB|
{
  MaxOfInitialAndValidLeaves(wayA, wayB, leaves, wayA[bobStart], |leaves|)
}

function MaxOfInitialAndValidLeaves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, initial: int, upTo: int): int
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  requires forall i :: 0 <= i < |wayA| ==> wayA[i] >= 0
  requires forall i :: 0 <= i < |wayB| ==> wayB[i] >= 0
  requires 0 <= upTo <= |leaves|
  requires initial >= 0
  decreases upTo
{
  if upTo == 0 then
    initial
  else
    var prevMax := MaxOfInitialAndValidLeaves(wayA, wayB, leaves, initial, upTo - 1);
    var leaf := leaves[upTo - 1];
    if wayA[leaf] > wayB[leaf] && wayA[leaf] > prevMax then
      wayA[leaf]
    else
      prevMax
}

method solve(n: int, x: int, edges: seq<(int, int)>, leaves: seq<int>, wayA: seq<int>, wayB: seq<int>) returns (result: int)
  requires ValidInput(n, x, edges)
  requires ValidDistances(wayA, wayB, n, x)
  requires ValidLeaves(leaves, edges, n)
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  ensures result >= 0
  ensures result == OptimalMoves(wayA, wayB, leaves, x)
  ensures result % 2 == 0
  ensures result >= 2 * wayA[x-1]
{
    var res := wayA[x-1];

    var i := 0;
    while i < |leaves| 
      invariant 0 <= i <= |leaves|
      invariant res >= wayA[x-1]
      invariant res == MaxOfInitialAndValidLeaves(wayA, wayB, leaves, wayA[x-1], i)
    {
        var leaf := leaves[i];
        if wayA[leaf] > wayB[leaf] {
            if wayA[leaf] > res {
                res := wayA[leaf];
            }
        }
        i := i + 1;
    }

    result := res * 2;
}
