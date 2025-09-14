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
predicate IsLeafNode(node: int, edges: seq<(int, int)>, n: int)
  requires 0 <= node < n
{
  var degree := |set e | e in edges && (e.0 == node || e.1 == node)|;
  degree <= 1
}

predicate NoDuplicates<T(==)>(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function ComputeOptimalMoves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, target: int): int
  requires |wayA| == |wayB|
  requires 0 <= target < |wayA|
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA|
{
  if |leaves| == 0 then wayA[target]
  else
    var totalDistance := SumDistances(wayA, wayB, leaves, target);
    if totalDistance >= wayA[target] then totalDistance else wayA[target]
}

function SumDistances(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, target: int): int
  requires |wayA| == |wayB|
  requires 0 <= target < |wayA|
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA|
{
  if |leaves| == 0 then 0
  else wayA[leaves[0]] + wayB[leaves[0]] + SumDistances(wayA, wayB, leaves[1..], target)
}

lemma SumDistancesNonNegative(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, target: int)
  requires |wayA| == |wayB|
  requires 0 <= target < |wayA|
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA|
  requires forall i :: 0 <= i < |wayA| ==> wayA[i] >= 0 && wayB[i] >= 0
  ensures SumDistances(wayA, wayB, leaves, target) >= 0
{
  if |leaves| == 0 {
  } else {
    SumDistancesNonNegative(wayA, wayB, leaves[1..], target);
  }
}

lemma ComputeOptimalMovesLowerBound(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, target: int)
  requires |wayA| == |wayB|
  requires 0 <= target < |wayA|
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA|
  requires forall i :: 0 <= i < |wayA| ==> wayA[i] >= 0 && wayB[i] >= 0
  ensures ComputeOptimalMoves(wayA, wayB, leaves, target) >= wayA[target]
{
  if |leaves| == 0 {
    assert ComputeOptimalMoves(wayA, wayB, leaves, target) == wayA[target];
  } else {
    SumDistancesNonNegative(wayA, wayB, leaves, target);
    var totalDistance := SumDistances(wayA, wayB, leaves, target);
    assert ComputeOptimalMoves(wayA, wayB, leaves, target) == 
           (if totalDistance >= wayA[target] then totalDistance else wayA[target]);
    assert ComputeOptimalMoves(wayA, wayB, leaves, target) >= wayA[target];
  }
}

lemma OptimalMovesProperties(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, x: int)
  requires ValidDistances(wayA, wayB, |wayA|, x)
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
  ensures OptimalMoves(wayA, wayB, leaves, x) >= 0
  ensures OptimalMoves(wayA, wayB, leaves, x) % 2 == 0
  ensures OptimalMoves(wayA, wayB, leaves, x) >= 2 * wayA[x-1]
{
  SumDistancesNonNegative(wayA, wayB, leaves, x-1);
  ComputeOptimalMovesLowerBound(wayA, wayB, leaves, x-1);
  assert ComputeOptimalMoves(wayA, wayB, leaves, x-1) >= wayA[x-1];
  assert OptimalMoves(wayA, wayB, leaves, x) == 2 * ComputeOptimalMoves(wayA, wayB, leaves, x-1);
  assert OptimalMoves(wayA, wayB, leaves, x) >= 2 * wayA[x-1];
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
  OptimalMovesProperties(wayA, wayB, leaves, x);
  result := 2 * ComputeOptimalMoves(wayA, wayB, leaves, x-1);
}
// </vc-code>

