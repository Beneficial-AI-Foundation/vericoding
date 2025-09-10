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
predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j]
}

function ComputeOptimalMoves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, x_idx: int): int
  requires ValidDistances(wayA, wayB, |wayA|, x_idx + 1)
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
{
  var n := |wayA-1|; // n is now wayA.Length - 1
  if leaves == [] then
    0
  else
    var max_val := 0;
    var max_idx := -1;
    for l_index := 0 to |leaves|-1
      decreases |leaves| - l_index
    {
      var leaf := leaves[l_index];
      var current_val := wayA[leaf] - wayB[leaf];
      if current_val > max_val then
        max_val := current_val;
        max_idx := leaf;
      else if current_val == max_val && wayA[leaf] > wayA[max_idx] then
        max_idx := leaf;
    }
    max_val * 2 + wayA[x_idx] // Corrected logic based on problem statement
}

function IsLeafNode(node: int, edges: seq<(int, int)>, n: int): bool
  requires n > 0
  requires forall e :: e in edges ==> 0 <= e.0 < n && 0 <= e.1 < n
{
  var degree := 0;
  for i := 0 to |edges|-1 {
    if edges[i].0 == node then
      degree := degree + 1;
    if edges[i].1 == node then
      degree := degree + 1;
  }
  degree == 1 && n > 1 || n == 1 && degree == 0
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
  var n := |wayA|;
  var x_idx := x - 1; // Convert 1-based x to 0-based index

  var max_val := 0;

  if leaves != [] {
    // Find the leaf with the maximum (wayA[leaf] - wayB[leaf])
    // If ties, pick the one with the maximum wayA[leaf]
    var max_diff := -2_000_000_000; // a very small number
    var best_leaf_idx := leaves[0]; // Initialize with the first leaf

    for i := 0 to |leaves|-1
      invariant 0 <= i <= |leaves|
      invariant (forall j :: 0 <= j < i ==> (wayA[leaves[j]] - wayB[leaves[j]] <= max_diff))
      invariant (forall j :: 0 <= j < i ==> (wayA[leaves[j]] - wayB[leaves[j]] == max_diff ==> wayA[leaves[j]] <= wayA[best_leaf_idx]))
      invariant 0 <= best_leaf_idx < n
    {
      var current_leaf := leaves[i];
      var current_diff := wayA[current_leaf] - wayB[current_leaf];

      if current_diff > max_diff then
        max_diff := current_diff;
        best_leaf_idx := current_leaf;
      else if current_diff == max_diff && wayA[current_leaf] > wayA[best_leaf_idx] then
        best_leaf_idx := current_leaf;
    }
    max_val := max_diff;
  } else {
    // If no leaves, max_val remains 0 as per the definition of ComputeOptimalMoves for empty leaves
    max_val := 0;
  }

  // The formula for OptimalMoves is 2 * ComputeOptimalMoves(wayA, wayB, leaves, x-1)
  // And ComputeOptimalMoves(..., x_idx) is max_val + wayA[x_idx]
  // Where max_val is max_diff from the loop when leaves is not empty, and 0 when leaves is empty.

  result := 2 * (max_val + wayA[x_idx]);
}
// </vc-code>

