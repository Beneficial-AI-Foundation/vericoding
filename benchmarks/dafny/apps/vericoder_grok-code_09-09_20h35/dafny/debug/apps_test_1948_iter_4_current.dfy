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
  forall i,j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate IsLeafNode(u: int, edges: seq<(int,int)>, n: int)
  requires ValidInput(n, 1, edges)
{
  |{e | 0 <= e < |edges| && (edges[e].0 == u || edges[e].1 == u)}| == 1
}

ghost function SeqMin(s: seq<int>) : int
  requires |s| >= 1
  decreases |s|
{
  if |s| == 1 then s[0] else if s[0] <= SeqMin(s[1..]) then s[0] else SeqMin(s[1..])
}

function ComputeOptimalMoves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, x: int): int
  requires ValidDistances(wayA, wayB, |wayA|, x)
  requires |leaves| > 0
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA|
{
  wayA[x-1] + SeqMin([ wayB[leaves[i]] | i | 0 <= i < |leaves| ])
}

function OptimalMoves(wayA: seq<int>, wayB: seq<int>, leaves: seq<int>, x: int): int
  requires ValidDistances(wayA, wayB, |wayA|, x)
  requires |leaves| > 0
  requires forall i :: 0 <= i < |leaves| ==> 0 <= leaves[i] < |wayA| && 0 <= leaves[i] < |wayB|
{
  2 * ComputeOptimalMoves(wayA, wayB, leaves, x)
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
  if |leaves| == 0 {
    result := 0;  // This should not happen based on ensures, but added for safety if requires |leaves| > 0 not added
  } else {
    var min_val := wayB[leaves[0]];
    for i := 1 to |leaves| - 1
    {
      if wayB[leaves[i]] < min_val
      {
        min_val := wayB[leaves[i]];
      }
    }
    result := 2 * (wayA[x - 1] + min_val);
  }
}
// </vc-code>

