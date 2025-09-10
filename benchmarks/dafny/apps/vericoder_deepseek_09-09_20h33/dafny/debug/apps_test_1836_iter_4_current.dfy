predicate ValidInput(n: int, edges: seq<(int, int)>)
{
    n >= 2 &&
    forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n && edges[i].0 != edges[i].1
}

predicate ValidOutput(result: int, n: int, edges: seq<(int, int)>)
{
    result >= 0 && result <= 2 * |edges| * (|edges| + 1)
}

// <vc-helpers>
lemma MaxDegreeAtMostTwiceEdges(n: int, edges: seq<(int, int)>)
  requires ValidInput(n, edges)
  ensures forall u :: 1 <= u <= n ==> (countDegree(u, edges) <= 2 * |edges|)
{
}

function countDegree(vertex: int, edges: seq<(int, int)>): int
  requires vertex >= 1
  requires forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1
{
  if |edges| == 0 then 0 else
    (if edges[0].0 == vertex || edges[0].1 == vertex then 1 else 0) 
    + countDegree(vertex, edges[1..])
}

lemma {:induction edges} CountDegreeProperty(vertex: int, edges: seq<(int, int)>)
  requires vertex >= 1
  requires forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1
  ensures countDegree(vertex, edges) ==
    (if |edges| == 0 then 0 else
      (if edges[0].0 == vertex || edges[0].1 == vertex then 1 else 0) 
      + countDegree(vertex, edges[1..]))
{
}

lemma NoSelfLoops(n: int, edges: seq<(int, int)>)
  requires ValidInput(n, edges)
  ensures forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1
{
}

ghost function maxDegree(edges: seq<(int, int)>, n: int): int
  requires ValidInput(n, edges)
{
  var max := 0;
  var u := 1;
  while u <= n
    invariant 1 <= u <= n+1
    invariant max >= 0
    invariant forall v :: 1 <= v < u ==> countDegree(v, edges) <= max
  {
    if countDegree(u, edges) > max {
      max := countDegree(u, edges);
    }
    u := u + 1;
  }
  max
}

lemma MaxDegreeIsMax(n: int, edges: seq<(int, int)>)
  requires ValidInput(n, edges)
  ensures forall u :: 1 <= u <= n ==> countDegree(u, edges) <= maxDegree(edges, n)
{
}

lemma MaxDegreeBounds(n: int, edges: seq<(int, int)>)
  requires ValidInput(n, edges)
  ensures maxDegree(edges, n) <= 2 * |edges|
{
}

lemma DegreeArrayInvariant(edges: seq<(int, int)>, n: int, idx: int)
  requires ValidInput(n, edges)
  requires 0 <= idx <= |edges|
  requires forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1
  ensures forall u :: 1 <= u <= n ==> countDegree(u, edges[..idx]) <= 2 * idx
{
}

lemma DegreeConsistency(n: int, edges: seq<(int, int)>, degree: array<int>)
  requires ValidInput(n, edges)
  requires degree.Length == n
  requires forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1
  requires forall u :: 0 <= u < n ==> degree[u] == countDegree(u + 1, edges)
  ensures forall u :: 0 <= u < n ==> degree[u] <= 2 * |edges|
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, edges: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, edges)
    ensures ValidOutput(result, n, edges)
// </vc-spec>
// <vc-code>
{
  var degree := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> degree[j] == 0
  {
    degree[i] := 0;
    i := i + 1;
  }
  
  var idx := 0;
  while idx < |edges|
    invariant 0 <= idx <= |edges|
    invariant forall u :: 0 <= u < n ==> degree[u] == countDegree(u + 1, edges[..idx])
    invariant forall u :: 0 <= u < n ==> 0 <= degree[u] <= 2 * |edges|
  {
    var edge := edges[idx];
    var u := edge.0 - 1;
    var v := edge.1 - 1;
    
    degree[u] := degree[u] + 1;
    degree[v] := degree[v] + 1;
    
    idx := idx + 1;
  }
  
  var max := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant max >= 0
    invariant forall j :: 0 <= j < i ==> degree[j] <= max
  {
    if degree[i] > max {
      max := degree[i];
    }
    i := i + 1;
  }
  
  result := max;
}
// </vc-code>

