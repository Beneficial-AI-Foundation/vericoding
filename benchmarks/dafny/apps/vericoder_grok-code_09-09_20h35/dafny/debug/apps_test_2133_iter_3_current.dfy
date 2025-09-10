predicate ValidTreeInput(input: string)
{
  var lines := SplitLines(input);
  |lines| >= 2 &&
  var n := ParseInt(lines[0]);
  n >= 1 && n <= 200000 &&
  |lines| == n + 1 &&
  ValidColorLine(lines[1], n) &&
  ValidEdgeLines(lines[2..], n) &&
  var edges := seq(|lines| - 2, i requires 0 <= i < |lines| - 2 => 
    var edge := ParseIntSeq(lines[i + 2]);
    (edge[0], edge[1])
  );
  IsValidTree(n, edges)
}

predicate ValidColorLine(line: string, n: int)
{
  var colors := ParseIntSeq(line);
  |colors| == n &&
  forall i :: 0 <= i < |colors| ==> colors[i] == 0 || colors[i] == 1
}

predicate ValidEdgeLines(lines: seq<string>, n: int)
{
  |lines| == n - 1 &&
  forall i :: 0 <= i < |lines| ==> 
    var edge := ParseIntSeq(lines[i]);
    |edge| == 2 && 
    1 <= edge[0] <= n && 
    1 <= edge[1] <= n && 
    edge[0] != edge[1]
}

predicate IsValidTree(n: int, edges: seq<(int, int)>)
{
  n >= 1 &&
  |edges| == n - 1 &&
  IsConnected(n, edges) &&
  (forall e :: e in edges ==> 1 <= e.0 <= n && 1 <= e.1 <= n && e.0 != e.1) &&
  NoDuplicateEdges(edges)
}

predicate IsConnected(n: int, edges: seq<(int, int)>)
{
  true
}

predicate NoDuplicateEdges(edges: seq<(int, int)>)
{
  forall i, j :: 0 <= i < j < |edges| ==> 
    edges[i] != edges[j] && 
    (edges[i].0, edges[i].1) != (edges[j].1, edges[j].0)
}

predicate ValidIntegerOutput(output: string)
{
  var trimmed := TrimWhitespace(output);
  |trimmed| > 0 &&
  forall c :: c in trimmed ==> '0' <= c <= '9'
}

predicate AllSameColor(colors: seq<int>)
{
  |colors| > 0 ==> forall i :: 0 <= i < |colors| ==> colors[i] == colors[0]
}

function ParseInput(input: string): (int, seq<int>, seq<(int, int)>)
  requires ValidTreeInput(input)
{
  var lines := SplitLines(input);
  var n := ParseInt(lines[0]);
  var colors := ParseIntSeq(lines[1]);
  var edges := seq(|lines| - 2, i requires 0 <= i < |lines| - 2 => 
    var edge := ParseIntSeq(lines[i + 2]);
    (edge[0], edge[1])
  );
  (n, colors, edges)
}

function ParseOutput(output: string): int
{
  ParseInt(TrimWhitespace(output))
}

function ComputeMinPaintOps(n: int, colors: seq<int>, edges: seq<(int, int)>): int
  requires n >= 1
  requires |colors| == n
  requires |edges| == n - 1
{
  if AllSameColor(colors) then 0
  else
    var components := BuildSameColorComponents(colors, edges);
    var componentGraph := BuildComponentGraph(components, colors, edges);
    (TreeDiameter(componentGraph) + 1) / 2
}

// <vc-helpers>
datatype UnionFind = UnionFind(parent: map<int, int>)

// Function to find root with path compression (path compression not strictly applied for simplicity)
// Decreases not enforced, assumes no cycles
function Find(parent: map<int, int>, x: int): int
  requires x in parent
{
  if parent[x] == x then x else Find(parent, parent[x])
}

function Union(parent: map<int, int>, x: int, y: int): map<int, int>
  requires x in parent && y in parent
{
  var px := Find(parent, x);
  var py := Find(parent, y);
  if px != py then parent[px := py] else parent
}

method CollectComponents(parent: map<int, int>, i: int, n: int, groups: map<int, seq<int>>) returns (res: map<int, seq<int>>)
  decreases n - i
{
  if i == n {
    res := groups;
  } else {
    var root := Find(parent, i);
    var list := if root in groups then groups[root] else [];
    var groups' := groups[root := list + [i]];
    res := CollectComponents(parent, i + 1, n, groups');
  }
}

method BuildForColor(c: int, n: int, colors: seq<int>, edges: seq<(int, int)>, parent0: map<int, int>) returns (res: map<int, int>)
  decreases |edges|
  requires forall i :: 0 <= i < n ==> i in parent0
  requires forall i :: 0 <= i < n ==> parent0[i] == i  // initial parent
{
  if |edges| == 0 {
    res := parent0;
  } else {
    var (u, v) := edges[0];
    var new_parent := parent0;
    if colors[u] == c && colors[v] == c {
      new_parent := Union(parent0, u, v);
    }
    res := BuildForColor(c, n, colors, edges[1..], new_parent);
  }
}

method BuildSameColorComponents(n: int, colors: seq<int>, edges: seq<(int, int)>) returns (res: seq<(int, seq<int>)>)
  requires |colors| == n && |edges| == n - 1
{
  var parent0 := map[i | 0 <= i < n :: i];
  var parent0' := BuildForColor(0, n, colors, edges, parent0);
  var groups0 := CollectComponents(parent0', 0, n, map[]);
  var comps0 := seq(c | c in groups0 :: (0, groups0[c]));

  var parent1 := map[i | 0 <= i < n :: i];
  var parent1' := BuildForColor(1, n, colors, edges, parent1);
  var groups1 := CollectComponents(parent1', 0, n, map[]);
  var comps1 := seq(c | c in groups1 :: (1, groups1[c]));

  res := comps0 + comps1;
}

function ComponentOf(x: int, componentForest: seq<(int, seq<int>)>): int
  decreases |componentForest|
{
  if componentForest == [] then -1
  else if x in componentForest[0].1 then 0
  else 1 + ComponentOf(x, componentForest[1..])
}

method BuildComponentGraph(componentForest: seq<(int, seq<int>)>, n: int, colors: seq<int>, edges: seq<(int, int)>) returns (res: (int, seq<(int, int)>))
  requires |colors| == n && |edges| == n - 1
{
  var num := |componentForest| - 0;
  var edge_map := map[];
  var i := 0;
  while i < |edges|
    invariant 0 <= i <= |edges|
  {
    var (u, v) := edges[i];
    var comp_u := ComponentOf(u, componentForest);
    var comp_v := ComponentOf(v, componentForest);
    if comp_u != comp_v {
      var pair := if comp_u < comp_v then (comp_u, comp_v) else (comp_v, comp_u);
      if pair !in edge_map {
        edge_map := edge_map[pair := true];
      }
    }
    i := i + 1;
  }
  var int_edges := seq(p | p in edge_map :: p);
  res := (num, int_edges);
}

method BFS(adj: seq<seq<int>>, start: int) returns (farthest: int, dist: int)
  requires 0 <= start < |adj|
  requires forall i :: 0 <= i < |adj| ==> forall j in adj[i] :: 0 <= j < |adj|
  requires forall i, j :: 0 <= i, j < |adj| && i != j ==> i in adj[j] <==> j in adj[i]  // undirected
{
  var queue := [start];
  var visited := {start};
  var distances := map[start := 0];
  var max_d := 0;
  var far := start;
  var q_start := 0;
  while q_start < |queue|
    ghost var prev_start := q_start;
    invariant 0 <= q_start <= |queue|
  {
    var u := queue[q_start];
    q_start := q_start + 1;
    for v in adj[u]
    {
      if v !in visited {
        visited := visited + {v};
        distances := distances[v := distances[u] + 1];
        if distances[v] > max_d {
          max_d := distances[v];
          far := v;
        }
        queue := queue + [v];
      }
    }
  }
  farthest := far;
  dist := max_d;
}

method TreeDiameter(num_components: int, component_edges: seq<(int, int)>) returns (res: int)
  requires num_components >= 0 && |component_edges| <= num_components * (num_components - 1) / 2
{
  if num_components <= 1 {
    res := 0;
  } else {
    var adj := seq(num_components, i => []);
    var i := 0;
    while i < |component_edges|
    {
      var (a, b) := component_edges[i];
      adj := adj[a := adj[a] + [b]];
      adj := adj[b := adj[b] + [a]];
      i := i + 1;
    }
    var (far1, _) := BFS(adj, 0);
    var (_, diam) := BFS(adj, far1);
    res := diam;
  }
}

// Assumed function for string output
function IntToString(i: int): string
  requires i >= 0
{
  // Implementation assumed or provided by runtime
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
  requires |stdin_input| > 0
  requires ValidTreeInput(stdin_input)
  ensures |output| > 0
  ensures ValidIntegerOutput(output)
  ensures var result := ParseOutput(output);
          result >= 0
  ensures var (n, colors, edges) := ParseInput(stdin_input);
          n >= 1 ==> var result := ParseOutput(output);
                     result <= n
  ensures var (n, colors, edges) := ParseInput(stdin_input);
          AllSameColor(colors) ==> ParseOutput(output) == 0
  ensures var (n, colors, edges) := ParseInput(stdin_input);
          n == 1 ==> ParseOutput(output) == 0
  ensures var (n, colors, edges) := ParseInput(stdin_input);
          IsValidTree(n, edges) && n >= 1
  ensures var (n, colors, edges) := ParseInput(stdin_input);
          var result := ParseOutput(output);
          result == ComputeMinPaintOps(n, colors, edges)
// </vc-spec>
// <vc-code>
{
  var n, colors, edges := ParseInput(stdin_input);
  var result := ComputeMinPaintOps(n, colors, edges);
  output := IntToString(result);
}
// </vc-code>

