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
predicate IsConnected(n: int, edges: seq<(int, int)>)
{
  if n == 1 then
    true
  else
    var adj := BuildAdjacencyList(n, edges);
    var visited := new bool[n];
    var stack := [0];
    visited[0] := true;
    var count := 1;
    
    while |stack| > 0
      invariant 0 <= count <= n
      invariant forall i :: 0 <= i < n ==> visited[i] ==> count > 0
    {
      var node := stack[|stack| - 1];
      stack := stack[..|stack| - 1];
      
      for neighbor in adj[node]
        invariant |stack| >= 0
        invariant count >= 0
      {
        if !visited[neighbor] {
          visited[neighbor] := true;
          count := count + 1;
          stack := stack + [neighbor];
        }
      }
    }
    count == n
}

function BuildAdjacencyList(n: int, edges: seq<(int, int)>): seq<seq<int>>
  requires n >= 1
  requires |edges| == n - 1
{
  var adj := seq(n, i => []);
  
  var result := adj;
  for i := 0 to |edges| - 1
    invariant forall j :: 0 <= j < n ==> |result[j]| >= 0
  {
    var (u, v) := edges[i];
    result := result[u-1 := result[u-1] + [v-1]];
    result := result[v-1 := result[v-1] + [u-1]];
  }
  result
}

function BuildSameColorComponents(colors: seq<int>, edges: seq<(int, int)>): seq<int>
  requires |colors| >= 1
  requires |edges| == |colors| - 1
{
  var n := |colors|;
  var adj := BuildAdjacencyList(n, edges);
  var component := seq(n, i => -1);
  var compId := 0;
  
  for i := 0 to n - 1
    invariant forall j :: 0 <= j < i ==> component[j] >= -1
  {
    if component[i] == -1 {
      component := DFS(i, compId, colors, adj, component);
      compId := compId + 1;
    }
  }
  component
}

function DFS(node: int, compId: int, colors: seq<int>, adj: seq<seq<int>>, component: seq<int>): seq<int>
  requires 0 <= node < |colors|
  requires compId >= 0
  requires |adj| == |colors|
  requires |component| == |colors|
  ensures |result| == |component|
{
  var stack := [node];
  var result := component;
  result := result[node := compId];
  
  while |stack| > 0
    invariant |result| == |component|
  {
    var current := stack[|stack| - 1];
    stack := stack[..|stack| - 1];
    
    for neighbor in adj[current]
      invariant |result| == |component|
    {
      if result[neighbor] == -1 && colors[neighbor] == colors[current] {
        result := result[neighbor := compId];
        stack := stack + [neighbor];
      }
    }
  }
  result
}

function BuildComponentGraph(components: seq<int>, colors: seq<int>, edges: seq<(int, int)>): seq<seq<int>>
  requires |components| == |colors|
  requires |edges| == |colors| - 1
{
  var maxComp := Max(components);
  var compGraph := seq(maxComp + 1, i => []);
  
  var result := compGraph;
  for i := 0 to |edges| - 1
    invariant |result| == maxComp + 1
  {
    var (u, v) := edges[i];
    var uComp := components[u-1];
    var vComp := components[v-1];
    
    if uComp != vComp {
      result := result[uComp := result[uComp] + [vComp]];
      result := result[vComp := result[vComp] + [uComp]];
    }
  }
  result
}

function Max(arr: seq<int>): int
  requires |arr| > 0
{
  if |arr| == 1 then arr[0]
  else var m := Max(arr[1..]); if arr[0] > m then arr[0] else m
}

function TreeDiameter(graph: seq<seq<int>>): int
  requires |graph| > 0
{
  if |graph| == 1 then 0
  else
    var (node1, _) := BFS(0, graph);
    var (node2, dist) := BFS(node1, graph);
    dist
}

function BFS(start: int, graph: seq<seq<int>>): (int, int)
  requires 0 <= start < |graph|
{
  var visited := new bool[|graph|];
  var queue := [start];
  visited[start] := true;
  var lastNode := start;
  var distance := 0;
  
  while |queue| > 0
    invariant 0 <= distance <= |graph|
  {
    var nextQueue: seq<int> := [];
    for node in queue
      invariant |nextQueue| >= 0
    {
      lastNode := node;
      for neighbor in graph[node] {
        if !visited[neighbor] {
          visited[neighbor] := true;
          nextQueue := nextQueue + [neighbor];
        }
      }
    }
    if |nextQueue| > 0 {
      distance := distance + 1;
    }
    queue := nextQueue;
  }
  (lastNode, distance)
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
  var (n, colors, edges) := ParseInput(stdin_input);
  
  if AllSameColor(colors) {
    output := "0";
    return;
  }
  
  if n == 1 {
    output := "0";
    return;
  }
  
  var components := BuildSameColorComponents(colors, edges);
  var componentGraph := BuildComponentGraph(components, colors, edges);
  var diameter := TreeDiameter(componentGraph);
  var result := (diameter + 1) / 2;
  
  output := IntToString(result);
}
// </vc-code>

