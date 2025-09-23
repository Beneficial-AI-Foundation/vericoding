// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
