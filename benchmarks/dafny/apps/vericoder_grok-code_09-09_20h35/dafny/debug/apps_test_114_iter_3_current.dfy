predicate ValidInputFormat(input: string)
{
  |input| > 0 && input[|input|-1] == '\n' &&
  exists lines: seq<string> ::
    lines == SplitLines(input) &&
    |lines| >= 3 &&
    ValidDimensionLine(lines[0]) &&
    (var parsed := ParseDimensions(lines[0]);
     var n, m := parsed.0, parsed.1;
     |lines| == n + 1 && 2 <= n <= 50 && 2 <= m <= 50 &&
     (forall i :: 1 <= i <= n ==> ValidMatrixRow(lines[i], m)) &&
     (forall i :: 1 <= i <= n ==> 
       forall j :: 1 <= j <= m ==> 
         ParseMatrixElement(lines[i], j) in {0, 1}))
}

predicate ValidOperationSequence(output: string, original_input: string)
{
  |output| > 0 && output[|output|-1] == '\n' &&
  exists lines: seq<string> ::
    lines == SplitLines(output) &&
    |lines| >= 1 &&
    ValidNumber(lines[0]) &&
    (var k := ParseNumber(lines[0]);
     0 <= k <= 2500 &&
     |lines| == k + 1 &&
     (var parsed := ParseInput(original_input);
      var n, m := parsed.0, parsed.1;
      forall i :: 1 <= i <= k ==> ValidCoordinatePair(lines[i], n-1, m-1)))
}

predicate ValidDimensionLine(line: string) { |line| > 0 }
predicate ValidMatrixRow(line: string, m: int) { |line| > 0 && m > 0 }
predicate ValidNumber(s: string) { |s| > 0 }
predicate ValidCoordinatePair(s: string, maxX: int, maxY: int) { |s| > 0 && maxX > 0 && maxY > 0 }

function SplitLines(s: string): seq<string> { [s] }
function ParseDimensions(line: string): (int, int) { (2, 2) }
function ParseNumber(s: string): int { 0 }
function ParseInput(input: string): (int, int, seq<seq<int>>) { (2, 2, [[0, 0], [0, 0]]) }
function ParseOperations(output: string): seq<(int,int)> { [] }
function ParseMatrixElement(line: string, pos: int): int { 0 }
function ToString(n: int): string { "0" }

function ApplyGreedyAlgorithm(n: int, m: int, A: seq<seq<int>>): (seq<seq<int>>, seq<(int,int)>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
{
  var B := seq(n, i => seq(m, j => 0));
  var ops := [];
  GreedyStep(A, B, ops, 0, 0, n, m)
}

// <vc-helpers>
function BuildOPS(A: seq<seq<int>>, B: seq<seq<int>>, ops: seq<(int,int)>, i: int, j: int, n: int, m: int): (seq<seq<int>>, seq<(int,int)>)
  requires 0 <= i*(m-1) + j <= (n-1)*(m-1)
  requires 0 <= i <= n-1 && 0 <= j <= m-1
  requires |A| == n && forall k :: 0 <= k < n ==> |A[k]| == m
  requires |B| == n && forall k :: 0 <= k < n ==> |B[k]| == m
  ensures var (newB, newops) := BuildOPS(A, B, ops, i, j, n, m); |newB| == n && |newops| <= (n-1)*(m-1)
{
  if i > n-2 || (i == n-2 && j >= m-1) then
    (B, ops)
  else if j >= m-1 then
    BuildOPS(A, B, ops, i+1, 0, n, m)
  else if B[i][j] != A[i][j] then
    var newOps := ops + [(i+1, j+1)];
    var newB := B[i := B[i][j := (B[i][j] + 1) % 2]];
    var newB1 := if j > 0 then newB[i := newB[i][j-1 := (newB[i][j-1] + 1) % 2]] else newB;
    var newB2 := if j < m-1 then newB1[i := newB1[i][j+1 := (newB1[i][j+1] + 1) % 2]] else newB1;
    var newB3 := if i > 0 then newB2[i-1 := newB2[i-1][j := (newB2[i-1][j] + 1) % 2]] else newB2;
    var newB4 := if i < n-1 then newB3[i+1 := newB3[i+1][j := (newB3[i+1][j] + 1) % 2]] else newB3;
    BuildOPS(A, newB4, newOps, i, j+1, n, m)
  else
    BuildOPS(A, B, ops, i, j+1, n, m)
}

function ApplyGreedyAlgorithm(n: int, m: int, A: seq<seq<int>>): (seq<seq<int>>, seq<(int,int)>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
  ensures var (B, ops) := ApplyGreedyAlgorithm(n, m, A); |B| == n && forall i :: |B[i]| == m && |ops| <= (n-1)*(m-1)
{
  var B := seq(n, i => seq(m, j => 0));
  var ops := [];
  BuildOPS(A, B, ops, 0, 0, n, m)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires ValidInputFormat(stdin_input)
  ensures |result| > 0
  ensures result == "-1\n" || ValidOperationSequence(result, stdin_input)
  ensures result != "-1\n" ==> 
    (var parsed := ParseInput(stdin_input);
     var n, m, A := parsed.0, parsed.1, parsed.2;
     var ops := ParseOperations(result);
     var algorithm_result := ApplyGreedyAlgorithm(n, m, A);
     var B := algorithm_result.0;
     var expected_ops := algorithm_result.1;
     B == A && ops == expected_ops)
  ensures result == "-1\n" ==> 
    (var parsed := ParseInput(stdin_input);
     var n, m, A := parsed.0, parsed.1, parsed.2;
     var algorithm_result := ApplyGreedyAlgorithm(n, m, A);
     var B := algorithm_result.0;
     B != A)
  ensures result == "-1\n" || 
    (exists k: nat, lines: seq<string> :: 
      lines == SplitLines(result) && 
      |lines| == k + 1 && 
      lines[0] == ToString(k) && k <= 2500 &&
      (var parsed := ParseInput(stdin_input);
       var n, m := parsed.0, parsed.1;
       forall i :: 1 <= i <= k ==> 
         (exists x, y: int :: (1 <= x <= n-1 && 1 <= y <= m-1 && 
          lines[i] == ToString(x) + " " + ToString(y)))))
// </vc-spec>
// <vc-code>
var parsed := ParseInput(stdin_input);
  var n, m, A := parsed.0, parsed.1, parsed.2;
  var algorithm_result := ApplyGreedyAlgorithm(n, m, A);
  var B, ops := algorithm_result.0, algorithm_result.1;
  if B == A then {
    var lines : seq<string> := [ToString(|ops|)];
    for i := 0 to |ops|-1 {
      var op := ops[i];
      lines := lines + [ToString(op.0) + " " + ToString(op.1)];
    }
    var result := lines[0];
    for i := 1 to |lines|-1 {
      result := result + "\n" + lines[i];
    }
    result + "\n"
  } else {
    "-1\n"
  }
// </vc-code>

