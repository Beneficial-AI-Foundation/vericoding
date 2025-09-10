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
function GreedyStep(A: seq<seq<int>>, B: seq<seq<int>>, ops: seq<(int,int)>, i: int, j: int, n: int, m: int): (seq<seq<int>>, seq<(int,int)>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall k :: 0 <= k < n ==> |A[k]| == m
  requires |B| == n && forall k :: 0 <= k < n ==> |B[k]| == m
  requires forall k, l :: 0 <= k < n && 0 <= l < m ==> A[k][l] in {0, 1} && B[k][l] in {0, 1}
  requires 0 <= i <= n && 0 <= j <= m
  decreases n*m - i*m - j
  writes A, B, ops
{
  if i == n then (B, ops)
  else if j == m then GreedyStep(A, B, ops, i+1, 0, n, m)
  else if B[i][j] == A[i][j] then GreedyStep(A, B, ops, i, j+1, n, m)
  else if i == n-1 || j == m-1 then (B, ops)
  else {
      B := B[i := B[i][j := 1 - B[i][j]]];
      B := B[i := B[i][j+1 := 1 - B[i][j+1]]];
      B := B[i+1 := B[i+1][j := 1 - B[i+1][j]]];
      B := B[i+1 := B[i+1][j+1 := 1 - B[i+1][j+1]]];
      ops := ops + [(i+1, j+1)];
      GreedyStep(A, B, ops, i, j+1, n, m)
  }
}

method ParseInt(s: string) returns (i: int)
  requires |s| > 0 && ValidNumber(s)
  ensures i == ParseNumber(s)
{
  var sign := 1;
  var pos := 0;
  if s[0] == '-' {
    sign := -1;
    pos := 1;
  }
  var n := 0;
  while pos < |s|
    invariant pos <= |s|
    invariant n == (if pos > 0 then ParseNumber(s[..pos]) else 0)
  {
    n := n * 10 + (s[pos] - '0');
    pos := pos + 1;
  }
  i := sign * n;
}

function method ParseMatrixElementHelper(line: string, pos: int, start: int): int
  requires line == ""
  requires |line| > 0
  requires 0 <= start < |line|
  requires 1 <= pos
  decreases |line| - start
{
  if pos == 1 then 
    if start == 0 then line[start] - '0' else ParseMatrixElementHelper(line, pos-1, start-1)
  else
    if start > 0 && line[start-1] == ' ' then ParseMatrixElementHelper(line, pos-1, start)
    else ParseMatrixElementHelper(line, pos, start-1)
}

method SplitLine(s: string) returns (a: string, b: string)
  requires |s| > 0
  ensures exists i: int :: 0 <= i < |s| && s[i] == ' ' && a == s[..i] && b == s[i+1..]
  ensures ValidNumber(a) && ValidNumber(b)
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] != ' '
  {
    if s[i] == ' ' {
      break;
    }
    i := i + 1;
  }
  a := s[..i];
  b := s[i+1..];
}

method parseMatrix(input: string) returns (n: int, m: int, matrix: seq<seq<int>>)
  requires ValidInputFormat(input)
{
  var lines := SplitLines(input);
  var dim_line := lines[0];
  var parsed_dim := ParseDimensions(dim_line);
  n := parsed_dim.0;
  m := parsed_dim.1;
  matrix := [];
  var i := 1;
  while i <= n
    invariant |matrix| == i - 1
    invariant 1 <= i <= n+1
  {
    var row := lines[i];
    var parsed_row := seq(m, j => ParseMatrixElement(row, j+1));
    matrix := matrix + [parsed_row];
    i := i + 1;
  }
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
{
  var n, m, A := parseMatrix(stdin_input);
  var algorithm_result := ApplyGreedyAlgorithm(n, m, A);
  var B := algorithm_result.0;
  var expected_ops := algorithm_result.1;
  var k := |expected_ops|;
  if k > 2500 || B != A {
    return "-1\n";
  }
  var result_lines := seq(k + 1, i => "");
  result_lines[0] := ToString(k);
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> 
      var op := expected_ops[j];
      result_lines[j+1] == ToString(op.1) + " " + ToString(op.0)
  {
    var op := expected_ops[i];
    result_lines[i+1] := ToString(op.1) + " " + ToString(op.0);
    i := i + 1;
  }
  var output := "";
  i := 0;
  while i < |result_lines|
    invariant 0 <= i <= |result_lines|
    invariant output == concat(result_lines[..i])
  {
    if i > 0 {
      output := output + "\n";
    }
    output := output + result_lines[i];
    i := i + 1;
  }
  output := output + "\n";
  return output;
}
// </vc-code>

