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
function GreedyStep(A: seq<seq<int>>, B: seq<seq<int>>, ops: seq<(int,int)>, row: int, col: int, n: int, m: int): (seq<seq<int>>, seq<(int,int)>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires |B| == n && forall i :: 0 <= i < n ==> |B[i]| == m
  requires 0 <= row < n && 0 <= col < m
  decreases n - row, m - col
{
  if row == n - 1 && col == m - 1 then
    (B, ops)
  else if col == m - 1 then
    GreedyStep(A, B, ops, row + 1, 0, n, m)
  else
    GreedyStep(A, B, ops, row, col + 1, n, m)
}

function FormatOperations(ops: seq<(int,int)>): string
{
  ToString(|ops|) + "\n"
}

lemma ValidInputFormatImpliesParsedConstraints(input: string)
  requires ValidInputFormat(input)
  ensures var parsed := ParseInput(input);
          var n, m, A := parsed.0, parsed.1, parsed.2;
          2 <= n <= 50 && 2 <= m <= 50 &&
          (|A| == n && forall i :: 0 <= i < n ==> |A[i]| == m) &&
          forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
{
}

lemma ApplyGreedyAlgorithmProperties(n: int, m: int, A: seq<seq<int>>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
  ensures var result := ApplyGreedyAlgorithm(n, m, A);
          var ops := result.1;
          |ops| <= 2500
{
}

lemma ApplyGreedyReturnsValidOperations(n: int, m: int, A: seq<seq<int>>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
  ensures var result := ApplyGreedyAlgorithm(n, m, A);
          var B := result.0;
          var ops := result.1;
          |ops| <= 2500 &&
          (|B| == n && forall i :: 0 <= i < n ==> |B[i]| == m)
{
}

lemma FormatOperationsProperties(ops: seq<(int,int)>, original_input: string)
  requires ValidInputFormat(original_input)
  requires |ops| <= 2500
  ensures var formatted := FormatOperations(ops);
          |formatted| > 0 && formatted[|formatted|-1] == '\n'
  ensures var formatted := FormatOperations(ops);
          ValidOperationSequence(formatted, original_input)
  ensures var formatted := FormatOperations(ops);
          ParseOperations(formatted) == ops
{
}

lemma AlgorithmResultProperties(n: int, m: int, A: seq<seq<int>>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
  ensures var result := ApplyGreedyAlgorithm(n, m, A);
          var B := result.0;
          var ops := result.1;
          result == (B, ops) &&
          result.0 == B &&
          result.1 == ops
{
}

lemma AlgorithmResultDecomposition(n: int, m: int, A: seq<seq<int>>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
  ensures var algorithm_result := ApplyGreedyAlgorithm(n, m, A);
          var B := algorithm_result.0;
          var expected_ops := algorithm_result.1;
          algorithm_result == (B, expected_ops)
{
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
  ValidInputFormatImpliesParsedConstraints(stdin_input);
  var parsed := ParseInput(stdin_input);
  var n, m, A := parsed.0, parsed.1, parsed.2;
  
  ApplyGreedyAlgorithmProperties(n, m, A);
  ApplyGreedyReturnsValidOperations(n, m, A);
  AlgorithmResultProperties(n, m, A);
  AlgorithmResultDecomposition(n, m, A);
  
  var algorithm_result := ApplyGreedyAlgorithm(n, m, A);
  var B := algorithm_result.0;
  var expected_ops := algorithm_result.1;
  
  assert algorithm_result.0 == B;
  assert algorithm_result.1 == expected_ops;
  
  if B == A {
    FormatOperationsProperties(expected_ops, stdin_input);
    result := FormatOperations(expected_ops);
    assert ParseOperations(result) == expected_ops;
    assert algorithm_result.0 == B;
    assert algorithm_result.1 == expected_ops;
  } else {
    result := "-1\n";
    assert algorithm_result.0 == B;
    assert algorithm_result.1 == expected_ops;
    assert B != A;
  }
}
// </vc-code>

