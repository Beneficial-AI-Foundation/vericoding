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

function SplitLines(s: string): seq<string> 
{
  if |s| == 0 then []
  else
    var nl := s[0] == '\n';
    [TrimNewline(if nl then s[1..] else s)] + SplitLines(if nl then s[1..] else s[1..])
}
function TrimNewline(s: string): string
  ensures |s| == 0 || s[0] != '\n'
{
  if |s| == 0 then s else if s[0] == '\n' then s[1..] else s
}

function ParseDimensions(line: string): (int, int)
  requires ValidDimensionLine(line)
{
  var parts := SplitBySpace(line);
  (ParseNumber(parts[0]), ParseNumber(parts[1]))
}
function ParseNumber(s: string): int
  requires ValidNumber(s)
{
  if |s| == 0 then 0
  else (s[0] as int - '0' as int) * Pow10(|s| - 1) + ParseNumber(s[1..])
}
function Pow10(n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else 10 * Pow10(n - 1)
}
function ParseInput(input: string): (int, int, seq<seq<int>>)
  requires ValidInputFormat(input)
{
  var lines := SplitLines(input);
  var dims := ParseDimensions(lines[0]);
  var n := dims.0;
  var m := dims.1;
  var matrix := seq(n, i => ParseMatrixRow(lines[i + 1], m));
  (n, m, matrix)
}
function ParseMatrixRow(line: string, m: int): seq<int>
  requires ValidMatrixRow(line, m)
{
  seq(m, j => ParseMatrixElement(line, j))
}
function ParseMatrixElement(line: string, pos: int): int
  requires ValidMatrixRow(line, pos)
{
  line[pos] as int - '0' as int
}
function ParseOperations(output: string): seq<(int,int)>
  requires ValidOperationSequence(output, "")
{
  var lines := SplitLines(output);
  var k := ParseNumber(lines[0]);
  seq(k, i => ParseCoordinatePair(lines[i + 1]))
}
function ParseCoordinatePair(line: string): (int, int)
  requires |line| > 0
{
  var parts := SplitBySpace(line);
  (ParseNumber(parts[0]), ParseNumber(parts[1]))
}
function SplitBySpace(s: string): seq<string>
{
  if |s| == 0 then []
  else if s[0] == ' ' then SplitBySpace(s[1..])
  else
    var word := TakeUntilSpace(s);
    [word] + SplitBySpace(s[|word|..])
}
function TakeUntilSpace(s: string): string
{
  if |s| == 0 || s[0] == ' ' then "" else [s[0]] + TakeUntilSpace(s[1..])
}
function ToString(n: int): string
{
  if n < 10 then [('0' as int + n) as char] else ToString(n / 10) + [('0' as int + n % 10) as char]
}
function ApplyGreedyAlgorithm(n: int, m: int, A: seq<seq<int>>): (seq<seq<int>>, seq<(int,int)>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
{
  var B := seq(n, i => seq(m, j => 0));
  var ops := seq(0, _ => (0,0));
  GreedyStep(A, B, ops, 0, 0, n, m)
}
function GreedyStep(A: seq<seq<int>>, B: seq<seq<int>>, ops: seq<(int,int)>, i: int, j: int, n: int, m: int): (seq<seq<int>>, seq<(int,int)>)
  requires 0 <= i < n && 0 <= j < m
  requires |A| == n && forall x :: 0 <= x < n ==> |A[x]| == m
  requires |B| == n && forall x :: 0 <= x < n ==> |B[x]| == m
  requires forall x, y :: 0 <= x < n && 0 <= y < m ==> A[x][y] in {0,1}
  requires forall x, y :: 0 <= x < n && 0 <= y < m ==> B[x][y] in {0,1}
  decreases (n - i) * m + (m - j)
{
  if j == m - 1 && i == n - 1 then
    (B, ops)
  else if j == m - 1 then
    GreedyStep(A, B, ops, i + 1, 0, n, m)
  else
    var newB := B;
    var newOps := ops;
    if A[i][j] != B[i][j] then
      newB := FlipWindow(newB, i, j);
      newOps := ops + [(i+1, j+1)];
    GreedyStep(A, newB, newOps, i, j + 1, n, m)
}
function FlipWindow(B: seq<seq<int>>, i: int, j: int): seq<seq<int>>
  requires |B| > i+1 && i >= 0
  requires forall row :: 0 <= row < |B| ==> |B[row]| > j+1 && j >= 0
  ensures |B| == |result|
  ensures forall row :: 0 <= row < |B| ==> |B[row]| == |result[row]|
{
  seq(|B|, row => 
    if row == i || row == i+1 then
      seq(|B[row]|, col => 
        if col == j || col == j+1 then
          1 - B[row][col]
        else
          B[row][col])
    else
      B[row])
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
  var parsed := ParseInput(stdin_input);
  var n, m, A := parsed.0, parsed.1, parsed.2;
  var algorithm_result := ApplyGreedyAlgorithm(n, m, A);
  var B := algorithm_result.0;
  var expected_ops := algorithm_result.1;
  
  if B != A {
    result := "-1\n";
  } else {
    var k := |expected_ops|;
    result := ToString(k) + "\n";
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant result.ValidOperationSequence(stdin_input)
    {
      var op := expected_ops[i];
      result := result + ToString(op.0) + " " + ToString(op.1) + "\n";
      i := i + 1;
    }
  }
}
// </vc-code>

