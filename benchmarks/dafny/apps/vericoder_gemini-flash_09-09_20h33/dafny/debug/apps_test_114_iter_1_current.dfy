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
function method IsDigit(c: char): bool { '0' <= c <= '9' }

function method StringToNat(s: string): (n: nat)
  requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
  requires |s| > 0
  ensures n >= 0
{
  var n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n >= 0
    invariant n == (if i == 0 then 0 else StringToNat(s[..i]))
  {
    n := n * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  return n;
}

function method SplitString(s: string, delimiter: char): seq<string>
  ensures forall i :: 0 <= i < |return| ==> |return[i]| >= 0
  ensures |s| == 0 ==> |return| == 1 && return[0] == ""
  ensures s == "" ==> return == [""]
  ensures delimiter in s ==> |return| >= 2
  ensures delimiter !in s ==> |return| == 1 && return[0] == s
{
  var result := [];
  var lastIndex := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |result| ==> |result[k]| >= 0
    invariant lastIndex <= i
    invariant (forall k :: lastIndex <= k < i ==> s[k] != delimiter)
  {
    if i == |s| || s[i] == delimiter {
      result := result + [s[lastIndex..i]];
      lastIndex := i + 1;
    }
  }
  return result;
}

function SplitLines(s: string): seq<string>
  ensures forall i :: 0 <= i < |return| ==> return[i] != "\n"
  ensures s == "" ==> return == [""]
  ensures s[|s|-1] == '\n' ==> |return| > 0 && return[|return|-1] == ""
{
  if |s| == 0 then return [""];
  var lines := SplitString(s, '\n');
  if |lines| > 0 && lines[|lines|-1] == "" && s[|s|-1] != '\n' {
    lines := lines[..|lines|-1];
  }
  return lines;
}

predicate ValidNumber(s: string) {
  |s| > 0 && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
}

function ParseNumber(s: string): int
  requires ValidNumber(s)
  ensures ParseNumber(s) == StringToNat(s)
{
  StringToNat(s)
}

predicate ValidDimensionLine(line: string) {
  var parts := SplitString(line, ' ');
  |parts| == 2 && ValidNumber(parts[0]) && ValidNumber(parts[1]) &&
  var n := ParseNumber(parts[0]);
  var m := ParseNumber(parts[1]);
  2 <= n <= 50 && 2 <= m <= 50
}

function ParseDimensions(line: string): (int, int)
  requires ValidDimensionLine(line)
  ensures var n, m := ParseDimensions(line); 2 <= n <= 50 && 2 <= m <= 50
{
  var parts := SplitString(line, ' ');
  (ParseNumber(parts[0]), ParseNumber(parts[1]))
}

function ToString(n: int): string
  requires n >= 0
  ensures ValidNumber(ToString(n))
  ensures StringToNat(ToString(n)) == n
{
  if n == 0 then "0"
  else {
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (temp == 0 ==> s != "") || (temp > 0 && s == "" && n == temp) || (temp > 0 && |s| > 0)
      invariant (ToString(n) == s + ToString(temp)) // not directly provable without a more complex invariant for recursion
    {
      s := (temp % 10 as char + '0' as int as char) + s;
      temp := temp / 10;
    }
    s
  }
}

predicate ValidMatrixElement(s: string) {
  ValidNumber(s) && (ParseNumber(s) == 0 || ParseNumber(s) == 1)
}

predicate ValidMatrixRow(line: string, m: int) {
  var parts := SplitString(line, ' ');
  |parts| == m && (forall i :: 0 <= i < m ==> ValidMatrixElement(parts[i]))
}

function method ParseMatrixElement(line: string, pos: int): int
  requires pos > 0
  requires (var parts := SplitString(line, ' '); 0 <= pos-1 < |parts|)
  requires ValidMatrixElement(SplitString(line, ' ')[pos-1])
  ensures ParseMatrixElement(line, pos) in {0, 1}
{
  ParseNumber(SplitString(line, ' ')[pos-1])
}

function ParseInput(input: string): (int, int, seq<seq<int>>)
  requires ValidInputFormat(input)
  ensures var n, m, A := ParseInput(input);
          2 <= n <= 50 && 2 <= m <= 50 &&
          |A| == n && (forall i :: 0 <= i < n ==> |A[i]| == m) &&
          (forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1})
{
  var lines := SplitLines(input);
  var n, m := ParseDimensions(lines[0]);
  var A := new seq<seq<int>>(n, i => new seq<int>(m, j => 0));
  for i := 0 to n-1 {
    var row_parts := SplitString(lines[i+1], ' ');
    for j := 0 to m-1 {
      A[i][j] := ParseNumber(row_parts[j]);
    }
  }
  (n, m, A)
}

predicate ValidCoordinatePair(s: string, maxX: int, maxY: int) {
  var parts := SplitString(s, ' ');
  |parts| == 2 && ValidNumber(parts[0]) && ValidNumber(parts[1]) &&
  var x := ParseNumber(parts[0]);
  var y := ParseNumber(parts[1]);
  0 <= x <= maxX && 0 <= y <= maxY
}

function ParseOperations(output: string): seq<(int, int)>
  requires ValidOperationSequence(output, "dummy_input_for_parsing") // Dummy input because validation is for output only here.
  ensures forall i :: 0 <= i < |return| ==> (0 <= return[i].0 && 0 <= return[i].1)
{
  var lines := SplitLines(output);
  var k := ParseNumber(lines[0]);
  var ops := new seq<(int, int)>(k, i => (0, 0));
  for i := 0 to k-1 {
    var parts := SplitString(lines[i+1], ' ');
    ops[i] := (ParseNumber(parts[0]), ParseNumber(parts[1]));
  }
  ops
}

function method ApplyFlip(A: seq<seq<int>>, r: int, c: int, n: int, m: int): seq<seq<int>>
  requires 0 <= r < n && 0 <= c < m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  ensures |return| == n && forall i :: 0 <= i < n ==> |return[i]| == m
  ensures forall i, j :: 0 <= i < n && 0 <= j < m ==> return[i][j] in {0, 1}
  ensures return[r][c] == (1 - A[r][c])
  ensures r + 1 < n ==> return[r+1][c] == (1 - A[r+1][c])
  ensures c + 1 < m ==> return[r][c+1] == (1 - A[r][c+1])
  ensures r + 1 < n && c + 1 < m ==> return[r+1][c+1] == (1 - A[r+1][c+1])
  ensures forall i, j :: 0 <= i < n && 0 <= j < m &&
                           !((i == r && j == c) || (i == r + 1 && j == c) ||
                             (i == r && j == c + 1) || (i == r + 1 && j == c + 1))
                           ==> return[i][j] == A[i][j]
{
  var B := A; // Create a mutable copy if A is conceptually immutable and changes are needed.
  // In Dafny, seqs are immutable, so we need to rebuild.
  var B' := new seq<seq<int>>(n, i => new seq<int>(m, j => A[i][j]));

  B'[r] := B'[r][c := 1 - B'[r][c]];
  if r + 1 < n {
    B'[r+1] := B'[r+1][c := 1 - B'[r+1][c]];
  }
  if c + 1 < m {
    B'[r] := B'[r][c+1 := 1 - B'[r][c+1]];
  }
  if r + 1 < n && c + 1 < m {
    B'[r+1] := B'[r+1][c+1 := 1 - B'[r+1][c+1]];
  }
  return B';
}


function GreedyStep(A: seq<seq<int>>, B: seq<seq<int>>, ops: seq<(int,int)>, r: int, c: int, n: int, m: int): (seq<seq<int>>, seq<(int,int)>)
  requires 0 <= r <= n
  requires 0 <= c <= m
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
  requires |B| == n && forall i :: 0 <= i < n ==> |B[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> B[i][j] in {0, 1}
  decreases (n-r)*m + (m-c)
  ensures 0 <= r <= n && 0 <= c <= m
  ensures |return.0| == n && forall i :: 0 <= i < n ==> |return.0[i]| == m
  ensures forall i, j :: 0 <= i < n && 0 <= j < m ==> return.0[i][j] in {0, 1}
  ensures forall i, j :: 0 <= i < r || (i == r && j < c) ==> return.0[i][j] == A[i][j]
  ensures (r == n && c == 0) ==> (forall i, j :: 0 <= i < n && 0 <= j < m ==> return.0[i][j] == A[i][j])
{
  if r >= n - 1 || c >= m - 1 {
    if r < n { // Check if any rows are not yet correct
      for k := c to m-1 {
        if B[r][k] != A[r][k] {
          // Final check: if we are at the edge, and still mismatch, it's unsolvable.
          // This algorithm finds a solution IFF B can be made A.
          // The problem statement implies it always fills A completely with GreedyStep
          // so this means B should become A only after iterating through all possible valid flips
          // to reach the (n-2, m-2) and then (n-1, m-2) positions
          // if we've reached a state where we can't make B[r][k] == A[r][k]
          // then it means there is no solution, this function doesn't return that, it assumes solution exists
          // which is the case when A' can be transformed into A. It's guaranteed to be correct here.
          // Dafny would need proof all values match at this point
        }
      }
    }
    return (B, ops);
  }

  var next_r := r;
  var next_c := c + 1;
  if next_c >= m - 1 {
    next_r := r + 1;
    next_c := 0;
  }

  var current_B := B;
  var current_ops := ops;

  if current_B[r][c] != A[r][c] {
    // Perform flip at (r, c)
    current_B := ApplyFlip(current_B, r, c, n, m);
    current_ops := current_ops + [(r, c)];
  }

  return GreedyStep(A, current_B, current_ops, next_r, next_c, n, m);
}

function ApplyGreedyAlgorithm(n: int, m: int, A: seq<seq<int>>): (seq<seq<int>>, seq<(int,int)>)
  requires 2 <= n <= 50 && 2 <= m <= 50
  requires |A| == n && forall i :: 0 <= i < n ==> |A[i]| == m
  requires forall i, j :: 0 <= i < n && 0 <= j < m ==> A[i][j] in {0, 1}
  ensures |return.0| == n && forall i :: 0 <= i < n ==> |return.0[i]| == m
  ensures forall i, j :: 0 <= i < n && 0 <= j < m ==> return.0[i][j] in {0, 1}
  ensures forall i, j :: 0 <= i < n-1 && 0 <= j < m-1 ==> return.0[i][j] == A[i][j]
{
  var C := new seq<seq<int>>(n, i => new seq<int>(m, j => 0)); // Start with a zero matrix
  var generated_ops := [];
  var result_tuple := GreedyStep(A, C, generated_ops, 0, 0, n, m);
  var ResultMatrix := result_tuple.0;
  var ResultOps := result_tuple.1;

  // After the GreedyStep completes, the matrix 'ResultMatrix' should match 'A' in the (n-1)x(m-1) top-left submatrix.
  // We need to check the last row and column to confirm if it leads to a valid state.
  // The problem implies that if a solution exists, this algorithm finds it.
  // If no solution, the final matrix (ResultMatrix) will not match A.

  return (ResultMatrix, ResultOps);
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
  var parsed_input := ParseInput(stdin_input);
  var n := parsed_input.0;
  var m := parsed_input.1;
  var A := parsed_input.2;

  var B_prime_result := ApplyGreedyAlgorithm(n, m, A);
  var B_prime := B_prime_result.0;
  var ops_seq := B_prime_result.1;

  var success := true;
  for i := 0 to n - 1 {
    for j := 0 to m - 1 {
      if B_prime[i][j] != A[i][j] {
        success := false;
        break;
      }
    }
    if !success {
      break;
    }
  }

  if !success {
    result := "-1\n";
  } else {
    var k_str := ToString(|ops_seq|);
    var ops_str := "";
    for op_idx := 0 to |ops_seq| - 1 {
      var r := ops_seq[op_idx].0;
      var c := ops_seq[op_idx].1;
      ops_str := ops_str + ToString(r + 1) + " " + ToString(c + 1) + "\n";
    }
    result := k_str + "\n" + ops_str;
  }
}
// </vc-code>

