predicate validInputFormat(input: string)
{
    var lines := parseLinesFunc(input);
    |lines| >= 3 &&
    var firstLine := parseIntsFunc(lines[0]);
    |firstLine| >= 2 &&
    var n := firstLine[0];
    var m := firstLine[1];
    n >= 1 && m >= 1 && m <= n &&
    |lines| >= 1 + n + m &&
    (forall k :: 1 <= k <= n ==> k < |lines| && |lines[k]| >= m) &&
    (forall k :: 1 + n <= k < 1 + n + m ==> k < |lines| && |lines[k]| >= n)
}

predicate validSolution(input: string, result: string)
{
    var lines := parseLinesFunc(input);
    if |lines| < 3 then true else
    var firstLine := parseIntsFunc(lines[0]);
    if |firstLine| < 2 then true else
    var n := firstLine[0];
    var m := firstLine[1];
    if n <= 0 || m <= 0 || m > n then true else
    var resultParts := parseIntsFunc(result);
    if |resultParts| < 2 then false else
    var i := resultParts[0];
    var j := resultParts[1];
    1 <= i <= n - m + 1 && 1 <= j <= n - m + 1 &&
    if |lines| >= 1 + n + m then correctSubMatricesMatch(lines, n, m, i - 1, j - 1) else false
}

predicate solutionExists(input: string)
{
    if !validInputFormat(input) then false else
    var lines := parseLinesFunc(input);
    var firstLine := parseIntsFunc(lines[0]);
    var n := firstLine[0];
    var m := firstLine[1];
    exists i, j :: (0 <= i <= n - m && 0 <= j <= n - m &&
        correctSubMatricesMatch(lines, n, m, i, j))
}

predicate solutionFound(input: string, result: string)
{
    validSolution(input, result) &&
    if !validInputFormat(input) then false else
    var lines := parseLinesFunc(input);
    var firstLine := parseIntsFunc(lines[0]);
    var n := firstLine[0];
    var m := firstLine[1];
    var resultParts := parseIntsFunc(result);
    if |resultParts| >= 2 then
        var i := resultParts[0] - 1;
        var j := resultParts[1] - 1;
        correctSubMatricesMatch(lines, n, m, i, j)
    else false
}

predicate correctMatrixMatching(input: string, result: string)
{
    if !validInputFormat(input) then true else
    var lines := parseLinesFunc(input);
    var firstLine := parseIntsFunc(lines[0]);
    var n := firstLine[0];
    var m := firstLine[1];
    var resultParts := parseIntsFunc(result);
    if |resultParts| >= 2 then
        var i := resultParts[0] - 1;
        var j := resultParts[1] - 1;
        0 <= i <= n - m && 0 <= j <= n - m &&
        (forall r, c {:trigger lines[1 + i + r][c]} {:trigger lines[1 + n + r][j + c]} :: (0 <= r < m && 0 <= c < m) ==>
            (1 + i + r < |lines| && c < |lines[1 + i + r]| &&
            r < m && 1 + n + r < |lines| && j + c < |lines[1 + n + r]|) ==>
            lines[1 + i + r][c] == lines[1 + n + r][j + c])
    else false
}

predicate alwaysReturnsFirstMatch(input: string, result: string)
{
    if !validInputFormat(input) then true else
    var lines := parseLinesFunc(input);
    var firstLine := parseIntsFunc(lines[0]);
    var n := firstLine[0];
    var m := firstLine[1];
    var resultParts := parseIntsFunc(result);
    if |resultParts| >= 2 then
        var resultI := resultParts[0] - 1;
        var resultJ := resultParts[1] - 1;
        forall i, j {:trigger correctSubMatricesMatch(lines, n, m, i, j)} :: (0 <= i <= n - m && 0 <= j <= n - m &&
            (i < resultI || (i == resultI && j < resultJ))) ==>
            !correctSubMatricesMatch(lines, n, m, i, j)
    else false
}

predicate correctSubMatricesMatch(lines: seq<string>, n: int, m: int, i: int, j: int)
    requires |lines| >= 1 + n + m
    requires 0 <= i <= n - m && 0 <= j <= n - m
{
    forall r, c {:trigger lines[1 + i + r][c]} {:trigger lines[1 + n + r][j + c]} :: (0 <= r < m && 0 <= c < m) ==>
        (1 + i + r < |lines| && c < |lines[1 + i + r]| &&
        1 + n + r < |lines| && j + c < |lines[1 + n + r]|) ==>
        lines[1 + i + r][c] == lines[1 + n + r][j + c]
}

function parseLinesFunc(input: string): seq<string>
{
    [""]
}

function parseIntsFunc(line: string): seq<int>
{
    [1, 1]
}

function intToStringFunc(n: int): string
    ensures |intToStringFunc(n)| > 0
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else "10"
}

// <vc-helpers>
lemma AllEqualImpliesMatch(lines: seq<string>, n: int, m: int, i: int, j: int)
    requires |lines| >= 1 + n + m
    requires 0 <= i <= n - m && 0 <= j <= n - m
    requires (forall r, c :: (0 <= r < m && 0 <= c < m) ==>
        (1 + i + r < |lines| && c < |lines[1 + i + r]| &&
         1 + n + r < |lines| && j + c < |lines[1 + n + r]|) ==>
         lines[1 + i + r][c] == lines[1 + n + r][j + c])
    ensures correctSubMatricesMatch(lines, n, m, i, j)
{
  // From the assumption (the provided forall) we directly have the predicate's condition.
  // The predicate correctSubMatricesMatch is exactly this forall-condition, so the lemma holds trivially.
}

lemma MismatchImpliesNotMatch(lines: seq<string>, n: int, m: int, i: int, j: int, r: int, c: int)
    requires |lines| >= 1 + n + m
    requires 0 <= i <= n - m && 0 <= j <= n - m
    requires 0 <= r < m && 0 <= c < m
    requires 1 + i + r < |lines| && c < |lines[1 + i + r]|
    requires 1 + n + r < |lines| && j + c < |lines[1 + n + r]|
    requires lines[1 + i + r][c] != lines[1 + n + r][j + c]
    ensures !correctSubMatricesMatch(lines, n, m, i, j)
{
  // If correctSubMatricesMatch held, then by its forall we would have equality for this (r,c).
  // That contradicts the provided inequality, hence correctSubMatricesMatch cannot hold.
  if correctSubMatricesMatch(lines, n, m, i, j) {
    // From the predicate we get the equality for this particular r,c
    assert (1 + i + r < |lines| && c < |lines[1 + i + r]| &&
            1 + n + r < |lines| && j + c < |lines[1 + n + r]|) ==>
           lines[1 + i + r][c] == lines[1 + n + r][j + c];
    // The antecedent holds by the requires clauses, thus we conclude equality, contradiction.
    assert lines[1 + i + r][c] == lines[1 + n + r][j + c];
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInputFormat(stdin_input)
    ensures |result| > 0
    ensures exists i, j :: i >= 1 && j >= 1 && result == intToStringFunc(i) + " " + intToStringFunc(j)
    ensures validSolution(stdin_input, result)
    ensures solutionExists(stdin_input) ==> solutionFound(stdin_input, result)
    ensures correctMatrixMatching(stdin_input, result)
    ensures alwaysReturnsFirstMatch(stdin_input, result)
// </vc-spec>
// <vc-code>
{
  var lines := parseLinesFunc(stdin_input);
  var firstLine := parseIntsFunc(lines[0]);
  var n := firstLine[0];
  var m := firstLine[1];
  var limit := n - m;

  var i := 0;
  while i <= limit
    invariant 0 <= i <= n - m + 1
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= limit ==> !correctSubMatricesMatch(lines, n, m, ii, jj)
    decreases n - i
  {
    var j := 0;
    while j <= limit
      invariant 0 <= j <= limit + 1
      invariant forall ii, jj ::
        (0 <= ii < i && 0 <= jj <= limit) || (ii == i && 0 <= jj < j) ==>
          !correctSubMatricesMatch(lines, n, m, ii, jj)
      decreases limit - j
    {
      // We will check whether submatrix at (i,j) matches by explicit comparison.
      var matched := true;
      var rr := 0;
      // Invariants to accumulate that all previously checked (r,c) are equal.
      while rr < m && matched
        invariant 0 <= rr <= m
        invariant matched ==> (forall r0, c0 :: 0 <= r0 < rr && 0 <= c0 < m ==>
            (1 + i + r0 < |lines| && c0 < |lines[1 + i + r0]| &&
             1 + n + r0 < |lines| && j + c0 < |lines[1 + n + r0]|) ==>
             lines[1 + i + r0][c0] == lines[1 + n + r0][j + c0])
        decreases m - rr
      {
        var cc := 0;
        while cc < m && matched
          invariant 0 <= cc <= m
          invariant matched ==> (forall r0, c0 :: (0 <= r0 < rr && 0 <= c0 < m) ||
                                (r0 == rr && 0 <= c0 < cc) ==>
              (1 + i + r0 < |lines| && c0 < |lines[1 + i + r0]| &&
               1 + n + r0 < |lines| && j + c0 < |lines[1 + n + r0]|) ==>
               lines[1 + i + r0][c0] == lines[1 + n + r0][j + c0])
          decreases m - cc
        {
          // Accesses are safe due to validInputFormat assumed at method entry.
          if !(lines[1 + i + rr][cc] == lines[1 + n + rr][j + cc]) {
            // Found a mismatch: record it logically to conclude this (i,j) is not a match.
            MismatchImpliesNotMatch(lines, n, m, i, j, rr, cc);
            matched := false;
            break;
          }
          cc := cc + 1;
        }
        if matched {
          rr := rr + 1;
        }
      }

      if matched {
        // All entries matched for this (i,j). Conclude logical predicate and return result.
        AllEqualImpliesMatch(lines, n, m, i, j);
        var res := intToStringFunc(i + 1) + " " + intToStringFunc(j + 1);
        return res;
      }

      // Otherwise continue with next j; the invariant that this (i,j) is not a match is preserved by the lemma called.
      j := j +
// </vc-code>

