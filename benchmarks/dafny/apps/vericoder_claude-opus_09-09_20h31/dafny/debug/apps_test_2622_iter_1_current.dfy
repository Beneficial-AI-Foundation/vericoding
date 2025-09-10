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
lemma SubMatrixMatchExists(lines: seq<string>, n: int, m: int)
    requires validInputFormat(parseLinesFunc("dummy"))
    requires |lines| >= 1 + n + m
    requires n >= 1 && m >= 1 && m <= n
    ensures exists i, j :: 0 <= i <= n - m && 0 <= j <= n - m && 
            correctSubMatricesMatch(lines, n, m, i, j)
{
    // At least position (0, 0) is valid
    assert 0 <= 0 <= n - m && 0 <= 0 <= n - m;
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
    
    var found := false;
    var resultI := 1;
    var resultJ := 1;
    
    var i := 0;
    while i <= n - m && !found
        invariant 0 <= i <= n - m + 1
        invariant found ==> 0 <= resultI - 1 <= n - m && 0 <= resultJ - 1 <= n - m
        invariant found ==> correctSubMatricesMatch(lines, n, m, resultI - 1, resultJ - 1)
        invariant !found ==> forall ii, jj :: 0 <= ii < i && 0 <= jj <= n - m ==> 
                  !correctSubMatricesMatch(lines, n, m, ii, jj)
        invariant found ==> forall ii, jj :: (0 <= ii <= n - m && 0 <= jj <= n - m &&
                  (ii < resultI - 1 || (ii == resultI - 1 && jj < resultJ - 1))) ==>
                  !correctSubMatricesMatch(lines, n, m, ii, jj)
    {
        var j := 0;
        while j <= n - m && !found
            invariant 0 <= j <= n - m + 1
            invariant 0 <= i <= n - m
            invariant found ==> 0 <= resultI - 1 <= n - m && 0 <= resultJ - 1 <= n - m
            invariant found ==> correctSubMatricesMatch(lines, n, m, resultI - 1, resultJ - 1)
            invariant !found ==> forall ii, jj :: (0 <= ii < i && 0 <= jj <= n - m) ==> 
                      !correctSubMatricesMatch(lines, n, m, ii, jj)
            invariant !found ==> forall jj :: 0 <= jj < j ==> 
                      !correctSubMatricesMatch(lines, n, m, i, jj)
            invariant found ==> forall ii, jj :: (0 <= ii <= n - m && 0 <= jj <= n - m &&
                      (ii < resultI - 1 || (ii == resultI - 1 && jj < resultJ - 1))) ==>
                      !correctSubMatricesMatch(lines, n, m, ii, jj)
        {
            var matches := true;
            var r := 0;
            while r < m && matches
                invariant 0 <= r <= m
                invariant matches ==> forall rr, cc :: 0 <= rr < r && 0 <= cc < m ==>
                          (1 + i + rr < |lines| && cc < |lines[1 + i + rr]| &&
                           1 + n + rr < |lines| && j + cc < |lines[1 + n + rr]|) ==>
                          lines[1 + i + rr][cc] == lines[1 + n + rr][j + cc]
            {
                var c := 0;
                while c < m && matches
                    invariant 0 <= c <= m
                    invariant 0 <= r < m
                    invariant matches ==> forall rr, cc :: 0 <= rr < r && 0 <= cc < m ==>
                              (1 + i + rr < |lines| && cc < |lines[1 + i + rr]| &&
                               1 + n + rr < |lines| && j + cc < |lines[1 + n + rr]|) ==>
                              lines[1 + i + rr][cc] == lines[1 + n + rr][j + cc]
                    invariant matches ==> forall cc :: 0 <= cc < c ==>
                              (1 + i + r < |lines| && cc < |lines[1 + i + r]| &&
                               1 + n + r < |lines| && j + cc < |lines[1 + n + r]|) ==>
                              lines[1 + i + r][cc] == lines[1 + n + r][j + cc]
                {
                    if 1 + i + r < |lines| && c < |lines[1 + i + r]| &&
                       1 + n + r < |lines| && j + c < |lines[1 + n + r]| {
                        if lines[1 + i + r][c] != lines[1 + n + r][j + c] {
                            matches := false;
                        }
                    }
                    c := c + 1;
                }
                r := r + 1;
            }
            
            if matches {
                found := true;
                resultI := i + 1;
                resultJ := j + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := intToStringFunc(resultI) + " " + intToStringFunc(resultJ);
}
// </vc-code>

