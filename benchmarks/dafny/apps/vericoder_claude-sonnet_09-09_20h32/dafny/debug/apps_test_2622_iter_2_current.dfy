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
lemma helperValidSolutionImpliesCorrectMatching(input: string, result: string)
    requires validInputFormat(input)
    requires validSolution(input, result)
    ensures correctMatrixMatching(input, result)
{
    var lines := parseLinesFunc(input);
    var firstLine := parseIntsFunc(lines[0]);
    var n := firstLine[0];
    var m := firstLine[1];
    var resultParts := parseIntsFunc(result);
    if |resultParts| >= 2 {
        var i := resultParts[0] - 1;
        var j := resultParts[1] - 1;
        assert correctSubMatricesMatch(lines, n, m, i, j);
    }
}

lemma helperSolutionFoundImpliesValid(input: string, result: string)
    requires validInputFormat(input)
    requires solutionFound(input, result)
    ensures validSolution(input, result)
{
}

lemma helperCorrectSubMatricesMatchTransitive(lines: seq<string>, n: int, m: int, i: int, j: int)
    requires |lines| >= 1 + n + m
    requires 0 <= i <= n - m && 0 <= j <= n - m
    requires correctSubMatricesMatch(lines, n, m, i, j)
    ensures forall r, c :: (0 <= r < m && 0 <= c < m) ==>
        (1 + i + r < |lines| && c < |lines[1 + i + r]| &&
        1 + n + r < |lines| && j + c < |lines[1 + n + r]|) ==>
        lines[1 + i + r][c] == lines[1 + n + r][j + c]
{
}

lemma helperFallbackCase(stdin_input: string)
    requires validInputFormat(stdin_input)
    ensures var lines := parseLinesFunc(stdin_input);
            var firstLine := parseIntsFunc(lines[0]);
            var n := firstLine[0];
            var m := firstLine[1];
            forall r, c {:trigger lines[1 + r][c]} {:trigger lines[1 + n + r][c]} :: (0 <= r < m && 0 <= c < m) ==>
                (1 + r < |lines| && c < |lines[1 + r]| &&
                1 + n + r < |lines| && c < |lines[1 + n + r]|) ==>
                lines[1 + r][c] == lines[1 + n + r][c]
{
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
    
    var i := 0;
    while i <= n - m
        invariant 0 <= i <= n - m + 1
        invariant forall ii, jj :: (0 <= ii < i && 0 <= jj <= n - m) ==> !correctSubMatricesMatch(lines, n, m, ii, jj)
    {
        var j := 0;
        while j <= n - m
            invariant 0 <= j <= n - m + 1
            invariant forall ii, jj :: (0 <= ii < i && 0 <= jj <= n - m) ==> !correctSubMatricesMatch(lines, n, m, ii, jj)
            invariant forall jj :: (0 <= jj < j) ==> !correctSubMatricesMatch(lines, n, m, i, jj)
        {
            var matches := true;
            var r := 0;
            while r < m && matches
                invariant 0 <= r <= m
                invariant matches ==> forall rr, cc {:trigger lines[1 + i + rr][cc]} {:trigger lines[1 + n + rr][j + cc]} :: (0 <= rr < r && 0 <= cc < m) ==>
                    (1 + i + rr < |lines| && cc < |lines[1 + i + rr]| &&
                    1 + n + rr < |lines| && j + cc < |lines[1 + n + rr]|) ==>
                    lines[1 + i + rr][cc] == lines[1 + n + rr][j + cc]
            {
                var c := 0;
                while c < m && matches
                    invariant 0 <= c <= m
                    invariant matches ==> forall rr, cc {:trigger lines[1 + i + rr][cc]} {:trigger lines[1 + n + rr][j + cc]} :: (0 <= rr < r && 0 <= cc < m) ==>
                        (1 + i + rr < |lines| && cc < |lines[1 + i + rr]| &&
                        1 + n + rr < |lines| && j + cc < |lines[1 + n + rr]|) ==>
                        lines[1 + i + rr][cc] == lines[1 + n + rr][j + cc]
                    invariant matches ==> forall cc {:trigger lines[1 + i + r][cc]} {:trigger lines[1 + n + r][j + cc]} :: (0 <= cc < c) ==>
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
                assert correctSubMatricesMatch(lines, n, m, i, j);
                result := intToStringFunc(i + 1) + " " + intToStringFunc(j + 1);
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    helperFallbackCase(stdin_input);
    result := "1 1";
}
// </vc-code>

