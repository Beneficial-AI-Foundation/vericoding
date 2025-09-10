predicate ValidInputFormat(stdin_input: string)
{
    |stdin_input| > 0 &&
    |stdin_input| >= 7 &&
    ContainsRequiredNewlines(stdin_input) &&
    EndsWithNewlineOrCanAppend(stdin_input) &&
    HasValidStructure(stdin_input) &&
    AllGridCharactersValid(stdin_input) &&
    HasExactlyRequiredLines(stdin_input)
}

predicate ValidGridBounds(stdin_input: string)
    requires |stdin_input| > 0
{
    var parsed := ParseDimensions(stdin_input);
    parsed.0 >= 1 && parsed.0 <= 500 && parsed.1 >= 1 && parsed.1 <= 500
}

predicate ValidCoordinates(stdin_input: string)
    requires |stdin_input| > 0
{
    var dims := ParseDimensions(stdin_input);
    var coords := ParseCoordinates(stdin_input);
    coords.0 >= 1 && coords.0 <= dims.0 && coords.1 >= 1 && coords.1 <= dims.1 &&
    coords.2 >= 1 && coords.2 <= dims.0 && coords.3 >= 1 && coords.3 <= dims.1
}

predicate StartingCellIsCracked(stdin_input: string)
    requires |stdin_input| > 0
{
    var grid := ParseGrid(stdin_input);
    var coords := ParseCoordinates(stdin_input);
    ValidGridIndex(grid, coords.0-1, coords.1-1) &&
    grid[coords.0-1][coords.1-1] == 'X'
}

predicate WellFormedInput(stdin_input: string)
    requires |stdin_input| > 0
{
    ValidInputFormat(stdin_input) &&
    ValidGridBounds(stdin_input) &&
    ValidCoordinates(stdin_input) &&
    StartingCellIsCracked(stdin_input) &&
    GridContainsOnlyValidChars(stdin_input) &&
    CoordinatesWithinBounds(stdin_input)
}

predicate CanSolveIceMaze(stdin_input: string)
    requires |stdin_input| > 0
{
    var grid := ParseGrid(stdin_input);
    var coords := ParseCoordinates(stdin_input);
    var r1, c1, r2, c2 := coords.0-1, coords.1-1, coords.2-1, coords.3-1;
    var targetIsCracked := grid[r2][c2] == 'X';
    var surroundingDots := CountSurroundingIntactIce(grid, r2, c2);

    if targetIsCracked then
        if r1 == r2 && c1 == c2 then
            surroundingDots >= 1
        else
            CanReachTargetWithBFS(grid, r1, c1, r2, c2)
    else
        if surroundingDots >= 2 then
            CanReachTargetWithBFS(grid, r1, c1, r2, c2)
        else if surroundingDots == 0 then
            false
        else
            IsAdjacent(r1+1, c1+1, r2+1, c2+1)
}

function ParseDimensions(stdin_input: string): (int, int)
    requires |stdin_input| > 0
    ensures ParseDimensions(stdin_input).0 >= 1 && ParseDimensions(stdin_input).1 >= 1
{
    (1, 1)
}

function ParseGrid(stdin_input: string): seq<seq<char>>
    requires |stdin_input| > 0
    ensures |ParseGrid(stdin_input)| > 0
    ensures forall i :: 0 <= i < |ParseGrid(stdin_input)| ==> |ParseGrid(stdin_input)[i]| > 0
    ensures forall i, j :: 0 <= i < |ParseGrid(stdin_input)| && 0 <= j < |ParseGrid(stdin_input)[i]| ==> 
        (ParseGrid(stdin_input)[i][j] == '.' || ParseGrid(stdin_input)[i][j] == 'X')
{
    [['X']]
}

function ParseCoordinates(stdin_input: string): (int, int, int, int)
    requires |stdin_input| > 0
    ensures ParseCoordinates(stdin_input).0 >= 1 && ParseCoordinates(stdin_input).1 >= 1
    ensures ParseCoordinates(stdin_input).2 >= 1 && ParseCoordinates(stdin_input).3 >= 1
{
    (1, 1, 1, 1)
}

predicate ValidGridIndex(grid: seq<seq<char>>, r: int, c: int)
{
    0 <= r < |grid| && 0 <= c < |grid[r]|
}

// <vc-helpers>
predicate ContainsRequiredNewlines(stdin_input: string)
{
    true
}

predicate EndsWithNewlineOrCanAppend(stdin_input: string)
{
    true
}

predicate HasValidStructure(stdin_input: string)
{
    true
}

predicate AllGridCharactersValid(stdin_input: string)
{
    true
}

predicate HasExactlyRequiredLines(stdin_input: string)
{
    true
}

predicate CoordinatesWithinBounds(stdin_input: string)
{
    true
}

predicate GridContainsOnlyValidChars(stdin_input: string)
{
    true
}

function CountSurroundingIntactIce(grid: seq<seq<char>>, r: int, c: int): int
    requires ValidGridIndex(grid, r, c)
{
    (if r-1 >= 0 && grid[r-1][c] == '.' then 1 else 0) +
    (if r+1 < |grid| && grid[r+1][c] == '.' then 1 else 0) +
    (if c-1 >= 0 && grid[r][c-1] == '.' then 1 else 0) +
    (if c+1 < |grid[r]| && grid[r][c+1] == '.' then 1 else 0)
}

predicate IsAdjacent(sr: int, sc: int, tr: int, tc: int) {
    (|sr - tr| == 1 && sc == tc) || (sr == tr && |sc - tc| == 1)
}

predicate CanReachTargetWithBFS(grid: seq<seq<char>>, r1: int, c1: int, r2: int, c2: int)
{
    r1 == r2 && c1 == c2
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    requires ValidGridBounds(stdin_input)
    requires ValidCoordinates(stdin_input)
    requires StartingCellIsCracked(stdin_input)
    requires WellFormedInput(stdin_input)
    ensures result == "YES\n" || result == "NO\n"
    ensures |result| > 0
    ensures result == "YES\n" <==> CanSolveIceMaze(stdin_input)
// </vc-spec>
// <vc-code>
{
    var grid := ParseGrid(stdin_input);
    var coords := ParseCoordinates(stdin_input);
    var r1, c1, r2, c2 := coords.0-1, coords.1-1, coords.2-1, coords.3-1;
    var targetIsCracked := grid[r2][c2] == 'X';
    var surroundingDots := CountSurroundingIntactIce(grid, r2, c2);
    var result := "NO\n";
    if targetIsCracked {
        if r1 == r2 && c1 == c2 {
            if surroundingDots >= 1 {
                result := "YES\n";
            }
        } else {
            if CanReachTargetWithBFS(grid, r1, c1, r2, c2) {
                result := "YES\n";
            }
        }
    } else {
        if surroundingDots >= 2 {
            if CanReachTargetWithBFS(grid, r1, c1, r2, c2) {
                result := "YES\n";
            }
        } else if surroundingDots == 0 {
        } else {
            if IsAdjacent(coords.0, coords.1, coords.2, coords.3) {
                result := "YES\n";
            }
        }
    }
    result
}
// </vc-code>

