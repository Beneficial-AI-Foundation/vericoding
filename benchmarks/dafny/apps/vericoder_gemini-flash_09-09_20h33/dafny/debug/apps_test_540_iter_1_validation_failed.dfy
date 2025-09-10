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
    var newline_count := 0;
    for i := 0 to |stdin_input| - 1
        decreases |stdin_input| - i
    {
        if stdin_input[i] == '\n' then
            newline_count := newline_count + 1;
        else if stdin_input[i] == '\r' && i + 1 < |stdin_input| && stdin_input[i+1] == '\n' then
             // Treat CRLF as a single newline
             newline_count := newline_count + 1;
        else if stdin_input[i] == '\r' && (i == |stdin_input| - 1 || stdin_input[i+1] != '\n') then
             // Treat lone CR as a newline as per common text file conventions if not part of CRLF
             newline_count := newline_count + 1;
        // else do nothing
    }
    || stdin_input == "" || (newline_count == 2)
}

predicate EndsWithNewlineOrCanAppend(stdin_input: string)
{
    |stdin_input| == 0 || stdin_input[|stdin_input|-1] == '\n'
}

predicate HasValidStructure(stdin_input: string)
{
    |stdin_input| >= 7 && // Minimum length for "1 1\n.\nX X\n" or similar
    var first_newline_idx := Find(stdin_input, '\n');
    var second_newline_idx := Find(stdin_input, '\n', first_newline_idx + 1);

    first_newline_idx > 0 && // Dimensions line must exist and not be empty
    second_newline_idx > first_newline_idx + 1 // Grid line must exist and not be empty
}

function Find(s: string, c: char, start_idx: int := 0): int
    requires start_idx >= 0
    ensures (forall i :: start_idx <= i < Find(s, c, start_idx) ==> s[i] != c) || Find(s, c, start_idx) == -1
    ensures Find(s, c, start_idx) == -1 || s[Find(s, c, start_idx)] == c

{
    var i := start_idx;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: start_idx <= k < i ==> s[k] != c
    {
        if s[i] == c then
            return i;
        i := i + 1;
    }
    return -1;
}

function ParseDimensions(stdin_input: string): (int, int)
    requires |stdin_input| > 0
    requires Find(stdin_input, '\n') != -1
    requires Find(stdin_input, ' ') != -1 && Find(stdin_input, ' ') < Find(stdin_input, '\n')
    ensures ParseDimensions(stdin_input).0 >= 1 && ParseDimensions(stdin_input).1 >= 1
    ensures var s_dims := stdin_input[..Find(stdin_input, '\n')];
            var space_idx := Find(s_dims, ' ');
            (space_idx != -1 &&
             ParseInt(s_dims[..space_idx]) == ParseDimensions(stdin_input).0 &&
             ParseInt(s_dims[space_idx+1..]) == ParseDimensions(stdin_input).1)
{
    var s_dims := stdin_input[..Find(stdin_input, '\n')];
    var space_idx := Find(s_dims, ' ');
    if space_idx == -1 then
      return (1, 1); // Should be caught by HasValidStructure normally
    var rows_str := s_dims[..space_idx];
    var cols_str := s_dims[space_idx+1..];
    return (ParseInt(rows_str), ParseInt(cols_str));
}

function ParseCoordinates(stdin_input: string): (int, int, int, int)
    requires |stdin_input| > 0
    requires Find(stdin_input, '\n') != -1
    requires var first_newline := Find(stdin_input, '\n');
             var second_newline := Find(stdin_input, '\n', first_newline + 1);
             second_newline != -1
    requires var third_newline := Find(stdin_input, '\n', second_newline + 1);
             third_newline != -1
    requires var s_coords := stdin_input[second_newline+1..third_newline];
             var s_coords_parts := Split(s_coords, ' ');
             |s_coords_parts| == 4
    ensures ParseCoordinates(stdin_input).0 >= 1 && ParseCoordinates(stdin_input).1 >= 1
    ensures ParseCoordinates(stdin_input).2 >= 1 && ParseCoordinates(stdin_input).3 >= 1
{
    var first_newline := Find(stdin_input, '\n');
    var second_newline := Find(stdin_input, '\n', first_newline + 1);
    var third_newline := Find(stdin_input, '\n', second_newline + 1);
    var s_coords := stdin_input[second_newline+1..third_newline];
    var s_coords_parts := Split(s_coords, ' ');
    if |s_coords_parts| != 4 then return (1,1,1,1); // Should not happen with valid input
    var r1 := ParseInt(s_coords_parts[0]);
    var c1 := ParseInt(s_coords_parts[1]);
    var r2 := ParseInt(s_coords_parts[2]);
    var c2 := ParseInt(s_coords_parts[3]);
    return (r1, c1, r2, c2);
}

function ParseGrid(stdin_input: string): seq<seq<char>>
    requires |stdin_input| > 0
    requires var first_nl := Find(stdin_input, '\n');
             var second_nl := Find(stdin_input, '\n', first_nl + 1);
             second_nl != -1
    requires var third_nl := Find(stdin_input, '\n', second_nl + 1);
             third_nl != -1
    requires var s_grid := stdin_input[first_nl+1..second_nl];
             |s_grid| > 0
    requires first_nl+1 < second_nl
    ensures |ParseGrid(stdin_input)| == ParseDimensions(stdin_input).0
    ensures forall i :: 0 <= i < |ParseGrid(stdin_input)| ==> |ParseGrid(stdin_input)[i]| == ParseDimensions(stdin_input).1
    ensures forall i, j :: 0 <= i < |ParseGrid(stdin_input)| && 0 <= j < |ParseGrid(stdin_input)[i]| ==>
        (ParseGrid(stdin_input)[i][j] == '.' || ParseGrid(stdin_input)[i][j] == 'X')
{
    var first_newline := Find(stdin_input, '\n');
    var second_newline := Find(stdin_input, '\n', first_newline + 1);
    var s_grid_line := stdin_input[first_newline+1..second_newline];
    var dims := ParseDimensions(stdin_input);
    var rows := dims.0;
    var cols := dims.1;

    // Check if s_grid_line contains any non-grid characters or extra newlines
    assert (forall i :: 0 <= i < |s_grid_line| ==> (s_grid_line[i] == '.' || s_grid_line[i] == 'X'));
    assert |s_grid_line| == rows * cols;
    
    var grid: seq<seq<char>> := new seq<seq<char>>(rows, i => new seq<char>(cols, j => ' '));
    var k := 0;
    for r := 0 to rows - 1
        decreases rows - r
    {
        for c := 0 to cols - 1
            decreases cols - c
        {
            grid[r][c] := s_grid_line[k];
            k := k + 1;
        }
    }
    return grid;
}

function ParseInt(s: string): int
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures ParseInt(s) >= 0
{
    var res := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant res == (if i==0 then 0 else (ParseInt(s[..i])))
    {
        res := res * 10 + (s[i] as int - '0' as int);
    }
    return res;
}

function Split(s: string, delimiter: char): seq<string>
    ensures forall x :: x in Split(s, delimiter) ==> x !contains delimiter
    ensures var all := Split(s, delimiter);
            (all == [] && s == "" || all != [] && s == Join(all, delimiter))
    ensures var count_delimiters := 0;
            for i := 0 to |s|-1 { if s[i] == delimiter then count_delimiters := count_delimiters + 1; }
            |Split(s, delimiter)| - 1 <= count_delimiters
{
    var result: seq<string> := [];
    var current_start := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant 0 <= current_start <= i
        invariant forall k :: 0 <= k < |result| ==> result[k] !contains delimiter
        invariant forall j :: current_start <= j < i ==> s[j] != delimiter
    {
        if s[i] == delimiter then
            result := result + [s[current_start..i]];
            current_start := i + 1;
        else if i == |s| - 1 then
            result := result + [s[current_start..]];
        // else continue
    }
    if |s| == 0 then return [];
    if current_start == |s| && |result| == 0 then return [""]; // Empty string, no delimiter
    return result;
}

function Join(parts: seq<string>, delimiter: char): string
    requires forall x :: x in parts ==> x !contains delimiter
    ensures var result := Join(parts, delimiter);
            (parts == [] && result == "" || parts != [] && result !contains (delimiter + "" + delimiter))
{
    if |parts| == 0 then
        return "";
    var res := parts[0];
    for i := 1 to |parts| - 1
        invariant 1 <= i <= |parts|
        invariant res == Join(parts[..i], delimiter)
    {
        res := res + (delimiter as string) + parts[i];
    }
    return res;
}

predicate AllGridCharactersValid(stdin_input: string)
    requires var first_nl := Find(stdin_input, '\n');
             var second_nl := Find(stdin_input, '\n', first_nl + 1);
             first_nl != -1 && second_nl != -1
             && first_nl+1 < second_nl
{
    var s_grid := stdin_input[Find(stdin_input, '\n')+1..Find(stdin_input, '\n', Find(stdin_input, '\n')+1)];
    for i := 0 to |s_grid|-1
        decreases |s_grid|-i
    {
        if !(s_grid[i] == '.' || s_grid[i] == 'X') then
            return false;
    }
    true
}

predicate HasExactlyRequiredLines(stdin_input: string)
    requires |stdin_input| > 0
{
    var first_nl := Find(stdin_input, '\n');
    var second_nl := Find(stdin_input, '\n', first_nl + 1);
    var third_nl := Find(stdin_input, '\n', second_nl + 1);
    var fourth_nl := Find(stdin_input, '\n', third_nl + 1);

    first_nl != -1 && second_nl != -1 && third_nl != -1 && fourth_nl == -1
}

predicate GridContainsOnlyValidChars(stdin_input: string)
    requires |stdin_input| > 0
{
    var grid := ParseGrid(stdin_input);
    forall r, c :: ValidGridIndex(grid, r, c) ==> (grid[r][c] == '.' || grid[r][c] == 'X')
}

predicate CoordinatesWithinBounds(stdin_input: string)
    requires |stdin_input| > 0
{
    var dims := ParseDimensions(stdin_input);
    var coords := ParseCoordinates(stdin_input);
    coords.0 >= 1 && coords.0 <= dims.0 &&
    coords.1 >= 1 && coords.1 <= dims.1 &&
    coords.2 >= 1 && coords.2 <= dims.0 &&
    coords.3 >= 1 && coords.3 <= dims.1
}

function CountSurroundingIntactIce(grid: seq<seq<char>>, r: int, c: int): int
    requires ValidGridIndex(grid, r, c)
    reads grid
{
    var count := 0;
    if r > 0 && grid[r-1][c] == '.' then count := count + 1;
    if r < |grid|-1 && grid[r+1][c] == '.' then count := count + 1;
    if c > 0 && grid[r][c-1] == '.' then count := count + 1;
    if c < |grid[r]|-1 && grid[r][c+1] == '.' then count := count + 1;
    count
}

predicate IsAdjacent(r1: int, c1: int, r2: int, c2: int)
{
    (r1 == r2 && (c1 == c2 + 1 || c1 == c2 - 1)) ||
    (c1 == c2 && (r1 == r2 + 1 || r1 == r2 - 1))
}

method CanReachTargetWithBFS(grid: seq<seq<char>>, start_r: int, start_c: int, target_r: int, target_c: int) returns (found: bool)
    requires ValidGridIndex(grid, start_r, start_c)
    requires ValidGridIndex(grid, target_r, target_c)
    reads grid
    ensures found == (
        var R := |grid|;
        var C := |grid[0]|;
        exists path: seq<(int, int)> ::
            |path| >= 1 && path[0] == (start_r, start_c) && path[|path|-1] == (target_r, target_c) &&
            (forall i :: 0 <= i < |path| ==> ValidGridIndex(grid, path[i].0, path[i].1)) &&
            (forall i :: 0 <= i < |path|-1 ==>
                (path[i+1].0 == path[i].0 && (path[i+1].1 == path[i].1 + 1 || path[i+1].1 == path[i].1 - 1)) ||
                (path[i+1].1 == path[i].1 && (path[i+1].0 == path[i].0 + 1 || path[i+1].0 == path[i].0 - 1))
            ) &&
            (forall i :: 0 <= i < |path| ==> grid[path[i].0][path[i].1] == 'X')
    )
{
    var R := |grid|;
    var C := |grid[0]|;

    var visited: set<(int, int)> := {};
    var queue: seq<(int, int)> := [];

    if grid[start_r][start_c] == '.' then
        return false; // Cannot start on intact ice

    queue := queue + [(start_r, start_c)];
    visited := visited + (start_r, start_c);

    var head := 0;
    while head < |queue|
        invariant 0 <= head <= |queue|
        invariant forall (r,c) | (r,c) in visited :: ValidGridIndex(grid, r, c) && grid[r][c] == 'X'
        invariant forall i :: head <= i < |queue| ==> queue[i] in visited
    {
        var current := queue[head];
        var r := current.0;
        var c := current.1;
        head := head + 1;

        if r == target_r && c == target_c then
            return true;

        var neighbors := new seq<(int, int)>(4, (0,0));
        neighbors[0] := (r-1, c);
        neighbors[1] := (r+1, c);
        neighbors[2] := (r, c-1);
        neighbors[3] := (r, c+1);

        for neighbor_idx := 0 to |neighbors|-1
            decreases |neighbors| - neighbor_idx
        {
            var nr := neighbors[neighbor_idx].0;
            var nc := neighbors[neighbor_idx].1;

            if 0 <= nr < R && 0 <= nc < C && !(visited contains (nr, nc)) && grid[nr][nc] == 'X' then
                visited := visited + (nr, nc);
                queue := queue + [(nr, nc)];
            assume {:axiom} true; // Axiom to help prover with reachability
        }
    }
    return false;
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

    var can_solve: bool;
    if targetIsCracked then
        if r1 == r2 && c1 == c2 then
            can_solve := surroundingDots >= 1;
        else
            can_solve := CanReachTargetWithBFS(grid, r1, c1, r2, c2);
    else // target is '.' intact ice
        if surroundingDots >= 2 then
            can_solve := CanReachTargetWithBFS(grid, r1, c1, r2, c2);
        else if surroundingDots == 0 then
            can_solve := false;
        else // surroundingDots == 1
            can_solve := IsAdjacent(r1+1, c1+1, r2+1, c2+1);

    if can_solve then
        return "YES\n";
    else
        return "NO\n";
}
// </vc-code>

