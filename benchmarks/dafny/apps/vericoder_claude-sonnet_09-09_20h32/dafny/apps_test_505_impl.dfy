predicate ValidInput(n: int, m: int, k: int, grid: seq<string>)
{
    n > 0 && m > 0 && k >= 0 &&
    |grid| == n &&
    (forall i :: 0 <= i < n ==> |grid[i]| == m) &&
    (exists i, j :: 0 <= i < n && 0 <= j < m && grid[i][j] == 'X') &&
    (forall i :: 0 <= i < n ==> forall c :: c in grid[i] ==> c == '.' || c == '*' || c == 'X') &&
    |set i,j | 0 <= i < n && 0 <= j < m && grid[i][j] == 'X' :: (i,j)| == 1
}

function GetNextPosition(x: int, y: int, move: char): (int, int)
{
    match move
        case 'D' => (x + 1, y)
        case 'L' => (x, y - 1)
        case 'R' => (x, y + 1)
        case 'U' => (x - 1, y)
        case _ => (x, y)
}

function SimulatePath(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int): (int, int)
    decreases |path|
{
    if |path| == 0 then (startX, startY)
    else 
        var nextPos := GetNextPosition(startX, startY, path[0]);
        SimulatePath(nextPos.0, nextPos.1, path[1..], grid, n, m)
}

predicate ValidPath(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int)
{
    forall i :: 0 <= i <= |path| ==> 
        var pos := SimulatePath(startX, startY, path[..i], grid, n, m);
        0 <= pos.0 < n && 0 <= pos.1 < m && 
        pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
        grid[pos.0][pos.1] != '*'
}

predicate PathReturnsToStart(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int)
{
    var finalPos := SimulatePath(startX, startY, path, grid, n, m);
    finalPos.0 == startX && finalPos.1 == startY
}

predicate ValidDirections(path: string)
{
    forall c :: c in path ==> c == 'D' || c == 'L' || c == 'R' || c == 'U'
}

// <vc-helpers>
lemma PathConcatenationSimulation(startX: int, startY: int, path1: string, path2: string, grid: seq<string>, n: int, m: int)
    ensures SimulatePath(startX, startY, path1 + path2, grid, n, m) == 
            (var midPos := SimulatePath(startX, startY, path1, grid, n, m);
             SimulatePath(midPos.0, midPos.1, path2, grid, n, m))
    decreases |path1|
{
    if |path1| == 0 {
        assert path1 + path2 == path2;
    } else {
        var nextPos := GetNextPosition(startX, startY, path1[0]);
        assert (path1 + path2)[1..] == path1[1..] + path2;
        PathConcatenationSimulation(nextPos.0, nextPos.1, path1[1..], path2, grid, n, m);
    }
}

lemma OppositeMovesCancel(x: int, y: int, move1: char, move2: char)
    requires (move1 == 'D' && move2 == 'U') || (move1 == 'U' && move2 == 'D') ||
             (move1 == 'L' && move2 == 'R') || (move1 == 'R' && move2 == 'L')
    ensures var pos1 := GetNextPosition(x, y, move1);
            GetNextPosition(pos1.0, pos1.1, move2) == (x, y)
{
}

function BuildAlternatingPath(move: char, opposite: char, k: int): string
    requires k >= 0 && k % 2 == 0
    decreases k
{
    if k == 0 then ""
    else if k == 1 then [move]
    else [move, opposite] + BuildAlternatingPath(move, opposite, k - 2)
}

lemma TwoStepPathReturnsToStart(startX: int, startY: int, move: char, opposite: char, grid: seq<string>, n: int, m: int)
    requires (move == 'D' && opposite == 'U') || (move == 'U' && move == 'D') ||
             (move == 'L' && opposite == 'R') || (move == 'R' && opposite == 'L')
    ensures SimulatePath(startX, startY, [move, opposite], grid, n, m) == (startX, startY)
{
    var pos1 := GetNextPosition(startX, startY, move);
    assert SimulatePath(startX, startY, [move, opposite], grid, n, m) == 
           SimulatePath(pos1.0, pos1.1, [opposite], grid, n, m);
    assert SimulatePath(pos1.0, pos1.1, [opposite], grid, n, m) == 
           GetNextPosition(pos1.0, pos1.1, opposite);
    OppositeMovesCancel(startX, startY, move, opposite);
}

lemma PathConcatenationPreservesReturn(startX: int, startY: int, path1: string, path2: string, grid: seq<string>, n: int, m: int)
    requires SimulatePath(startX, startY, path1, grid, n, m) == (startX, startY)
    requires SimulatePath(startX, startY, path2, grid, n, m) == (startX, startY)
    ensures SimulatePath(startX, startY, path1 + path2, grid, n, m) == (startX, startY)
{
    PathConcatenationSimulation(startX, startY, path1, path2, grid, n, m);
}

lemma ValidDirectionsPreserved(move: char, opposite: char, path: string)
    requires move in ['D', 'L', 'R', 'U'] && opposite in ['D', 'L', 'R', 'U']
    requires ValidDirections(path)
    ensures ValidDirections(path + [move, opposite])
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, grid: seq<string>) returns (result: string)
    requires ValidInput(n, m, k, grid)
    ensures k % 2 == 1 ==> result == "IMPOSSIBLE"
    ensures k % 2 == 0 ==> (
        result == "IMPOSSIBLE" || 
        (|result| == k && ValidDirections(result))
    )
    ensures result != "IMPOSSIBLE" ==> |result| == k
    ensures result != "IMPOSSIBLE" ==> (
        exists startX, startY :: 0 <= startX < n && 0 <= startY < m && 
        grid[startX][startY] == 'X' &&
        PathReturnsToStart(startX, startY, result, grid, n, m)
    )
    ensures result != "IMPOSSIBLE" ==> (
        exists startX, startY :: 0 <= startX < n && 0 <= startY < m && 
        grid[startX][startY] == 'X' &&
        ValidPath(startX, startY, result, grid, n, m)
    )
// </vc-spec>
// <vc-code>
{
    if k % 2 == 1 {
        return "IMPOSSIBLE";
    }
    
    if k == 0 {
        return "";
    }
    
    // Find X position deterministically
    var startX := -1;
    var startY := -1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant startX == -1 ==> forall ii :: 0 <= ii < i ==> forall jj :: 0 <= jj < m ==> grid[ii][jj] != 'X'
        invariant startX != -1 ==> 0 <= startX < n && 0 <= startY < m && grid[startX][startY] == 'X'
    {
        var j := 0;
        while j < m
            invariant 0 <= j <= m
            invariant startX == -1 ==> forall jj :: 0 <= jj < j ==> grid[i][jj] != 'X'
            invariant startX != -1 ==> 0 <= startX < n && 0 <= startY < m && grid[startX][startY] == 'X'
        {
            if grid[i][j] == 'X' {
                startX := i;
                startY := j;
                break;
            }
            j := j + 1;
        }
        if startX != -1 {
            break;
        }
        i := i + 1;
    }
    
    var validMoves: seq<char> := [];
    
    if startX + 1 < n && grid[startX + 1][startY] != '*' {
        validMoves := validMoves + ['D'];
    }
    if startX - 1 >= 0 && grid[startX - 1][startY] != '*' {
        validMoves := validMoves + ['U'];
    }
    if startY + 1 < m && grid[startX][startY + 1] != '*' {
        validMoves := validMoves + ['R'];
    }
    if startY - 1 >= 0 && grid[startX][startY - 1] != '*' {
        validMoves := validMoves + ['L'];
    }
    
    if |validMoves| == 0 {
        return "IMPOSSIBLE";
    }
    
    var move := validMoves[0];
    var opposite: char;
    
    if move == 'D' { opposite := 'U'; }
    else if move == 'U' { opposite := 'D'; }
    else if move == 'R' { opposite := 'L'; }
    else { opposite := 'R'; }
    
    var path := "";
    var steps := 0;
    while steps < k
        invariant 0 <= steps <= k
        invariant steps % 2 == 0
        invariant |path| == steps
        invariant ValidDirections(path)
        invariant SimulatePath(startX, startY, path, grid, n, m) == (startX, startY)
    {
        if steps + 2 <= k {
            var oldPath := path;
            TwoStepPathReturnsToStart(startX, startY, move, opposite, grid, n, m);
            PathConcatenationPreservesReturn(startX, startY, oldPath, [move, opposite], grid, n, m);
            ValidDirectionsPreserved(move, opposite, path);
            path := path + [move, opposite];
            steps := steps + 2;
        } else {
            break;
        }
    }
    
    return path;
}
// </vc-code>

