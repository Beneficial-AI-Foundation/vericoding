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

function FindXPosition(grid: seq<string>, n: int, m: int): (int, int)
    requires n > 0 && m > 0 && |grid| == n
    requires forall i :: 0 <= i < n ==> |grid[i]| == m
    requires exists i, j :: 0 <= i < n && 0 <= j < m && grid[i][j] == 'X'
{
    var i :| 0 <= i < n && exists j :: 0 <= j < m && grid[i][j] == 'X';
    var j :| 0 <= j < m && grid[i][j] == 'X';
    (i, j)
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
    
    var pos := FindXPosition(grid, n, m);
    var startX, startY := pos.0, pos.1;
    
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
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant i % 2 == 0
        invariant |path| == i
        invariant forall c :: c in path ==> c == move || c == opposite
    {
        if i + 1 < k {
            path := path + [move] + [opposite];
            i := i + 2;
        } else {
            break;
        }
    }
    
    return path;
}
// </vc-code>

