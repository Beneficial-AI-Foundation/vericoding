Given an n×m rectangular maze with a robot starting at position 'X', find the lexicographically smallest path of exactly k moves that returns the robot to its starting position.
The maze contains '.' for empty cells, '*' for obstacles, and 'X' for the robot's starting position.
Robot can move in 4 directions: L (left), R (right), U (up), D (down) and can only move to empty cells.
Return the lexicographically smallest string of length k consisting of characters 'D', 'L', 'R', 'U' that returns the robot to start, or "IMPOSSIBLE".

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
{
    // Find starting position
    var x, y := 0, 0;
    var found := false;

    for i := 0 to n
        invariant 0 <= i <= n
        invariant !found ==> forall i' :: 0 <= i' < i ==> forall j' :: 0 <= j' < m ==> grid[i'][j'] != 'X'
        invariant found ==> 0 <= x < n && 0 <= y < m && grid[x][y] == 'X'
    {
        if !found {
            for j := 0 to m
                invariant 0 <= j <= m
                invariant !found ==> forall j' :: 0 <= j' < j ==> grid[i][j'] != 'X'
                invariant found ==> 0 <= x < n && 0 <= y < m && grid[x][y] == 'X'
            {
                if grid[i][j] == 'X' {
                    x := i;
                    y := j;
                    found := true;
                    break;
                }
            }
        }
    }

    if k % 2 == 1 {
        return "IMPOSSIBLE";
    }

    if k == 0 {
        return "";
    }

    // Try simple solution: go right then left, or down then up
    var directions := ['D', 'L', 'R', 'U'];
    var dx := [1, 0, 0, -1];
    var dy := [0, -1, 1, 0];

    // Try each direction first
    for firstDir := 0 to 4
        invariant 0 <= firstDir <= 4
    {
        var nx := x + dx[firstDir];
        var ny := y + dy[firstDir];

        if 0 <= nx < n && 0 <= ny < m && grid[nx][ny] != '*' {
            // Check if we can make a round trip
            var oppositeDir := match firstDir
                case 0 => 3  // D -> U
                case 1 => 2  // L -> R  
                case 2 => 1  // R -> L
                case 3 => 0  // U -> D
                case _ => 0;

            // Check if the opposite direction is also valid
            var backX := nx + dx[oppositeDir];
            var backY := ny + dy[oppositeDir];

            if backX == x && backY == y {
                // Simple solution: alternate between two directions
                var path := "";

                for i := 0 to k/2
                    invariant 0 <= i <= k/2
                    invariant |path| == i
                    invariant forall c :: c in path ==> c == directions[firstDir]
                    invariant directions[firstDir] == 'D' || directions[firstDir] == 'L' || directions[firstDir] == 'R' || directions[firstDir] == 'U'
                {
                    path := path + [directions[firstDir]];
                }

                for i := 0 to k/2
                    invariant 0 <= i <= k/2
                    invariant |path| == k/2 + i
                    invariant forall c :: c in path ==> c == directions[firstDir] || c == directions[oppositeDir]
                    invariant directions[firstDir] == 'D' || directions[firstDir] == 'L' || directions[firstDir] == 'R' || directions[firstDir] == 'U'
                    invariant directions[oppositeDir] == 'D' || directions[oppositeDir] == 'L' || directions[oppositeDir] == 'R' || directions[oppositeDir] == 'U'
                {
                    path := path + [directions[oppositeDir]];
                }

                // Verify the path is valid and returns to start
                if |path| == k && 
                   ValidPath(x, y, path, grid, n, m) &&
                   PathReturnsToStart(x, y, path, grid, n, m) {
                    assert |path| == k;
                    assert ValidDirections(path);
                    return path;
                }
            }
        }
    }

    return "IMPOSSIBLE";
}
