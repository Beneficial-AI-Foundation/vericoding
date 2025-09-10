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
// <vc-helpers>
// Helpers here if needed
// </vc-helpers>
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
    var startX : nat := 0;
    var startY : nat := 0;
    for i : nat := 0 to n - 1 {
        for j : nat := 0 to m - 1 {
            if grid[i][j] == 'X' {
                startX := i;
                startY := j;
            }
        }
    }
    assert 0 <= startX < n && 0 <= startY < m;
    if k == 0 {
        return "";
    } else if k % 2 == 1 {
        return "IMPOSSIBLE";
    } else {
        var hasNeighbor := false;
        var moveOut := ' ';
        var moveBack := ' ';
        if startY + 1 < m {
            if grid[startX][startY + 1] == '.' {
                hasNeighbor := true;
                moveOut := 'R';
                moveBack := 'L';
            }
        }
        if !hasNeighbor && startX + 1 < n {
            if grid[startX + 1][startY] == '.' {
                hasNeighbor := true;
                moveOut := 'D';
                moveBack := 'U';
            }
        }
        if !hasNeighbor && startY > 0 {
            if grid[startX][startY - 1] == '.' {
                hasNeighbor := true;
                moveOut := 'L';
                moveBack := 'R';
            }
        }
        if !hasNeighbor && startX > 0 {
            if grid[startX - 1][startY] == '.' {
                hasNeighbor := true;
                moveOut := 'U';
                moveBack := 'D';
            }
        }
        if !hasNeighbor {
            return "IMPOSSIBLE";
        } else {
            var path := "";
            var steps := k / 2;
            for i : nat := 0 to steps - 1 {
                path := path + [moveOut];
                path := path + [moveBack];
            }
            assert ValidDirections(path);
            assert PathReturnsToStart(startX, startY, path, grid, n, m);
            assert ValidPath(startX, startY, path, grid, n, m);
            return path;
        }
    }
}
// </vc-code>

