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
predicate AllDirections(d: char)
{
    d == 'D' || d == 'L' || d == 'R' || d == 'U'
}

function FindTreasure(grid: seq<string>, n: int, m: int): (int, int)
    requires ValidInput(n, m, 0, grid)
    ensures 0 <= result.0 < n && 0 <= result.1 < m && grid[result.0][result.1] == 'X'
{
    reveal ValidInput();
    var i : int :| 0 <= i < n;
    var j : int :| 0 <= j < m && grid[i][j] == 'X';
    (i, j)
}

function ReverseDir(d: char): char
    requires AllDirections(d)
    ensures AllDirections(ReverseDir(d))
{
    match d
        case 'D' => 'U'
        case 'U' => 'D'
        case 'L' => 'R'
        case 'R' => 'L'
}

function IsValidCell(x: int, y: int, grid: seq<string>, n: int, m: int): bool
{
    0 <= x < n && 0 <= y < m && grid[x][y] != '*'
}

lemma {:autoInline} SimulatePathReturnsToStartLemma(path: string, reversePath: string, startX: int, startY: int, grid: seq<string>, n: int, m: int)
    requires ValidDirections(path)
    requires ValidDirections(reversePath)
    requires |reversePath| == |path|
    requires forall i :: 0 <= i < |path| ==> reversePath[i] == ReverseDir(path[|path|-1-i])
    requires ValidPath(startX, startY, path, grid, n, m)
    requires ValidPath(SimulatePath(startX, startY, path, grid, n, m).0, SimulatePath(startX, startY, path, grid, n, m).1, reversePath, grid, n, m)
    ensures PathReturnsToStart(startX, startY, path + reversePath, grid, n, m)
{
}

function ConstructPathForK(startX: int, startY: int, k: int, grid: seq<string>, n: int, m: int): string
    requires k > 0 && k % 2 == 0
    requires 0 <= startX < n && 0 <= startY < m
    requires grid[startX][startY] == 'X'
    requires |grid[0]| > 0
    requires forall i :: 0 <= i < n ==> |grid[i]| == m
    ensures |ConstructPathForK(startX, startY, k, grid, n, m)| == k
    ensures ValidDirections(ConstructPathForK(startX, startY, k, grid, n, m))
    decreases k
{
    if k == 0 then ""
    else
        var d1: char;
        var d2: char;
        if startX + 1 < n && IsValidCell(startX + 1, startY, grid, n, m) {
            d1 := 'D';
            d2 := 'U';
            ConstructPathForK(startX + 1, startY, k - 2, grid, n, m) + [d1, d2]
        }
        else if startX - 1 >= 0 && IsValidCell(startX - 1, startY, grid, n, m) {
            d1 := 'U';
            d2 := 'D';
            ConstructPathForK(startX - 1, startY, k - 2, grid, n, m) + [d1, d2]
        }
        else if startY + 1 < m && IsValidCell(startX, startY + 1, grid, n, m) {
            d1 := 'R';
            d2 := 'L';
            ConstructPathForK(startX, startY + 1, k - 2, grid, n, m) + [d1, d2]
        }
        else {
            d1 := 'L';
            d2 := 'R';
            ConstructPathForK(startX, startY - 1, k - 2, grid, n, m) + [d1, d2]
        }
}

lemma {:autoInline} ConstructPathForKIsValidLemma(startX: int, startY: int, k: int, grid: seq<string>, n: int, m: int)
    requires k > 0 && k % 2 == 0
    requires 0 <= startX < n && 0 <= startY < m
    requires grid[startX][startY] == 'X'
    requires ValidInput(n, m, 0, grid)
    ensures ValidPath(startX, startY, ConstructPathForK(startX, startY, k, grid, n, m), grid, n, m)
    ensures PathReturnsToStart(startX, startY, ConstructPathForK(startX, startY, k, grid, n, m), grid, n, m)
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
    
    var startX, startY := FindTreasure(grid, n, m);
    
    var p1, p2 := (startX + 1, startY), (startX - 1, startY);
    var p3, p4 := (startX, startY + 1), (startX, startY - 1);

    if !IsValidCell(p1.0, p1.1, grid, n, m) && !IsValidCell(p2.0, p2.1, grid, n, m) &&
       !IsValidCell(p3.0, p3.1, grid, n, m) && !IsValidCell(p4.0, p4.1, grid, n, m) {
        return "IMPOSSIBLE";
    }

    result := ConstructPathForK(startX, startY, k, grid, n, m);
    
    return result;
}
// </vc-code>

