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
predicate {:opaque} CanReachStartInKSteps(startX: int, startY: int, k: int, grid: seq<string>, n: int, m: int, path: string)
    reads grid
{
    |path| == k &&
    ValidDirections(path) &&
    ValidPath(startX, startY, path, grid, n, m) &&
    PathReturnsToStart(startX, startY, path, grid, n, m)
}

function GetStartPos(grid: seq<string>): (int, int)
    requires (exists i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| && grid[i][j] == 'X')
    returns (x', y')
    ensures grid[x'][y'] == 'X'
{
    var x := 0;
    var y := 0;
    while x < |grid|
        invariant 0 <= x <= |grid|
        invariant (exists i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| && grid[i][j] == 'X') ==>
            (exists i',j' :: (0 <= i' < x && 0 <= j' < |grid[i']|) || (i' == x && 0 <= j' < y && x < |grid| && y < |grid[x]| && x >= 0 && y >= 0) && grid[i'][j'] == 'X') ||
            (exists i',j' :: 0 <= i' < |grid| && 0 <= j' < |grid[i']| && grid[i'][j'] == 'X' &&
            !( (0 <= i' < x && 0 <= j' < |grid[i']|) || (i' == x && 0 <= j' < y) ) )
    {
        y := 0;
        while y < |grid[x]|
            invariant 0 <= x < |grid|
            invariant 0 <= y <= |grid[x]|
            invariant (exists i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| && grid[i][j] == 'X') ==>
            (exists i',j' :: (0 <= i' < x && 0 <= j' < |grid[i']|) || (i' == x && 0 <= j' < y && x < |grid| && y < |grid[x]| && x >= 0 && y >= 0) && grid[i'][j'] == 'X') ||
            (exists i',j' :: 0 <= i' < |grid| && 0 <= j' < |grid[i']| && grid[i'][j'] == 'X' &&
            !( (0 <= i' < x && 0 <= j' < |grid[i']|) || (i' == x && 0 <= j' < y) ) )
        {
            if grid[x][y] == 'X' then
                return (x, y);
            y := y + 1;
        }
        x := x + 1;
    }
    // This part should be unreachable due to the precondition
    (0,0) // provide a dummy return to satisfy Dafny's exhaustiveness checker
}

method {:induction k} FindPath(startX: int, startY: int, k: int, grid: seq<string>, n: int, m: int) returns (result_path: string)
    requires 0 <= startX < n && 0 <= startY < m
    requires n > 0 && m > 0
    requires (forall i :: 0 <= i < n ==> |grid[i]| == m)
    requires (forall i :: 0 <= i < n ==> forall c :: c in grid[i] ==> c == '.' || c == '*' || c == 'X')
    decreases k
    ensures k % 2 == 1 ==> result_path == "IMPOSSIBLE"
    ensures k % 2 == 0 ==> (
        result_path == "IMPOSSIBLE" ||
        CanReachStartInKSteps(startX, startY, k, grid, n, m, result_path)
    )
{
    if k == 0 then
        result_path := "";
        return;
    if k == 1 then
        result_path := "IMPOSSIBLE";
        return;
    
    // Check for k % 2 == 1
    if k % 2 == 1 {
        result_path := "IMPOSSIBLE";
        return;
    }

    var directions := ['D', 'L', 'R', 'U'];
    var dx := [1, 0, 0, -1];
    var dy := [0, -1, 1, 0];
    
    var i := 0;
    while i < |directions|
        invariant 0 <= i <= |directions|
        invariant k % 2 == 0 ==> (
            forall dir_idx :: 0 <= dir_idx < i ==>
            var next_x0 := startX + dx[dir_idx];
            var next_y0 := startY + dy[dir_idx];
            (next_x0 < 0 || next_x0 >= n || next_y0 < 0 || next_y0 >= m || grid[next_x0][next_y0] == '*' ||
            (FindPath(next_x0, next_y0, k - 2, grid, n, m) == "IMPOSSIBLE" ||
             (exists pth: string :: FindPath(next_x0, next_y0, k - 2, grid, n, m) == pth &&
                           directions[dir_idx] + pth + directions[3 - dir_idx] != "IMPOSSIBLE" ==>
                           CanReachStartInKSteps(startX, startY, k, grid, n, m, directions[dir_idx] + pth + directions[3 - dir_idx]))
            ))
        )
    {
        var current_dir := directions[i];
        var opp_dir := directions[3-i]; // 'D'->'U', 'L'->'R', 'R'->'L', 'U'->'D'

        var next_x := startX + dx[i];
        var next_y := startY + dy[i];

        if 0 <= next_x < n && 0 <= next_y < m && grid[next_x][next_y] != '*' {
            var sub_path := FindPath(next_x, next_y, k - 2, grid, n, m);
            if sub_path != "IMPOSSIBLE" {
                // Ensure the return path gets back to start (next_x, next_y)
                var final_x1 := 0; var final_y1 := 0;
                var temp_tuple := SimulatePath(next_x, next_y, sub_path, grid, n, m);
                final_x1 := temp_tuple.0;
                final_y1 := temp_tuple.1;

                if final_x1 == next_x && final_y1 == next_y {
                    // Check if a move back makes sense
                    var final_x2 := 0; var final_y2 := 0;
                    var temp_tuple2 := GetNextPosition(final_x1, final_y1, opp_dir);
                    final_x2 := temp_tuple2.0;
                    final_y2 := temp_tuple2.1;

                    if final_x2 == startX && final_y2 == startY {
                        result_path := current_dir + sub_path + opp_dir;
                        return;
                    }
                }
            }
        }
        i := i + 1;
    }
    result_path := "IMPOSSIBLE";
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
    if k % 2 == 1 then
        return "IMPOSSIBLE";
    
    var startX_var := 0;
    var startY_var := 0;
    
    var start_pos := GetStartPos(grid);
    startX_var := start_pos.0;
    startY_var := start_pos.1;
    
    // Call the recursive helper function
    return FindPath(startX_var, startY_var, k, grid, n, m);
}
// </vc-code>

