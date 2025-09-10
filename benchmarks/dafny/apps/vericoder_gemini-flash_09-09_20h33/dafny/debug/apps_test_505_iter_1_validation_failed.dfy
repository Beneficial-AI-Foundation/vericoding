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
predicate PathFormsCycle(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int)
    reads grid
{
    PathReturnsToStart(startX, startY, path, grid, n, m) &&
    ValidPath(startX, startY, path, grid, n, m)
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
    var startX := 0;
    var startY := 0;
    
    // Find the starting position 'X'
    for i := 0 to n-1
        ensures (exists x, y :: 0 <= x < n && 0 <= y < m && grid[x][y] == 'X' ==> 
                 (exists sx, sy :: 0 <= sx < n && 0 <= sy < m && grid[sx][sy] == 'X' && (sx != x || sy != y) ==> 
                  startX == i && startY == y
                 ) ||
                 (exists i_prime :: 0 <= i_prime < n && (exists j_prime :: 0 <= j_prime < m && grid[i_prime][j_prime] == 'X'))
                )
    {
        for j := 0 to m-1
            ensures (exists x, y :: 0 <= x < n && 0 <= y < m && grid[x][y] == 'X' ==> 
                     (exists sx, sy :: 0 <= sx < n && 0 <= sy < m && grid[sx][sy] == 'X' && (sx != x || sy != y) ==> 
                      (grid[i][j] == 'X' ==> startX == i && startY == j)
                     ) ||
                     (exists i_prime :: 0 <= i_prime < n && (exists j_prime :: 0 <= j_prime < m && grid[i_prime][j_prime] == 'X'))
                    )
        {
            if grid[i][j] == 'X' {
                startX := i;
                startY := j;
                break; // Found 'X', exit inner loop
            }
        }
        if grid[startX][startY] == 'X' {
            break; // Found 'X', exit outer loop
        }
    }

    if k % 2 == 1 {
        return "IMPOSSIBLE";
    }

    /*
     * We need to find a path of length k that returns to (startX, startY)
     * and only traverses valid cells (not '*').
     *
     * We can always construct a path of even length k >= 2 that returns
     * to the start if there's *any* valid adjacent cell.
     * For example, "DU" or "LD" or "R L".
     *
     * The problem implies a simple 4-directional grid movement.
     * A path of length k must return to start. If k is even, we can
     * always achieve this unless no moves are possible.
     *
     * Consider a simple 2-step cycle:
     * D -> U (if (startX+1, startY) is valid)
     * L -> R (if (startX, startY-1) is valid)
     * U -> D (if (startX-1, startY) is valid)
     * R -> L (if (startX, startY+1) is valid)
     *
     * If k >= 2 and there's at least one valid move from (startX, startY),
     * we can construct a path of length k.
     * E.g., if (startX+1, startY) is valid, then "DU" is a path of length 2.
     * For k > 2 and even, we can repeat "DU" (k/2) times.
     * E.g., for k=4, "DUDU".
     */
    
    // Check if there's any valid adjacent move
    var possibleMoves: seq<char> := [];
    
    // Try 'D'
    var nextD := GetNextPosition(startX, startY, 'D');
    if 0 <= nextD.0 < n && 0 <= nextD.1 < m && grid[nextD.0][nextD.1] != '*' {
        possibleMoves := possibleMoves + ['D'];
    }

    // Try 'L'
    var nextL := GetNextPosition(startX, startY, 'L');
    if 0 <= nextL.0 < n && 0 <= nextL.1 < m && grid[nextL.0][nextL.1] != '*' {
        possibleMoves := possibleMoves + ['L'];
    }

    // Try 'R'
    var nextR := GetNextPosition(startX, startY, 'R');
    if 0 <= nextR.0 < n && 0 <= nextR.1 < m && grid[nextR.0][nextR.1] != '*' {
        possibleMoves := possibleMoves + ['R'];
    }

    // Try 'U'
    var nextU := GetNextPosition(startX, startY, 'U');
    if 0 <= nextU.0 < n && 0 <= nextU.1 < m && grid[nextU.0][nextU.1] != '*' {
        possibleMoves := possibleMoves + ['U'];
    }
    
    if |possibleMoves| == 0 {
        // No valid moves from the start position. Cannot form any path.
        return "IMPOSSIBLE";
    }

    // Since k is even and there is at least one valid move, we can construct the path.
    // The simplest path is move-back. For example, "DU" or "LR".
    // We can always pick 'D' and 'U' if 'D' is valid.
    // If 'D' is not valid, pick 'L' and 'R' if 'L' is valid.
    // If 'L' is not valid, pick 'R' and 'L' if 'R' is valid.
    // If 'R' is not valid, pick 'U' and 'D' if 'U' is valid.
    // At least one of these pairs will be valid because |possibleMoves| > 0.
    
    var path_segment := "";
    if 'D' in possibleMoves && 'U' in possibleMoves {
        path_segment := "DU";
    } else if 'L' in possibleMoves && 'R' in possibleMoves {
        path_segment := "LR";
    } else if 'U' in possibleMoves && 'D' in possibleMoves { // This condition is technically covered by 'D' in possibleMoves, but written explicitly
        path_segment := "UD";
    } else if 'R' in possibleMoves && 'L' in possibleMoves { // This condition is technically covered by 'L' in possibleMoves, but written explicitly
        path_segment := "RL";
    } else {
        // If we can only move in one direction and not back, it's impossible to return in 2 steps.
        // Example: only 'D' is valid. 'DU' requires 'U' to be valid too.
        // This case should be handled.
        // Wait, the post-condition requires *a* path. Not necessarily a 2-step one.
        // If there's an isolated 'X' and k >= 2 and even, it's impossible.
        // However, we've established |possibleMoves| > 0.
        // Let's assume there's always a valid 2-step cycle if k is even, as long as there's a valid move.
        // This is a common assumption in these types of problems.
        // Example: If only 'D' is valid: we can create path like "DUDUDU..." which requires 'U' to be valid from (startX+1, startY).
        // It's not necessarily "XY" where Y is the reverse of X.
        // But the problem domain usually implies that reverse moves are valid if forward moves are.
        // Let's stick to the simplest interpretation, forming a simple 2-cycle if possible.

        // If 'D' is possible, 'U' is possible FROM (startX+1, startY) means we can form "DU"
        // But the current formulation of PathReturnsToStart and ValidPath requires path to be valid from start.
        // We only care what path we *return*. 
        //
        // If there's at least one adjacent valid cell (say (dx, dy)), then we can form an even cycle.
        // E.g., if (dx,dy) corresponds to 'D', then at least from (dx,dy) we can make a 'U' move to return to (startX, startY).
        // This is a strong assumption. Let's verify it.
        // For the current specification, `ValidPath` means every intermediate position is valid.
        // And `PathReturnsToStart` means the final position is start.

        // If this block is reached, it means we have a possible move, but its symmetric reverse is not among possibleMoves (from start).
        // E.g., 'D' is possible, but 'U' (from start) is not.
        // This means (startX+1, startY) is valid, but (startX-1, startY) is blocked.
        // In this case, we cannot simply use "DU" from start to illustrate.
        //
        // Let's reconsider. The problem doesn't simply ask that *a* path exists, but that *this specific* implementation finds it.
        // This is where "IMPOSSIBLE" makes sense.
        //
        // A minimal return path "RL" or "DU" requires two cells to be navigable.
        // If only one direction is possible from start without a direct return (e.g., only 'D' is valid),
        // we might get stuck searching for a simple pair.

        // The simplest solution is to use one of the available moves.
        // We know |possibleMoves| > 0.
        var moveChar := possibleMoves[0];
        var reversedMoveChar := ' ';
        if moveChar == 'D' then reversedMoveChar := 'U';
        else if moveChar == 'U' then reversedMoveChar := 'D';
        else if moveChar == 'L' then reversedMoveChar := 'R';
        else if moveChar == 'R' then reversedMoveChar := 'L';
        
        path_segment := "" + moveChar + reversedMoveChar;
        
        // This path segment (e.g., "DU") might still be problematic if the reversed move char
        // is not valid *from the original start position*.
        // Example: start is (0,0). Can move 'D' to (1,0). But cannot move 'U' from (0,0) (out of bounds).
        // In this specific condition (if `path_segment` doesn't form a full cycle that `ValidPath` accepts),
        // we MUST verify for k=2 it's valid.

        // The problem description has a crucial hint in the `k % 2 == 1` implies "IMPOSSIBLE".
        // This suggests there's always a solution for even k.
        // This is only true if the path chosen is guaranteed to be valid.
        //
        // To be safe, we must explicitly check two basic 2-step cycles.
        // Let's test "RL" and "DU". At least one must work if possible at all.
        // Smallest k is 0 - empty string. k=0 is even. "IMPOSSIBLE" is not valid for k=0.
        // The spec implies k >= 0. For k=0, result is "" (empty string). empty string IS a valid path that returns to start.
        if k == 0 {
            return "";
        }

        // For k > 0 and even.
        // Prefer "DU" if both D and U moves are possible FROM (startX, startY)
        // and both (startX+1, startY) and (startX, startY) are not '*'.
        // This is what ValidPath and PathReturnsToStart mean for "DU".
        var path_du := "DU";
        if PathFormsCycle(startX, startY, path_du, grid, n, m) {
            path_segment := path_du;
        } else {
            // Try "LR"
            var path_lr := "LR";
            if PathFormsCycle(startX, startY, path_lr, grid, n, m) {
                path_segment := path_lr;
            } else {
                // Try "UD"
                var path_ud := "UD";
                if PathFormsCycle(startX, startY, path_ud, grid, n, m) {
                    path_segment := path_ud;
                } else {
                    // Try "RL"
                    var path_rl := "RL";
                    if PathFormsCycle(startX, startY, path_rl, grid, n, m) {
                        path_segment := path_rl;
                    } else {
                        // This case means no simple two-step cycle exists from start.
                        // Can we find another path?
                        // For example, from (0,0), only 'D' is valid to (1,0). From (1,0), say 'R' to (1,1) is valid.
                        // Then from (1,1) 'U' to (0,1) is valid. From (0,1) 'L' to (0,0) is valid.
                        // This makes path "DRUL" of length 4.
                        // The specification requires us to return *a* such string if one exists.
                        // But finding an arbitrary path could be complicated (BFS/DFS).
                        //
                        // Given the nature of a competitive programming problem,
                        // if k is even and not 0, and there's a valid move,
                        // there must be a simple pattern solution.
                        // Typically, if an 'X' is not completely isolated (e.g. n=1, m=1, k=2),
                        // we can form a path.
                        // If n=1, m=1, grid=["X"], startX=0, startY=0. k=2. No moves possible. -> IMPOSSIBLE.
                        // Our current logic will correctly set `|possibleMoves| == 0`, leading to "IMPOSSIBLE".
                        //
                        // If n=2, m=1, grid=["X", "."], startX=0, startY=0. k=2. 'D' is valid.
                        // nextD is (1,0). From (1,0), a 'U' move will take us back to (0,0).
                        //
                        // Let's re-package the check for PathFormsCycle
                        //
                        // For path "DU": SimPath(0, "D") -> (1,0). SimPath(0, "DU") -> (0,0).
                        // ValidPath("DU"): SimPath(0,"") = (0,0) valid. SimPath(0,"D")=(1,0) valid. SimPath(0,"DU")=(0,0) valid.
                        // This means (0,0) must not be '*' and (1,0) must not be '*'.
                        //
                        // If (nextD.0, nextD.1) is valid AND (startX, startY) is valid for 'U' move FROM (nextD.0, nextD.1)
                        // Then "DU" path is valid.
                        // So the check 'D' in possibleMoves ensures `(startX+1, startY)` is not `*`.
                        // Then we need to check if a 'U' move from `(startX+1, startY)` leads to `(startX, startY)`
                        // and `grid[startX][startY]` is not `*`. Since grid[startX][startY] is 'X', it's not `*`.
                        // The critical point is if `U` is a valid move from `(startX+1, startY)`.
                        // This is implicit in the setup: `GetNextPosition` for these moves simply calculates coordinates.
                        // We need `0 <= pos.0 < n && 0 <= pos.1 < m` for `ValidPath`.

                        // The code should actually check that the *returned* sequence "XY" works.
                        // Not that X and Y are in 'possibleMoves' from start.

                        // Let's refine the logic for path_segment to guarantee one is found if possible.
                        // This implies that if `grid[currX][currY]` is not `'*'`, then moving outside the grid
                        // or to a `'*'` makes it an invalid path.

                        var currentPath := "";
                        var foundPath := false;
                        
                        var pathOptions: seq<string> := ["D", "L", "R", "U"];
                        
                        for i := 0 to |pathOptions|-1 {
                            var move1 := pathOptions[i];
                            var pos1 := GetNextPosition(startX, startY, move1);
                            
                            if 0 <= pos1.0 < n && 0 <= pos1.1 < m && grid[pos1.0][pos1.1] != '*' {
                                // First move is valid. Now try to find a second move that brings us back.
                                var pathOptions2: seq<string> := ["U", "R", "L", "D"]; // Reverse preference
                                for j := 0 to |pathOptions2|-1 {
                                    var move2 := pathOptions2[j];
                                    var pos2 := GetNextPosition(pos1.0, pos1.1, move2);
                                    
                                    if pos2.0 == startX && pos2.1 == startY {
                                        // This pair of moves returns to start.
                                        var testPath := "" + move1 + move2;
                                        if ValidPath(startX, startY, testPath, grid, n, m) {
                                            // This 2-step path is valid and returns to start.
                                            path_segment := testPath;
                                            foundPath := true;
                                            break;
                                        }
                                    }
                                }
                            }
                            if foundPath { break; }
                        }

                        if !foundPath {
                            return "IMPOSSIBLE";
                        }
                    }
                }
            }
        }
    
    var resultString := "";
    for i := 0 to k/2 - 1 {
        resultString := resultString + path_segment;
    }
    return resultString;
}
// </vc-code>

