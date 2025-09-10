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
lemma SimulatePathEmpty(x: int, y: int, grid: seq<string>, n: int, m: int)
    ensures SimulatePath(x, y, "", grid, n, m) == (x, y)
{
}

lemma SimulatePathConcat(x: int, y: int, path1: string, path2: string, grid: seq<string>, n: int, m: int)
    ensures SimulatePath(x, y, path1 + path2, grid, n, m) == 
            SimulatePath(SimulatePath(x, y, path1, grid, n, m).0, 
                        SimulatePath(x, y, path1, grid, n, m).1, path2, grid, n, m)
    decreases |path1|
{
    if |path1| == 0 {
        assert path1 + path2 == path2;
    } else {
        var nextPos := GetNextPosition(x, y, path1[0]);
        SimulatePathConcat(nextPos.0, nextPos.1, path1[1..], path2, grid, n, m);
    }
}

lemma OppositeMovesCancel(x: int, y: int, grid: seq<string>, n: int, m: int)
    ensures SimulatePath(x, y, "LR", grid, n, m) == (x, y)
    ensures SimulatePath(x, y, "RL", grid, n, m) == (x, y)
    ensures SimulatePath(x, y, "UD", grid, n, m) == (x, y)
    ensures SimulatePath(x, y, "DU", grid, n, m) == (x, y)
{
}

function RepeatPattern(pattern: string, times: int): string
    requires times >= 0
    decreases times
{
    if times == 0 then ""
    else pattern + RepeatPattern(pattern, times - 1)
}

lemma RepeatPatternLength(pattern: string, times: int)
    requires times >= 0
    ensures |RepeatPattern(pattern, times)| == |pattern| * times
{
    if times == 0 {
    } else {
        RepeatPatternLength(pattern, times - 1);
    }
}

lemma RepeatPatternValidDirections(pattern: string, times: int)
    requires times >= 0
    requires ValidDirections(pattern)
    ensures ValidDirections(RepeatPattern(pattern, times))
{
    if times == 0 {
    } else {
        RepeatPatternValidDirections(pattern, times - 1);
    }
}

lemma RepeatPatternReturns(x: int, y: int, pattern: string, times: int, grid: seq<string>, n: int, m: int)
    requires times >= 0
    requires pattern == "LR" || pattern == "RL" || pattern == "UD" || pattern == "DU"
    requires (pattern == "LR" || pattern == "RL" || pattern == "UD" || pattern == "DU") ==>
            SimulatePath(x, y, pattern, grid, n, m) == (x, y)
    ensures SimulatePath(x, y, RepeatPattern(pattern, times), grid, n, m) == (x, y)
    decreases times
{
    if times == 0 {
        SimulatePathEmpty(x, y, grid, n, m);
    } else {
        OppositeMovesCancel(x, y, grid, n, m);
        var path := RepeatPattern(pattern, times);
        assert path == pattern + RepeatPattern(pattern, times - 1);
        SimulatePathConcat(x, y, pattern, RepeatPattern(pattern, times - 1), grid, n, m);
        RepeatPatternReturns(x, y, pattern, times - 1, grid, n, m);
    }
}

lemma SimulatePathPrefix(x: int, y: int, path: string, i: int, grid: seq<string>, n: int, m: int)
    requires 0 <= i <= |path|
    requires |path| >= 2
    requires path[0] in "LRUD"
    ensures i == 0 ==> SimulatePath(x, y, path[..i], grid, n, m) == (x, y)
    ensures i == 1 && path[0] == 'L' ==> SimulatePath(x, y, path[..i], grid, n, m) == (x, y - 1)
    ensures i == 1 && path[0] == 'R' ==> SimulatePath(x, y, path[..i], grid, n, m) == (x, y + 1)
    ensures i == 1 && path[0] == 'U' ==> SimulatePath(x, y, path[..i], grid, n, m) == (x - 1, y)
    ensures i == 1 && path[0] == 'D' ==> SimulatePath(x, y, path[..i], grid, n, m) == (x + 1, y)
{
}

lemma ValidPathLeftRight(x: int, y: int, times: int, grid: seq<string>, n: int, m: int)
    requires 0 <= x < n && 0 <= y < m
    requires times >= 0
    requires y > 0 && 0 <= x < |grid| && 0 <= y - 1 < |grid[x]| && grid[x][y - 1] != '*'
    requires |grid| == n && (forall i :: 0 <= i < n ==> |grid[i]| == m)
    ensures ValidPath(x, y, RepeatPattern("LR", times), grid, n, m)
    decreases times
{
    if times == 0 {
        assert RepeatPattern("LR", 0) == "";
        forall i | 0 <= i <= 0
            ensures var pos := SimulatePath(x, y, ""[..i], grid, n, m);
                    0 <= pos.0 < n && 0 <= pos.1 < m && 
                    pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
                    grid[pos.0][pos.1] != '*'
        {
            assert i == 0;
            var pos := SimulatePath(x, y, "", grid, n, m);
            assert pos == (x, y);
            assert grid[x][y] == 'X';
        }
    } else {
        var path := RepeatPattern("LR", times);
        forall i | 0 <= i <= |path|
            ensures var pos := SimulatePath(x, y, path[..i], grid, n, m);
                    0 <= pos.0 < n && 0 <= pos.1 < m && 
                    pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
                    grid[pos.0][pos.1] != '*'
        {
            if i == 0 {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y);
                assert grid[x][y] != '*';
            } else if i % 2 == 1 {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y - 1) || pos == (x, y);
                if pos == (x, y - 1) {
                    assert grid[x][y - 1] != '*';
                }
            } else {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y);
                assert grid[x][y] != '*';
            }
        }
    }
}

lemma ValidPathRightLeft(x: int, y: int, times: int, grid: seq<string>, n: int, m: int)
    requires 0 <= x < n && 0 <= y < m
    requires times >= 0
    requires y < m - 1 && 0 <= x < |grid| && 0 <= y + 1 < |grid[x]| && grid[x][y + 1] != '*'
    requires |grid| == n && (forall i :: 0 <= i < n ==> |grid[i]| == m)
    ensures ValidPath(x, y, RepeatPattern("RL", times), grid, n, m)
    decreases times
{
    if times == 0 {
        assert RepeatPattern("RL", 0) == "";
        forall i | 0 <= i <= 0
            ensures var pos := SimulatePath(x, y, ""[..i], grid, n, m);
                    0 <= pos.0 < n && 0 <= pos.1 < m && 
                    pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
                    grid[pos.0][pos.1] != '*'
        {
            assert i == 0;
            var pos := SimulatePath(x, y, "", grid, n, m);
            assert pos == (x, y);
            assert grid[x][y] == 'X';
        }
    } else {
        var path := RepeatPattern("RL", times);
        forall i | 0 <= i <= |path|
            ensures var pos := SimulatePath(x, y, path[..i], grid, n, m);
                    0 <= pos.0 < n && 0 <= pos.1 < m && 
                    pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
                    grid[pos.0][pos.1] != '*'
        {
            if i == 0 {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y);
                assert grid[x][y] != '*';
            } else if i % 2 == 1 {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y + 1) || pos == (x, y);
                if pos == (x, y + 1) {
                    assert grid[x][y + 1] != '*';
                }
            } else {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y);
                assert grid[x][y] != '*';
            }
        }
    }
}

lemma ValidPathUpDown(x: int, y: int, times: int, grid: seq<string>, n: int, m: int)
    requires 0 <= x < n && 0 <= y < m
    requires times >= 0
    requires x > 0 && 0 <= x - 1 < |grid| && 0 <= y < |grid[x - 1]| && grid[x - 1][y] != '*'
    requires |grid| == n && (forall i :: 0 <= i < n ==> |grid[i]| == m)
    ensures ValidPath(x, y, RepeatPattern("UD", times), grid, n, m)
    decreases times
{
    if times == 0 {
        assert RepeatPattern("UD", 0) == "";
        forall i | 0 <= i <= 0
            ensures var pos := SimulatePath(x, y, ""[..i], grid, n, m);
                    0 <= pos.0 < n && 0 <= pos.1 < m && 
                    pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
                    grid[pos.0][pos.1] != '*'
        {
            assert i == 0;
            var pos := SimulatePath(x, y, "", grid, n, m);
            assert pos == (x, y);
            assert grid[x][y] == 'X';
        }
    } else {
        var path := RepeatPattern("UD", times);
        forall i | 0 <= i <= |path|
            ensures var pos := SimulatePath(x, y, path[..i], grid, n, m);
                    0 <= pos.0 < n && 0 <= pos.1 < m && 
                    pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
                    grid[pos.0][pos.1] != '*'
        {
            if i == 0 {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y);
                assert grid[x][y] != '*';
            } else if i % 2 == 1 {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x - 1, y) || pos == (x, y);
                if pos == (x - 1, y) {
                    assert grid[x - 1][y] != '*';
                }
            } else {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y);
                assert grid[x][y] != '*';
            }
        }
    }
}

lemma ValidPathDownUp(x: int, y: int, times: int, grid: seq<string>, n: int, m: int)
    requires 0 <= x < n && 0 <= y < m
    requires times >= 0
    requires x < n - 1 && 0 <= x + 1 < |grid| && 0 <= y < |grid[x + 1]| && grid[x + 1][y] != '*'
    requires |grid| == n && (forall i :: 0 <= i < n ==> |grid[i]| == m)
    ensures ValidPath(x, y, RepeatPattern("DU", times), grid, n, m)
    decreases times
{
    if times == 0 {
        assert RepeatPattern("DU", 0) == "";
        forall i | 0 <= i <= 0
            ensures var pos := SimulatePath(x, y, ""[..i], grid, n, m);
                    0 <= pos.0 < n && 0 <= pos.1 < m && 
                    pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
                    grid[pos.0][pos.1] != '*'
        {
            assert i == 0;
            var pos := SimulatePath(x, y, "", grid, n, m);
            assert pos == (x, y);
            assert grid[x][y] == 'X';
        }
    } else {
        var path := RepeatPattern("DU", times);
        forall i | 0 <= i <= |path|
            ensures var pos := SimulatePath(x, y, path[..i], grid, n, m);
                    0 <= pos.0 < n && 0 <= pos.1 < m && 
                    pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
                    grid[pos.0][pos.1] != '*'
        {
            if i == 0 {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y);
                assert grid[x][y] != '*';
            } else if i % 2 == 1 {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x + 1, y) || pos == (x, y);
                if pos == (x + 1, y) {
                    assert grid[x + 1][y] != '*';
                }
            } else {
                var pos := SimulatePath(x, y, path[..i], grid, n, m);
                assert pos == (x, y);
                assert grid[x][y] != '*';
            }
        }
    }
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
    
    // Find the starting position 'X'
    var startX := -1;
    var startY := -1;
    var i := 0;
    
    while i < n && startX == -1
        invariant 0 <= i <= n
        invariant startX == -1 ==> forall ii, jj :: 0 <= ii < i && 0 <= jj < m ==> grid[ii][jj] != 'X'
        invariant startX != -1 ==> 0 <= startX < n && 0 <= startY < m && grid[startX][startY] == 'X'
    {
        var j := 0;
        while j < m && startX == -1
            invariant 0 <= j <= m
            invariant startX == -1 ==> forall jj :: 0 <= jj < j ==> grid[i][jj] != 'X'
            invariant startX != -1 ==> 0 <= startX < n && 0 <= startY < m && grid[startX][startY] == 'X'
        {
            if grid[i][j] == 'X' {
                startX := i;
                startY := j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    assert startX != -1 && startY != -1;
    assert 0 <= startX < n && 0 <= startY < m && grid[startX][startY] == 'X';
    
    if k == 0 {
        return "";
    }
    
    // Try simple back-and-forth movements
    // Try left-right
    if startY > 0 && grid[startX][startY - 1] != '*' {
        var path := RepeatPattern("LR", k / 2);
        RepeatPatternLength("LR", k / 2);
        assert |path| == 2 * (k / 2) == k;
        
        assert ValidDirections("LR");
        RepeatPatternValidDirections("LR", k / 2);
        assert ValidDirections(path);
        
        // Verify this path works
        assert PathReturnsToStart(startX, startY, path, grid, n, m) by {
            var halfSteps := k / 2;
            assert path == RepeatPattern("LR", halfSteps);
            RepeatPatternReturns(startX, startY, "LR", halfSteps, grid, n, m);
        }
        
        assert ValidPath(startX, startY, path, grid, n, m) by {
            ValidPathLeftRight(startX, startY, k/2, grid, n, m);
        }
        
        return path;
    }
    
    // Try right-left
    if startY < m - 1 && grid[startX][startY + 1] != '*' {
        var path := RepeatPattern("RL", k / 2);
        RepeatPatternLength("RL", k / 2);
        assert |path| == 2 * (k / 2) == k;
        
        assert ValidDirections("RL");
        RepeatPatternValidDirections("RL", k / 2);
        assert ValidDirections(path);
        
        assert PathReturnsToStart(startX, startY, path, grid, n, m) by {
            var halfSteps := k / 2;
            assert path == RepeatPattern("RL", halfSteps);
            RepeatPatternReturns(startX, startY, "RL", halfSteps, grid, n, m);
        }
        
        assert ValidPath(startX, startY, path, grid, n, m) by {
            ValidPathRightLeft(startX, startY, k/2, grid, n, m);
        }
        
        return path;
    }
    
    // Try up-down
    if startX > 0 && grid[startX - 1][startY] != '*' {
        var path := RepeatPattern("UD", k / 2);
        RepeatPatternLength("UD", k / 2);
        assert |path| == 2 * (k / 2) == k;
        
        assert ValidDirections("UD");
        RepeatPatternValidDirections("UD", k / 2);
        assert ValidDirections(path);
        
        assert PathReturnsToStart(startX, startY, path, grid, n, m) by {
            var halfSteps := k / 2;
            assert path == RepeatPattern("UD", halfSteps);
            RepeatPatternReturns(startX, startY, "UD", halfSteps, grid, n, m);
        }
        
        assert ValidPath(startX, startY, path, grid, n, m) by {
            ValidPathUpDown(startX, startY, k/2, grid, n, m);
        }
        
        return path;
    }
    
    // Try down-up
    if startX < n - 1 && grid[startX + 1][startY] != '*' {
        var path := RepeatPattern("DU", k / 2);
        RepeatPatternLength("DU", k / 2);
        assert |path| == 2 * (k / 2) == k;
        
        assert ValidDirections("DU");
        RepeatPatternValidDirections("DU", k / 2);
        assert ValidDirections(path);
        
        assert PathReturnsToStart(startX, startY, path, grid, n, m) by {
            var halfSteps := k / 2;
            assert path == RepeatPattern("DU", halfSteps);
            RepeatPatternReturns(startX, startY, "DU", halfSteps, grid, n, m);
        }
        
        assert ValidPath(startX, startY, path, grid, n, m) by {
            ValidPathDownUp(startX, startY, k/2, grid, n, m);
        }
        
        return path;
    }
    
    return "IMPOSSIBLE";
}
// </vc-code>

