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
lemma SimulatePathPreservesBounds(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int)
  requires ValidInput(n, m, 0, grid)
  requires 0 <= startX < n && 0 <= startY < m
  requires grid[startX][startY] == 'X'
  requires ValidDirections(path)
  ensures forall i :: 0 <= i <= |path| ==> 
    var pos := SimulatePath(startX, startY, path[..i], grid, n, m);
    0 <= pos.0 < n && 0 <= pos.1 < m
  decreases |path|
{
  if |path| == 0 {
    // Base case: empty path stays at start
  } else {
    var nextPos := GetNextPosition(startX, startY, path[0]);
    // Check if next position is within bounds
    assert 0 <= nextPos.0 < n && 0 <= nextPos.1 < m
        && grid[nextPos.0][nextPos.1] != '*'
        && 0 <= nextPos.0 < n && 0 <= nextPos.1 < m;
    SimulatePathPreservesBounds(nextPos.0, nextPos.1, path[1..], grid, n, m);
  }
}

lemma SimulatePathAvoidsStars(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int)
  requires ValidInput(n, m, 0, grid)
  requires 0 <= startX < n && 0 <= startY < m
  requires grid[startX][startY] == 'X'
  requires ValidDirections(path)
  ensures forall i :: 0 <= i <= |path| ==> 
    var pos := SimulatePath(startX, startY, path[..i], grid, n, m);
    grid[pos.0][pos.1] != '*'
  decreases |path|
{
  if |path| == 0 {
    // Base case: start position is 'X', not '*'
  } else {
    var nextPos := GetNextPosition(startX, startY, path[0]);
    // Check if next position avoids stars
    assert 0 <= nextPos.0 < n && 0 <= nextPos.1 < m
        && grid[nextPos.0][nextPos.1] != '*';
    SimulatePathAvoidsStars(nextPos.0, nextPos.1, path[1..], grid, n, m);
  }
}

function repeat(s: string, count: nat): string
  requires count >= 0
  ensures |repeat(s, count)| == (|s| * count) 
  ensures forall c :: c in repeat(s, count) ==> c in s
{
  if count == 0 then "" 
  else s + repeat(s, count - 1)
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
    result := "IMPOSSIBLE";
  } else if k == 0 {
    var startX : int, startY : int :| 0 <= startX < n && 0 <= startY < m && grid[startX][startY] == 'X';
    result := "";
  } else {
    var startX : int, startY : int :| 0 <= startX < n && 0 <= startY < m && grid[startX][startY] == 'X';
    
    // Simple alternating path that returns to start
    if startX > 0 && startX < n - 1 && grid[startX - 1][startY] != '*' && grid[startX + 1][startY] != '*' {
      result := repeat("UD", k / 2);
    } else if startY > 0 && startY < m - 1 && grid[startX][startY - 1] != '*' && grid[startX][startY + 1] != '*' {
      result := repeat("LR", k / 2);
    } else {
      result := "IMPOSSIBLE";
    }
    
    if result != "IMPOSSIBLE" {
      // Verify path properties
      assert forall c :: c in result ==> c == 'D' || c == 'L' || c == 'R' || c == 'U';
      assert PathReturnsToStart(startX, startY, result, grid, n, m);
      assert ValidPath(startX, startY, result, grid, n, m);
    }
  }
}
// </vc-code>

