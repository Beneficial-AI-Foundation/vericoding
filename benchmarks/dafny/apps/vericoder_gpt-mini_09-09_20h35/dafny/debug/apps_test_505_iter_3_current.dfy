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
lemma AlternatingPathLemma(startX:int, startY:int, dir: char, opp: char, path: string, grid: seq<string>, n:int, m:int)
  requires 0 <= startX < n && 0 <= startY < m
  requires grid[startX][startY] != '*'
  requires |path| % 2 == 0
  requires (forall i :: 0 <= i < |path| ==> (if i % 2 == 0 then path[i] == dir else path[i] == opp))
  requires (dir == 'D' || dir == 'U' || dir == 'L' || dir == 'R')
  requires ((dir == 'D' && opp == 'U') || (dir == 'U' && opp == 'D') || (dir == 'L' && opp == 'R') || (dir == 'R' && opp == 'L'))
  requires 0 <= GetNextPosition(startX, startY, dir).0 < n
  requires 0 <= GetNextPosition(startX, startY, dir).1 < m
  requires grid[GetNextPosition(startX, startY, dir).0][GetNextPosition(startX, startY, dir).1] != '*'
  decreases |path|
{
  if |path| == 0 {
    assert SimulatePath(startX, startY, "", grid, n, m) == (startX, startY);
    return;
  }

  // First two moves are dir then opp
  assert path[0] == dir && path[1] == opp;
  var nb := GetNextPosition(startX, startY, dir);
  var back := GetNextPosition(nb.0, nb.1, opp);
  // the two moves cancel out
  assert back == (startX, startY);

  // Unfold SimulatePath one step
  assert SimulatePath(startX, startY, path, grid, n, m) == SimulatePath(nb.0, nb.1, path[1..], grid, n, m);
  // Unfold SimulatePath the second step
  assert SimulatePath(nb.0, nb.1, path[1..], grid, n, m) == SimulatePath(back.0, back.1, path[2..], grid, n, m);
  // replace back with start
  assert SimulatePath(back.0, back.1, path[2..], grid, n, m) == SimulatePath(startX, startY, path[2..], grid, n, m);

  // apply induction on the remainder of the path
  AlternatingPathLemma(startX, startY, dir, opp, path[2..], grid, n, m);

  // conclude the full path returns to start
  assert SimulatePath(startX, startY, path, grid, n, m) == SimulatePath(startX, startY, path[2..], grid, n, m);
  assert SimulatePath(startX, startY, path[2..], grid, n, m) == (startX, startY);
  return;
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
        return;
    }

    var startX := 0;
    var startY := 0;
    var found := false;
    var i := 0;
    while i < n && !found {
        var j := 0;
        while j < m && !found {
            if grid[i][j] == 'X' {
                startX := i;
                startY := j;
                found := true;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    if k == 0 {
        result := "";
        return;
    }

    var dir := "";
    var opp := "";
    var ok := false;

    var nb := GetNextPosition(startX, startY, 'D');
    if 0 <= nb.0 && nb.0 < n && 0 <= nb.1 && nb.1 < m && grid[nb.0][nb.1] != '*' {
        dir := "D"; opp := "U"; ok := true;
    } else {
        nb := GetNextPosition(startX, startY, 'L');
        if 0 <= nb.0 && nb.0 < n && 0 <= nb.1 && nb.1 < m && grid[nb.0][nb.1] != '*' {
            dir := "L"; opp := "R"; ok := true;
        } else {
            nb := GetNextPosition(startX, startY, 'R');
            if 0 <= nb.0 && nb.0 < n && 0 <= nb.1 && nb.1 < m && grid[nb.0][nb.1] != '*' {
                dir := "R"; opp := "L"; ok := true;
            } else {
                nb := GetNextPosition(startX, startY, 'U');
                if 0 <= nb.0 && nb.0 < n && 0 <= nb.1 && nb.1 < m && grid[nb.0][nb.1] != '*' {
                    dir := "U"; opp := "D"; ok := true;
                }
            }
        }
    }

    if !ok {
        result := "IMPOSSIBLE";
        return;
    }

    var res := "";
    var times := k / 2;
    var t := 0;
    while t < times {
        res := res + dir;
        res := res + opp;
        t := t + 1;
    }

    // help the verifier: relate dir/opp strings to chars and nb
    assert dir != "";
    assert opp != "";
    assert 0 <= nb.0 && nb.0 < n && 0 <= nb.1 && nb.1 < m && grid[nb.0][nb.1] != '*';
    assert GetNextPosition(startX, startY, dir[0]) == nb;

    AlternatingPathLemma(startX, startY, dir[0], opp[0], res, grid, n, m);

    result := res;
    return;
}
// </vc-code>

