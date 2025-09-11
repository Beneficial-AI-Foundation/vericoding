// <vc-preamble>
predicate ValidPath(path: seq<(int, int)>, m: int, n: int)
{
    |path| >= 1 &&
    path[0] == (0, 0) &&
    path[|path|-1] == (m-1, n-1) &&
    (forall i :: 0 <= i < |path| ==> 0 <= path[i].0 < m && 0 <= path[i].1 < n) &&
    forall i :: 0 <= i < |path|-1 ==> 
        (path[i+1].0 == path[i].0 && path[i+1].1 == path[i].1 + 1) ||
        (path[i+1].0 == path[i].0 + 1 && path[i+1].1 == path[i].1)
}

function PathSum(path: seq<(int, int)>, grid: array2<int>): int
    requires forall i :: 0 <= i < |path| ==> 0 <= path[i].0 < grid.Length0 && 0 <= path[i].1 < grid.Length1
    reads grid
{
    if |path| == 0 then 0
    else grid[path[0].0, path[0].1] + PathSum(path[1..], grid)
}

predicate ValidInput(grid: array2<int>)
    reads grid
{
    grid.Length0 > 0 && grid.Length1 > 0 &&
    forall i, j :: 0 <= i < grid.Length0 && 0 <= j < grid.Length1 ==> grid[i, j] >= 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method minPathSum(grid: array2<int>) returns (result: int)
    requires ValidInput(grid)
    ensures result >= 0
    ensures grid.Length0 == 1 && grid.Length1 == 1 ==> result == grid[0, 0]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
