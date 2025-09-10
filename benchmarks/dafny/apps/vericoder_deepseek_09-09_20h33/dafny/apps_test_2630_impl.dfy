predicate ValidGrid(grid: seq<seq<int>>)
{
    |grid| > 0 && |grid[0]| > 0 &&
    (forall i :: 0 <= i < |grid| ==> |grid[i]| == |grid[0]|) &&
    (forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] in {0, 1})
}

function DPPathCount(grid: seq<seq<int>>): int
    requires ValidGrid(grid)
    ensures DPPathCount(grid) >= 0
    ensures grid[0][0] == 1 ==> DPPathCount(grid) == 0
    ensures grid[|grid|-1][|grid[0]|-1] == 1 ==> DPPathCount(grid) == 0
    ensures |grid| == 1 && |grid[0]| == 1 ==> 
            DPPathCount(grid) == (if grid[0][0] == 0 then 1 else 0)
    ensures (forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[0]| ==> grid[i][j] == 0) ==> 
            DPPathCount(grid) == Binomial(|grid| + |grid[0]| - 2, |grid| - 1)
    ensures |grid| == 1 ==> 
            (DPPathCount(grid) > 0 <==> (forall j :: 0 <= j < |grid[0]| ==> grid[0][j] == 0))
    ensures |grid[0]| == 1 ==> 
            (DPPathCount(grid) > 0 <==> (forall i :: 0 <= i < |grid| ==> grid[i][0] == 0))
{
    var m := |grid|;
    var n := |grid[0]|;
    if grid[0][0] == 1 || grid[m-1][n-1] == 1 then 0
    else 
        if m == 1 && n == 1 then 1
        else if m == 1 then 
            if forall j :: 0 <= j < n ==> grid[0][j] == 0 then 1 else 0
        else if n == 1 then
            if forall i :: 0 <= i < m ==> grid[i][0] == 0 then 1 else 0
        else if forall i, j :: 0 <= i < m && 0 <= j < n ==> grid[i][j] == 0 then
            Binomial(m + n - 2, m - 1)
        else
            var path := InitializePath(grid);
            ComputePaths(grid, path, m, n)
}

function Binomial(n: int, k: int): int
    requires n >= 0 && k >= 0
    ensures Binomial(n, k) >= 0
    decreases n, k
{
    if k > n then 0
    else if k == 0 || k == n then 1
    else if k == 1 then n
    else Binomial(n-1, k-1) + Binomial(n-1, k)
}

// <vc-helpers>
predicate ValidCell(grid: seq<seq<int>>, i: int, j: int) 
    requires ValidGrid(grid)
{
    0 <= i < |grid| && 0 <= j < |grid[0]| && grid[i][j] == 0
}

ghost function FillDP(grid: seq<seq<int>>, dp: array2<int>, m: int, n: int): bool
    requires ValidGrid(grid)
    requires dp != null
    requires dp.Length0 == m && dp.Length1 == n
{
    dp[0, 0] == (if grid[0][0] == 0 then 1 else 0) &&
    (forall i, j :: 0 <= i < m && 0 <= j < n ==>
        (if i == 0 && j == 0 then true
        else if i == 0 then dp[i, j] == (if grid[i][j] == 0 then dp[i, j-1] else 0)
        else if j == 0 then dp[i, j] == (if grid[i][j] == 0 then dp[i-1, j] else 0)
        else dp[i, j] == (if grid[i][j] == 0 then dp[i-1, j] + dp[i, j-1] else 0)))
}

lemma FillDPInvariant(grid: seq<seq<int>>, dp: array2<int>, i: int, j: int, m: int, n: int)
    requires ValidGrid(grid)
    requires dp != null && dp.Length0 == m && dp.Length1 == n
    requires 0 <= i < m && 0 <= j < n
    requires dp[0, 0] == (if grid[0][0] == 0 then 1 else 0)
    requires forall ii, jj :: 0 <= ii <= i && 0 <= jj <= j ==> 
        (if ii == 0 && jj == 0 then true
         else if ii == 0 then dp[ii, jj] == (if grid[ii][jj] == 0 then dp[ii, jj-1] else 0)
         else if jj == 0 then dp[ii, jj] == (if grid[ii][jj] == 0 then dp[ii-1, jj] else 0)
         else dp[ii, jj] == (if grid[ii][jj] == 0 then dp[ii-1, jj] + dp[ii, jj-1] else 0))
    ensures forall ii, jj :: 0 <= ii <= i && 0 <= jj <= j ==>
        dp[ii][jj] == DPPathCount(grid[0..ii+1][0..jj+1])
{
}

function InitializePath(grid: seq<seq<int>>): (path: array2<int>)
    requires ValidGrid(grid)
    ensures path != null
    ensures path.Length0 == |grid| && path.Length1 == |grid[0]|
    ensures FillDP(grid, path, |grid|, |grid[0]|)
{
    var m := |grid|;
    var n := |grid[0]|;
    var dp : array2<int> := new int[m, n];
    if grid[0][0] == 0 {
        dp[0, 0] := 1;
    } else {
        dp[0, 0] := 0;
    }
    dp
}

method ComputePaths(grid: seq<seq<int>>, dp: array2<int>, m: int, n: int) returns (count: int)
    requires ValidGrid(grid)
    requires dp != null && dp.Length0 == m && dp.Length1 == n
    requires FillDP(grid, dp, m, n)
    ensures count == DPPathCount(grid)
{
    count := dp[m-1, n-1];
}
// </vc-helpers>

// <vc-spec>
method uniquePathsWithObstacles(obstacleGrid: seq<seq<int>>) returns (result: int)
    requires ValidGrid(obstacleGrid)
    ensures result >= 0
    ensures obstacleGrid[0][0] == 1 ==> result == 0
    ensures obstacleGrid[|obstacleGrid|-1][|obstacleGrid[0]|-1] == 1 ==> result == 0
    ensures |obstacleGrid| == 1 && |obstacleGrid[0]| == 1 ==> 
            result == (if obstacleGrid[0][0] == 0 then 1 else 0)
    ensures result == DPPathCount(obstacleGrid)
    ensures (forall i, j :: 0 <= i < |obstacleGrid| && 0 <= j < |obstacleGrid[0]| ==> obstacleGrid[i][j] == 0) ==> 
            result == Binomial(|obstacleGrid| + |obstacleGrid[0]| - 2, |obstacleGrid| - 1)
    ensures |obstacleGrid| == 1 ==> 
            (result > 0 <==> (forall j :: 0 <= j < |obstacleGrid[0]| ==> obstacleGrid[0][j] == 0))
    ensures |obstacleGrid[0]| == 1 ==> 
            (result > 0 <==> (forall i :: 0 <= i < |obstacleGrid| ==> obstacleGrid[i][0] == 0))
// </vc-spec>
// <vc-code>
{
    var m := |obstacleGrid|;
    var n := |obstacleGrid[0]|;
    
    if obstacleGrid[0][0] == 1 || obstacleGrid[m-1][n-1] == 1 {
        result := 0;
    } else if m == 1 && n == 1 {
        result := 1;
    } else {
        var dp : array2<int> := new int[m, n];
        
        dp[0, 0] := 1;
        
        var j := 1;
        while j < n
            invariant 1 <= j <= n
            invariant forall jj :: 0 <= jj < j ==> 
                dp[0, jj] == (if obstacleGrid[0][jj] == 0 then (if jj == 0 then 1 else dp[0, jj-1]) else 0)
        {
            if obstacleGrid[0][j] == 0 {
                dp[0, j] := dp[0, j-1];
            } else {
                dp[0, j] := 0;
            }
            j := j + 1;
        }
        
        var i := 1;
        while i < m
            invariant 1 <= i <= m
            invariant forall ii :: 0 <= ii < i ==> 
                dp[ii, 0] == (if obstacleGrid[ii][0] == 0 then (if ii == 0 then 1 else dp[ii-1, 0]) else 0)
        {
            if obstacleGrid[i][0] == 0 {
                dp[i, 0] := dp[i-1, 0];
            } else {
                dp[i, 0] := 0;
            }
            i := i + 1;
        }
        
        i := 1;
        while i < m
            invariant 1 <= i <= m
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> 
                dp[ii, jj] == (if obstacleGrid[ii][jj] == 0 then 
                    (if ii == 0 then (if jj == 0 then 1 else dp[ii, jj-1]) 
                    else if jj == 0 then dp[ii-1, jj]
                    else dp[ii-1, jj] + dp[ii, jj-1]) 
                else 0)
        {
            j := 1;
            while j < n
                invariant 1 <= j <= n
                invariant forall jj :: 0 <= jj < j ==> 
                    dp[i, jj] == (if obstacleGrid[i][jj] == 0 then 
                        (if i == 0 then (if jj == 0 then 1 else dp[i, jj-1]) 
                        else if jj == 0 then dp[i-1, jj]
                        else dp[i-1, jj] + dp[i, jj-1]) 
                    else 0)
                invariant forall ii :: 0 <= ii < i ==> forall jj :: 0 <= jj < n ==> 
                    dp[ii, jj] == (if obstacleGrid[ii][jj] == 0 then 
                        (if ii == 0 then (if jj == 0 then 1 else dp[ii, jj-1]) 
                        else if jj == 0 then dp[ii-1, jj]
                        else dp[ii-1, jj] + dp[ii, jj-1]) 
                    else 0)
            {
                if obstacleGrid[i][j] == 0 {
                    dp[i, j] := dp[i-1, j] + dp[i, j-1];
                } else {
                    dp[i, j] := 0;
                }
                j := j + 1;
            }
            i := i + 1;
        }
        
        result := dp[m-1, n-1];
    }
}
// </vc-code>

