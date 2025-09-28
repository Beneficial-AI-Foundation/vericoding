// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_grid(grid: Seq<Seq<int>>) -> bool {
    grid.len() > 0 && grid[0].len() > 0 &&
    (forall|i: int| #![trigger grid[i].len(), grid[0].len()] 0 <= i < grid.len() ==> grid[i].len() == grid[0].len()) &&
    (forall|i: int, j: int| #![trigger grid[i][j]] 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 
        grid[i][j] == 0 || grid[i][j] == 1)
}

spec fn binomial(n: int, k: int) -> int
    decreases n, k
{
    if k > n || n < 0 || k < 0 {
        0int
    } else if k == 0 || k == n {
        1int
    } else if k == 1 {
        n
    } else {
        binomial(n-1, k-1) + binomial(n-1, k)
    }
}

spec fn dp_path_count(grid: Seq<Seq<int>>) -> int
    recommends valid_grid(grid)
{
    let m = grid.len();
    let n = grid[0].len();
    if grid[0][0] == 1 || grid[m-1][n-1] == 1 {
        0int
    } else if m == 1 && n == 1 {
        1int
    } else if m == 1 {
        if forall|j: int| #![trigger grid[0][j]] 0 <= j < n ==> grid[0][j] == 0 { 1int } else { 0int }
    } else if n == 1 {
        if forall|i: int| #![trigger grid[i][0]] 0 <= i < m ==> grid[i][0] == 0 { 1int } else { 0int }
    } else if forall|i: int, j: int| #![trigger grid[i][j]] 0 <= i < m && 0 <= j < n ==> grid[i][j] == 0 {
        binomial(m + n - 2, m - 1)
    } else {
        0int  /* placeholder for complex case */
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
exec fn unique_paths_with_obstacles(obstacle_grid: Vec<Vec<i8>>) -> (result: i8)
    requires 
        valid_grid(obstacle_grid@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int))),
    ensures 
        result >= 0,
        obstacle_grid@[0][0] == 1 ==> result == 0,
        obstacle_grid@[obstacle_grid@.len()-1][obstacle_grid@[0].len()-1] == 1 ==> result == 0,
        obstacle_grid@.len() == 1 && obstacle_grid@[0].len() == 1 ==> 
            result == (if obstacle_grid@[0][0] == 0 { 1i8 } else { 0i8 }),
        result as int == dp_path_count(obstacle_grid@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int))),
        (forall|i: int, j: int| #![trigger obstacle_grid@[i][j]] 0 <= i < obstacle_grid@.len() && 0 <= j < obstacle_grid@[0].len() ==> obstacle_grid@[i][j] == 0) ==> 
            result as int == binomial(obstacle_grid@.len() + obstacle_grid@[0].len() - 2, obstacle_grid@.len() - 1),
        obstacle_grid@.len() == 1 ==> 
            (result > 0 <==> (forall|j: int| #![trigger obstacle_grid@[0][j]] 0 <= j < obstacle_grid@[0].len() ==> obstacle_grid@[0][j] == 0)),
        obstacle_grid@[0].len() == 1 ==> 
            (result > 0 <==> (forall|i: int| #![trigger obstacle_grid@[i][0]] 0 <= i < obstacle_grid@.len() ==> obstacle_grid@[i][0] == 0))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type annotation for integer literal */
    let m = obstacle_grid.len();
    let n = obstacle_grid[0].len();
    
    if obstacle_grid[0][0] == 1 || obstacle_grid[m-1][n-1] == 1 {
        return 0;
    }
    
    if m == 1 && n == 1 {
        return 1;
    }
    
    let mut dp: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            dp@.len() == i,
            forall|k: int| 0 <= k < i ==> dp@[k].len() == n,
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                row@.len() == j,
        {
            row.push(0);
            j = j + 1;
        }
        dp.push(row);
        i = i + 1;
    }
    
    dp[0][0] = 1;
    
    let mut j: usize = 1;
    while j < n
        invariant
            1 <= j <= n,
            forall|k: int| 0 <= k < j ==> dp@[0][k] == if obstacle_grid@[0][k] == 1 || (k > 0 && dp@[0][k-1] == 0int) { 0int } else { 1int },
    {
        if obstacle_grid[0][j] == 1 {
            dp[0][j] = 0;
        } else {
            dp[0][j] = dp[0][j-1];
        }
        j = j + 1;
    }
    
    let mut i: usize = 1;
    while i < m
        invariant
            1 <= i <= m,
            forall|k: int| 0 <= k < i ==> dp@[k][0] == if obstacle_grid@[k][0] == 1 || (k > 0 && dp@[k-1][0] == 0int) { 0int } else { 1int },
    {
        if obstacle_grid[i][0] == 1 {
            dp[i][0] = 0;
        } else {
            dp[i][0] = dp[i-1][0];
        }
        i = i + 1;
    }
    
    let mut i: usize = 1;
    while i < m
        invariant
            1 <= i <= m,
    {
        let mut j: usize = 1;
        while j < n
            invariant
                1 <= j <= n,
        {
            if obstacle_grid[i][j] == 1 {
                dp[i][j] = 0;
            } else {
                let sum = dp[i-1][j] + dp[i][j-1];
                if sum > 127 {
                    dp[i][j] = 127;
                } else {
                    dp[i][j] = sum;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    dp[m-1][n-1]
}
// </vc-code>


}

fn main() {}