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
fn get_dp_value(dp: &Vec<Vec<i8>>, i: usize, j: usize) -> (result: i8)
    requires
        i < dp@.len(),
        j < dp@[i as int].len(),
    ensures
        result == dp@[i as int][j as int],
{
    dp[i][j]
}

fn sum_first_row(grid: &Vec<Vec<i8>>) -> (count: i8)
    requires
        grid@.len() > 0,
        grid@[0].len() > 0,
    ensures
        count >= 0,
        count <= 1,
        count == 1 <==> (forall|j: int| #![trigger grid@[0][j]] 0 <= j < grid@[0].len() ==> grid@[0][j] == 0),
{
    for i in 0..grid[0].len()
        invariant
            i <= grid[0].len(),
            i > 0 ==> (exists|k: int| 0 <= k < i && grid@[0][k] == 1) || (forall|k: int| #![trigger grid@[0][k]] 0 <= k < i ==> grid@[0][k] == 0),
    {
        if grid[0][i] == 1 {
            return 0;
        }
    }
    1
}

fn sum_first_col(grid: &Vec<Vec<i8>>) -> (count: i8)
    requires
        grid@.len() > 0,
        grid@[0].len() > 0,
    ensures
        count >= 0,
        count <= 1,
        count == 1 <==> (forall|i: int| #![trigger grid@[i][0]] 0 <= i < grid@.len() ==> grid@[i][0] == 0),
{
    for i in 0..grid.len()
        invariant
            i <= grid.len(),
            i > 0 ==> (exists|k: int| 0 <= k < i && grid@[k][0] == 1) || (forall|k: int| #![trigger grid@[k][0]] 0 <= k < i ==> grid@[k][0] == 0),
    {
        if grid[i][0] == 1 {
            return 0;
        }
    }
    1
}
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
    /* code modified by LLM (iteration 5): use mutable indexing instead of update method */
    let m = obstacle_grid.len();
    let n = obstacle_grid[0].len();
    
    if obstacle_grid[0][0] == 1 || obstacle_grid[m-1][n-1] == 1 {
        return 0;
    }
    
    if m == 1 && n == 1 {
        return 1;
    }
    
    if m == 1 {
        return sum_first_row(&obstacle_grid);
    }
    
    if n == 1 {
        return sum_first_col(&obstacle_grid);
    }
    
    let mut dp = Vec::with_capacity(m);
    for i in 0..m
        invariant
            i <= m,
            dp.len() == i,
    {
        let mut row = Vec::with_capacity(n);
        for j in 0..n
            invariant
                j <= n,
                row.len() == j,
        {
            row.push(0i8);
        }
        dp.push(row);
    }
    
    dp[0].set(0, 1i8);
    
    for i in 0..m
        invariant
            i <= m,
            dp.len() == m,
            forall|k: int| 0 <= k < m ==> dp@[k].len() == n,
    {
        for j in 0..n
            invariant
                j <= n,
                dp.len() == m,
                forall|k: int| 0 <= k < m ==> dp@[k].len() == n,
        {
            if obstacle_grid[i][j] == 1 {
                dp[i].set(j, 0i8);
            } else {
                let mut paths = 0i8;
                if i > 0 {
                    paths = paths + get_dp_value(&dp, i-1, j);
                }
                if j > 0 {
                    paths = paths + get_dp_value(&dp, i, j-1);
                }
                if i == 0 && j == 0 {
                    paths = 1;
                }
                dp[i].set(j, paths);
            }
        }
    }
    
    get_dp_value(&dp, m-1, n-1)
}
// </vc-code>


}

fn main() {}