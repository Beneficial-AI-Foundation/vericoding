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
/* helper modified by LLM (iteration 5): No changes needed. Existing helper is fine. */
proof fn lemma_binomial_non_negative(n: int, k: int)
    ensures binomial(n, k) >= 0
    decreases n, k
{
    if k > n || n < 0 || k < 0 {
        // binomial is 0, which is >= 0
    } else if k == 0 || k == n {
        // binomial is 1, which is >= 0
    } else if k == 1 {
        // binomial is n. If n >= 0, then n >=0. We know n >= 0 here because k=1 implies n>=1
    } else {
        lemma_binomial_non_negative(n - 1, k - 1);
        lemma_binomial_non_negative(n - 1, k);
    }
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
/* code modified by LLM (iteration 5): Corrected type issues with Vec<int> initialization and access, and explicit `as int` casts for spec functions. */
{
    let m = obstacle_grid.len();
    let n = obstacle_grid[0].len();

    if m == 0 || n == 0 {
        return 0i8;
    }
    if obstacle_grid[0][0] == 1 || obstacle_grid[m - 1][n - 1] == 1 {
        return 0i8;
    }

    let mut dp: Vec<int> = vec![0int; n as usize];

    if obstacle_grid[0][0] == 0 {
        dp[0] = 1;
    }

    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i as int <= m as int,
            dp.len() == n,
            forall|idx: int| 0 <= idx < n as int ==> dp[idx as usize] >= 0,
        decreases m - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j as int <= n as int,
                dp.len() == n,
                forall|idx: int| 0 <= idx < n as int ==> dp[idx as usize] >= 0,
        decreases n - j
        {
            if obstacle_grid[i][j] == 1 {
                dp[j] = 0;
            } else if i > 0 && j == 0 {
                // If obstacle_grid[i][0] is not an obstacle, it inherits paths from dp[j] (which corresponds to dp[0] from the previous row).
                // If obstacle_grid[i][0] is an obstacle, dp[0] is already set to 0. So no change is needed. 
                // This line makes sure we only consider unique paths from the top (i-1).
                dp[j] = dp[j];
            } else if i == 0 && j > 0 {
                dp[j] = dp[j - 1];
            } else if i > 0 && j > 0 {
                dp[j] = dp[j] + dp[j - 1];
            }
            j = j + 1;
        }
        i = i + 1;
    }

    (dp[n - 1] as i8)
}
// </vc-code>


}

fn main() {}