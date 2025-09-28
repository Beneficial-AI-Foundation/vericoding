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
spec fn binomial_helper(n: int, k: int) -> int
    recommends n >= 0, k >= 0, k <= n
    decreases n, k
{
    if k > n || n < 0 || k < 0 {
        0
    } else if k == 0 || k == n {
        1
    } else {
        binomial_helper(n-1, k-1) + binomial_helper(n-1, k)
    }
}

/* helper modified by LLM (iteration 3): No changes needed as compilation error is in vc-code */
exec fn binomial_exec(n: i32, k: i32) -> (result: i8)
    requires k >= 0 && n >= 0 && k <= n
    ensures result as int == binomial(n as int, k as int)
    decreases n, k
{
    if k > n {
        0
    } else if k == 0 || k == n {
        1i8
    } else {
        binomial_exec(n-1, k-1) + binomial_exec(n-1, k)
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
{
    /* code modified by LLM (iteration 5): Changed forall binders from nat to int and cast i to int in obstacle_grid@[i] for type consistency */
    let m = obstacle_grid.len() as usize;
    let n = obstacle_grid[0].len() as usize;
    if obstacle_grid[0 as usize][0 as usize] == 1 {
        return 0i8;
    }
    if m == 1 && n == 1 {
        if obstacle_grid[0 as usize][0 as usize] == 0 { return 1i8; } else { return 0i8; }
    } else if m == 1 {
        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                forall|jj: int| 0 <= jj < j as int ==> obstacle_grid@[0][jj] == 0i8
        {
            if obstacle_grid[0 as usize][j] == 1i8 { return 0i8; }
            j += 1;
        }
        return 1i8;
    } else if n == 1 {
        let mut i = 0;
        while i < m
            invariant
                0 <= i <= m,
                forall|ii: int| 0 <= ii < i as int ==> obstacle_grid@[ii][0] == 0i8
        {
            if obstacle_grid[i][0 as usize] == 1i8 { return 0i8; }
            i += 1;
        }
        return 1i8;
    } else {
        let mut i = 0;
        while i < m
            invariant
                0 <= i <= m,
                forall|ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < n as int ==> obstacle_grid@[ii][jj] == 0i8
        {
            let mut j = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    0 <= i < m,
                    forall|ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < n as int ==> obstacle_grid@[ii][jj] == 0i8,
                    forall|jj: int| 0 <= jj < j as int ==> obstacle_grid@[i as int][jj] == 0i8
            {
                if obstacle_grid[i][j] == 1i8 { return 0i8; }
                j += 1;
            }
            i += 1;
        }
        let nn = m as i32 + n as i32 - 2;
        let kk = m as i32 - 1;
        let result_each = binomial_exec(nn, kk);
        return result_each;
    }
}
// </vc-code>


}

fn main() {}