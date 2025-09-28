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
/* helper modified by LLM (iteration 5): prove dp_path_count non-negativity */
proof fn dp_nonneg(grid: Seq<Seq<int>>)
    recommends valid_grid(grid)
    ensures dp_path_count(grid) >= 0,
{
    let m = grid.len();
    let n = grid[0].len();
    if grid[0][0] == 1 || grid[m-1][n-1] == 1 {
        assert(dp_path_count(grid) == 0);
    } else if m == 1 && n == 1 {
        assert(dp_path_count(grid) == 1);
    } else if m == 1 {
        if forall|j: int| #![trigger grid[0][j]] 0 <= j < n ==> grid[0][j] == 0 {
            assert(dp_path_count(grid) == 1);
        } else {
            assert(dp_path_count(grid) == 0);
        }
    } else if n == 1 {
        if forall|i: int| #![trigger grid[i][0]] 0 <= i < m ==> grid[i][0] == 0 {
            assert(dp_path_count(grid) == 1);
        } else {
            assert(dp_path_count(grid) == 0);
        }
    } else if forall|i: int, j: int| #![trigger grid[i][j]] 0 <= i < m && 0 <= j < n ==> grid[i][j] == 0 {
        assert(binomial(m + n - 2, m - 1) >= 0);
        assert(dp_path_count(grid) == binomial(m + n - 2, m - 1));
    } else {
        assert(dp_path_count(grid) == 0);
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
    /* code modified by LLM (iteration 5): imperative DP to compute path counts using correct mutable indexing */
    // Convert runtime grid to spec-level sequence
    let grid_spec = obstacle_grid@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int));

    // We can rely on the specification function for the value; prove non-negativity
    proof {
        dp_nonneg(grid_spec);
    }

    // Compute the result by running a standard imperative DP over ints
    let m: nat = obstacle_grid.len();
    let n: nat = obstacle_grid[0].len();

    // Quick checks for trivial cases
    if obstacle_grid@[0][0] == 1 || obstacle_grid@[m-1][n-1] == 1 {
        0i8
    } else if m == 1 && n == 1 {
        if obstacle_grid@[0][0] == 0 { 1i8 } else { 0i8 }
    } else {
        let mut counts: Vec<Vec<int>> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row: Vec<int> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                row.push(0);
                j = j + 1;
            }
            counts.push(row);
            i = i + 1;
        }

        // initialize (0,0)
        if obstacle_grid@[0][0] == 0 { counts.mut()[0].mut()[0] = 1; } else { counts.mut()[0].mut()[0] = 0; }

        // first row
        let mut j2: usize = 1;
        while j2 < n
            invariant
                1 <= n,
            decreases n - j2
        {
            if obstacle_grid@[0][j2] == 0 {
                counts.mut()[0].mut()[j2] = counts@[0]@[j2 - 1];
            } else {
                counts.mut()[0].mut()[j2] = 0;
            }
            j2 = j2 + 1;
        }

        // first column
        let mut i2: usize = 1;
        while i2 < m
            invariant
                1 <= m,
            decreases m - i2
        {
            if obstacle_grid@[i2][0] == 0 {
                counts.mut()[i2].mut()[0] = counts@[i2 - 1]@[0];
            } else {
                counts.mut()[i2].mut()[0] = 0;
            }
            i2 = i2 + 1;
        }

        // rest
        let mut ii: usize = 1;
        while ii < m
            invariant
                1 <= m,
            decreases m - ii
        {
            let mut jj: usize = 1;
            while jj < n
                invariant
                    1 <= n,
                decreases n - jj
            {
                if obstacle_grid@[ii][jj] == 0 {
                    counts.mut()[ii].mut()[jj] = counts@[ii - 1]@[jj] + counts@[ii]@[jj - 1];
                } else {
                    counts.mut()[ii].mut()[jj] = 0;
                }
                jj = jj + 1;
            }
            ii = ii + 1;
        }

        // result
        let final_count: int = counts@[m - 1]@[n - 1];
        proof { assert(final_count >= 0); }
        final_count as i8
    }
}

// </vc-code>


}

fn main() {}