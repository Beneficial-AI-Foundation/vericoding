// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_grid(grid: Seq<Seq<int>>, n: int, m: int) -> bool {
    grid.len() == n && n > 0 && m > 0 &&
    (forall|i: int| 0 <= i < n ==> grid[i].len() == m) &&
    (forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> grid[i][j] == 0 || grid[i][j] == 1)
}

spec fn valid_queries(queries: Seq<(int, int)>, q: int, n: int, m: int) -> bool {
    queries.len() == q && q >= 0 &&
    (forall|k: int| 0 <= k < q ==> #[trigger] queries[k].0 >= 1 && queries[k].0 <= n && queries[k].1 >= 1 && queries[k].1 <= m)
}

spec fn cons_helper(l: Seq<int>, index: int, current: int, max_so_far: int) -> int
    decreases l.len() - index
{
    if index >= l.len() {
        max_so_far
    } else if l[index] == 1 {
        let new_current = current + 1;
        let new_max = if new_current > max_so_far { new_current } else { max_so_far };
        cons_helper(l, index + 1, new_current, new_max)
    } else {
        cons_helper(l, index + 1, 0, max_so_far)
    }
}

spec fn cons(l: Seq<int>) -> int {
    cons_helper(l, 0, 0, 0)
}

spec fn max_in_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let rest = max_in_seq(s.subrange(1, s.len() as int));
        if s[0] > rest { s[0] } else { rest }
    }
}

spec fn compute_score(grid: Seq<Seq<int>>) -> int {
    if grid.len() == 0 {
        0
    } else {
        let row_scores = Seq::new(grid.len(), |i: int| cons(grid[i]));
        max_in_seq(row_scores)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): compute max consecutive ones in a row */
fn cons_vec(row: &Vec<i8>) -> i8
{
    let n: usize = row.len();
    let mut idx: usize = 0;
    let mut current: i8 = 0;
    let mut max: i8 = 0;
    while idx < n
        invariant
            idx <= n,
            current >= 0,
            max >= 0,
        decreases n - idx
    {
        if row[idx] == 1 {
            current = current + 1;
            if current > max { max = current; }
        } else {
            current = 0;
        }
        idx += 1;
    }
    max
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, q: i8, grid: Vec<Vec<i8>>, queries: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires 
        valid_grid(grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)), n as int, m as int),
        valid_queries(queries@.map(|k: int, query: (i8, i8)| (query.0 as int, query.1 as int)), q as int, n as int, m as int),
    ensures 
        results.len() == q,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): avoid mutable indexing by rebuilding grid and recomputing max */
    let mut grid = grid;
    let mut results: Vec<i8> = Vec::new();
    let mut k: usize = 0;
    let qn: usize = queries.len();
    while k < qn
        invariant
            k <= qn,
            results.len() == k,
        decreases qn - k
    {
        let (r, c) = queries[k];
        let rui: usize = (r as usize) - 1;
        let cui: usize = (c as usize) - 1;

        // build new_grid by cloning rows, flipping the target cell
        let mut new_grid: Vec<Vec<i8>> = Vec::new();
        let mut row_i: usize = 0;
        let nrows: usize = grid.len();
        while row_i < nrows
            invariant
                row_i <= nrows,
                new_grid.len() == row_i,
            decreases nrows - row_i
        {
            if row_i == rui {
                // build modified row
                let mut new_row: Vec<i8> = Vec::new();
                let mut col_j: usize = 0;
                let ncols: usize = grid[row_i].len();
                while col_j < ncols
                    invariant
                        col_j <= ncols,
                        new_row.len() == col_j,
                    decreases ncols - col_j
                {
                    let val = grid[row_i][col_j];
                    if col_j == cui {
                        if val == 0 { new_row.push(1); } else { new_row.push(0); }
                    } else {
                        new_row.push(val);
                    }
                    col_j += 1;
                }
                new_grid.push(new_row);
            } else {
                new_grid.push(grid[row_i].clone());
            }
            row_i += 1;
        }

        // recompute overall max
        let mut j: usize = 0;
        let mut overall: i8 = 0;
        while j < nrows
            invariant
                j <= nrows,
                overall >= 0,
            decreases nrows - j
        {
            let row_best: i8 = cons_vec(&new_grid[j]);
            if row_best > overall { overall = row_best; }
            j += 1;
        }

        grid = new_grid;
        results.push(overall);
        k += 1;
    }

    results
}
// </vc-code>


}

fn main() {}