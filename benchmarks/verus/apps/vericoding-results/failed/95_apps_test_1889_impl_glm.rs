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
/* helper modified by LLM (iteration 3): changed to use slices instead of Vec references */
fn cons_helper_impl(l: &[i8], index: usize, current: i8, max_so_far: i8) -> (result: i8)
    decreases l.len() - index
{
    if index >= l.len() {
        max_so_far
    } else if l[index] == 1 {
        let new_current = current + 1;
        let new_max = if new_current > max_so_far { new_current } else { max_so_far };
        cons_helper_impl(l, index + 1, new_current, new_max)
    } else {
        cons_helper_impl(l, index + 1, 0, max_so_far)
    }
}

/* helper modified by LLM (iteration 3): changed to use slices instead of Vec references */
fn cons_impl(l: &[i8]) -> (result: i8)
    decreases l.len()
{
    cons_helper_impl(l, 0, 0, 0)
}

/* helper modified by LLM (iteration 4): fixed slice indexing using split_at */
fn max_in_seq_impl(s: &[i8]) -> (result: i8)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let (_, rest_slice) = s.split_at(1);
        let rest = max_in_seq_impl(rest_slice);
        if s[0] > rest { s[0] } else { rest }
    }
}

/* helper modified by LLM (iteration 5): fixed slice indexing by removing redundant range */
fn compute_score_impl(grid: &Vec<Vec<i8>>) -> (result: i8)
    decreases grid.len()
{
    if grid.len() == 0 {
        0
    } else {
        let mut row_scores: Vec<i8> = Vec::with_capacity(grid.len());
        for i in 0..grid.len() {
            row_scores.push(cons_impl(&grid[i]));
        }
        max_in_seq_impl(&row_scores[..])
    }
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
    /* code modified by LLM (iteration 3): updated helper functions to use slices */
    let mut results: Vec<i8> = Vec::with_capacity(q as usize);
    
    for k in 0..q {
        let (r, c) = queries[k as usize];
        let r_index = (r - 1) as usize;
        let c_index = (c - 1) as usize;
        
        let mut new_grid = grid.clone();
        new_grid[r_index][c_index] = 1 - new_grid[r_index][c_index];
        
        let score = compute_score_impl(&new_grid);
        
        results.push(score);
    }
    
    results
}
// </vc-code>


}

fn main() {}