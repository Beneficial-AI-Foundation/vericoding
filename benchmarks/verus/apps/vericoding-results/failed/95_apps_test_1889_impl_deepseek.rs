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
/* helper modified by LLM (iteration 5): Add view functions for mutable vector handling */
view fn grid_at(grid: &Vec<Vec<i8>>, i: int) -> Seq<int>
    requires
        0 <= i < grid.len(),
{
    grid[i].view()@.map(|j: int, x: i8| x as int)
}

view fn row_at(row: &Vec<i8>) -> Seq<int>
{
    row@.map(|j: int, x: i8| x as int)
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
/* code modified by LLM (iteration 5): Use view functions instead of direct indexing */
{
    let mut result = Vec::with_capacity(q as usize);
    let mut current_grid = grid;
    let mut current_scores: Vec<i8> = Vec::with_capacity(n as usize);
    let mut current_max: i8 = 0;
    
    // Initialize scores
    for i in 0..n {
        let row = &current_grid[i as usize];
        let view_row = row_at(row);
        let mut consecutive = 0;
        let mut max_consecutive = 0;
        for j in 0..m {
            if view_row[j as int] == 1 {
                consecutive += 1;
            } else {
                consecutive = 0;
            }
            if consecutive > max_consecutive {
                max_consecutive = consecutive;
            }
        }
        current_scores.push(max_consecutive);
        if max_consecutive > current_max {
            current_max = max_consecutive;
        }
    }
    
    for k in 0..q {
        let (r, c) = queries[k as usize];
        let row_index = (r - 1) as usize;
        let col_index = (c - 1) as usize;
        
        let old_val = current_grid[row_index][col_index];
        let new_val = 1 - old_val;
        current_grid[row_index][col_index] = new_val;
        
        let old_row_score = current_scores[row_index];
        let row = &current_grid[row_index];
        let view_row = row_at(row);
        let mut consecutive = 0;
        let mut max_consecutive = 0;
        for j in 0..m {
            if view_row[j as int] == 1 {
                consecutive += 1;
            } else {
                consecutive = 0;
            }
            if consecutive > max_consecutive {
                max_consecutive = consecutive;
            }
        }
        current_scores[row_index] = max_consecutive;
        
        if max_consecutive > current_max {
            current_max = max_consecutive;
        } else if old_row_score == current_max && max_consecutive < old_row_score {
            current_max = 0;
            for score in &current_scores {
                if *score > current_max {
                    current_max = *score;
                }
            }
        }
        
        result.push(current_max);
    }
    
    result
}
// </vc-code>


}

fn main() {}