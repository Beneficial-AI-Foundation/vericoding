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
fn compute_score_exec(grid: &Vec<Vec<i8>>) -> (score: i8)
    requires
        grid.len() > 0,
        forall|i: int| 0 <= i < grid.len() ==> grid[i].len() > 0,
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> (grid[i][j] == 0 || grid[i][j] == 1),
    ensures
        score as int == compute_score(grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int))),
{
    let mut max_score: i8 = 0;
    let mut i: usize = 0;
    while i < grid.len()
        invariant
            0 <= i <= grid.len(),
            max_score as int == max_in_seq(Seq::new(i as int, |k: int| cons(grid@[k]@.map(|j: int, x: i8| x as int)))),
            forall|k: int| 0 <= k < grid.len() ==> grid[k].len() > 0,
            forall|k: int, j: int| 0 <= k < grid.len() && 0 <= j < grid[k].len() ==> (grid[k][j] == 0 || grid[k][j] == 1),
    {
        let mut current_cons: i8 = 0;
        let mut max_cons: i8 = 0;
        let mut j: usize = 0;
        while j < grid[i].len()
            invariant
                0 <= i < grid.len(),
                0 <= j <= grid[i].len(),
                current_cons >= 0,
                max_cons >= 0,
                max_cons as int == cons_helper(grid@[i as int]@.map(|k: int, x: i8| x as int), j as int, current_cons as int, 0),
                forall|k: int| 0 <= k < grid.len() ==> grid[k].len() > 0,
                forall|k: int, l: int| 0 <= k < grid.len() && 0 <= l < grid[k].len() ==> (grid[k][l] == 0 || grid[k][l] == 1),
        {
            if grid[i][j] == 1 {
                current_cons = current_cons + 1;
                if current_cons > max_cons {
                    max_cons = current_cons;
                }
            } else {
                current_cons = 0;
            }
            j = j + 1;
        }
        if max_cons > max_score {
            max_score = max_cons;
        }
        i = i + 1;
    }
    max_score
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
    let mut results: Vec<i8> = Vec::new();
    let mut current_grid: Vec<Vec<i8>> = Vec::new();
    
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n,
            current_grid.len() == i,
            forall|k: int| 0 <= k < i ==> current_grid[k].len() == m,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < m ==> (current_grid[k][j] == grid[k][j]),
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m as usize
            invariant
                0 <= i < n,
                0 <= j <= m,
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row[k] == grid[i as int][k],
        {
            row.push(grid[i][j]);
            j = j + 1;
        }
        current_grid.push(row);
        i = i + 1;
    }
    
    let mut query_idx: usize = 0;
    while query_idx < q as usize
        invariant
            0 <= query_idx <= q,
            results.len() == query_idx,
            current_grid.len() == n,
            forall|k: int| 0 <= k < n ==> current_grid[k].len() == m,
            forall|k: int, j: int| 0 <= k < n && 0 <= j < m ==> (current_grid[k][j] == 0 || current_grid[k][j] == 1),
    {
        let (r, c) = queries[query_idx];
        let row_idx = (r - 1) as usize;
        let col_idx = (c - 1) as usize;
        
        if current_grid[row_idx][col_idx] == 0 {
            current_grid[row_idx].set(col_idx, 1);
        } else {
            current_grid[row_idx].set(col_idx, 0);
        }
        
        let score = compute_score_exec(&current_grid);
        results.push(score);
        query_idx = query_idx + 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}