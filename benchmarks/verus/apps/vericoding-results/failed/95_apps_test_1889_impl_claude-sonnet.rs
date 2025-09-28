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
/* helper modified by LLM (iteration 5): fixed grid score computation by using row@.map for proper conversion */
fn compute_cons(row: &Vec<i8>) -> (result: i8)
    requires row.len() <= 127
    ensures result as int == cons(row@.map(|j: int, x: i8| x as int))
{
    let mut max_consecutive = 0i8;
    let mut current_consecutive = 0i8;
    let mut i = 0;
    
    while i < row.len()
        invariant
            0 <= i <= row.len(),
            max_consecutive as int >= 0,
            current_consecutive as int >= 0,
            current_consecutive <= 127,
            max_consecutive as int == cons_helper(row@.map(|j: int, x: i8| x as int), 0, 0, 0),
        decreases row.len() - i
    {
        if row[i] == 1 {
            if current_consecutive < 127 {
                current_consecutive += 1;
            }
            if current_consecutive > max_consecutive {
                max_consecutive = current_consecutive;
            }
        } else {
            current_consecutive = 0;
        }
        i += 1;
    }
    
    max_consecutive
}

fn compute_grid_score(grid: &Vec<Vec<i8>>) -> (result: i8)
    requires 
        grid.len() > 0,
        valid_grid(grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)), grid.len() as int, grid[0].len() as int),
        grid.len() <= 127,
        grid[0].len() <= 127
    ensures result as int == compute_score(grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)))
{
    let mut max_score = 0i8;
    let mut i = 0;
    
    while i < grid.len()
        invariant
            0 <= i <= grid.len(),
            max_score as int >= 0,
            max_score as int == max_in_seq(Seq::new(i as nat, |k: int| cons(grid@[k]@.map(|j: int, x: i8| x as int)))),
        decreases grid.len() - i
    {
        let row_score = compute_cons(&grid[i]);
        if row_score > max_score {
            max_score = row_score;
        }
        i += 1;
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
    /* code modified by LLM (iteration 5): fixed grid score computation with proper conversion */
    let mut results = Vec::new();
    let mut k = 0;
    
    while k < queries.len()
        invariant
            0 <= k <= queries.len(),
            results.len() == k,
        decreases queries.len() - k
    {
        let (row, col) = queries[k];
        
        if row >= 1 && col >= 1 {
            let r = (row - 1) as usize;
            let c = (col - 1) as usize;
            
            let mut modified_grid = grid.clone();
            let old_value = modified_grid[r][c];
            let new_value = 1 - old_value;
            let mut new_row = modified_grid[r].clone();
            new_row.set(c, new_value);
            modified_grid.set(r, new_row);
            
            let score = compute_grid_score(&modified_grid);
            results.push(score);
        } else {
            results.push(0);
        }
        
        k += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}