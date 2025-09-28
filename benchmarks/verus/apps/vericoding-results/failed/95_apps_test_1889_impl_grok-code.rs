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
/* helper modified by LLM (iteration 5): fixed compilation error by using |ret| binding for ensures clauses */
exec fn cons_helper_exec(l: &[i8], index: usize, current: i8, max_so_far: i8) -> i8
    requires 
        index <= l.len(),
        current >= 0,
        max_so_far >= 0,
        (forall|i: usize| 0 <= i < l.len() ==> l[i] == 0 || l[i] == 1),
    ensures 
        |ret| (ret as int) == cons_helper(l@.map(|i: int| l@[i] as int), index as int, current as int, max_so_far as int),
    decreases l.len() - index
{
    if index >= l.len() {
        return max_so_far;
    }
    let cell = l[index];
    if cell == 1 {
        let new_current = current + 1;
        let new_max = if new_current > max_so_far { new_current } else { max_so_far };
        cons_helper_exec(l, index + 1, new_current, new_max)
    } else {
        cons_helper_exec(l, index + 1, 0, max_so_far)
    }
}

exec fn cons_exec(row: &[i8]) -> i8
    requires 
        (forall|i: usize| 0 <= i < row.len() ==> row[i] == 0 || row[i] == 1),
    ensures 
        |ret| (ret as int) == cons(row@.map(|i: int, x: i8| x as int)),
{
    cons_helper_exec(row, 0, 0, 0)
}

exec fn max_in_seq_exec(s: &[i8]) -> i8
    requires 
        s.len() <= i32::MAX as usize,
        (forall|i: usize| 0 <= i < s.len() ==> s[i] >= 0),
    ensures 
        |ret| (ret as int) == max_in_seq(s@.map(|i: int, x: i8| x as int)),
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let rest = max_in_seq_exec(&s[1..]);
        if s[0] > rest { s[0] } else { rest }
    }
}

exec fn compute_score_exec(grid: &Vec<Vec<i8>>) -> i8
    requires 
        grid.len() > 0,
        (forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid@[i].len() ==> grid@[i][j] == 0 || grid@[i][j] == 1),
    ensures 
        |ret| (ret as int) == compute_score(grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int))),
{
    let mut row_scores = Vec::new();
    let n = grid.len();
    for i in 0..n {
        let row_score = cons_exec(&grid[i]);
        row_scores.push(row_score);
    }
    proof {
        assert(row_scores@ == Seq::new(n as int, |ii: int| cons(grid@[ii])));
    }
    max_in_seq_exec(&row_scores)
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
/* code modified by LLM (iteration 5): implementation remains the same as previous iteration for completing the score computation after bit flips */
{
    let mut grid = grid;
    let mut results = Vec::new();
    for query in queries {
        let r = (query.0 - 1) as usize;
        let c = (query.1 - 1) as usize;
        grid[r][c] = 1 - grid[r][c];
        let score = compute_score_exec(&grid);
        results.push(score);
    }
    results
}
// </vc-code>


}

fn main() {}