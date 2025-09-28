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
/* helper modified by LLM (iteration 5): The helper has been modified to remove unnecessary `ghost` keywords from the parameters `i` and `j` because they are not necessary in a `proof` function of this type. */
proof fn lemma_update_cell_preserves_other_cells(grid: Seq<Seq<int>>, r: int, c: int, val: int, i: int, j: int)
    requires
        0 <= r < grid.len(),
        0 <= c < grid[r].len(),
        0 <= i < grid.len(),
        0 <= j < grid[i].len(),
        i != r || j != c,
    ensures
        (#[trigger] grid.update(r, grid[r].update(c, val)))[i][j] == grid[i][j],
{
    if i == r {
        // Within the updated row
        assert((#[trigger] grid.update(r, grid[r].update(c, val)))[i].len() == grid[r].len()); // Follows from update
        assert((#[trigger] grid.update(r, grid[r].update(c, val)))[i][j] == grid[r].update(c, val)[j]);
        assert(j != c);
        assert(grid[r].update(c, val)[j] == grid[r][j]);
    } else {
        // Not the updated row
        assert((#[trigger] grid.update(r, grid[r].update(c, val)))[i] == grid[i]);
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
/* code modified by LLM (iteration 5): Explicitly cast `x` to `int` in the `grid_mut@.map` expressions. */
{
    let mut grid_mut = grid;
    let mut results = Vec::new();

    let ghost N_int = n as int;
    let ghost M_int = m as int;
    let ghost Q_int = q as int;

    proof {
        assert(valid_grid(grid_mut@.map(|i, row| row@.map(|j, x: i8| x as int)), N_int, M_int));
    }

    let mut k: int = 0;
    while k < Q_int
        invariant
            0 <= k <= Q_int,
            results.len() == k,
            valid_grid(grid_mut@.map(|i, row| row@.map(|j, x: i8| x as int)), N_int, M_int),
    {
        let query_val = queries[k as usize];
        let ghost r_query_int = query_val.0 as int;
        let ghost c_query_int = query_val.1 as int;

        let r_idx = (query_val.0 - 1) as usize;
        let c_idx = (query_val.1 - 1) as usize;

        let current_val = grid_mut[r_idx][c_idx];
        let new_val = if current_val == 0 { 1 } else { 0 };

        let ghost old_grid_seq = grid_mut@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int));

        // Update the grid
        let mut updated_row = grid_mut[r_idx].clone();
        updated_row.set(c_idx, new_val);
        grid_mut.set(r_idx, updated_row);

        proof {
            let prev_grid_seq = old_grid_seq;
            let new_grid_seq = grid_mut@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int));

            assert(new_grid_seq.len() == N_int);
            assert(N_int > 0 ==> new_grid_seq[0].len() == M_int); // Ensure grid[0] exists before accessing
            assert(forall|i: int, j: int| 0 <= i < N_int && 0 <= j < M_int ==> new_grid_seq[i].len() == M_int);
            assert(forall|i: int, j: int| 0 <= i < N_int && 0 <= j < M_int ==> new_grid_seq[i][j] == 0 || new_grid_seq[i][j] == 1);
            assert(valid_grid(new_grid_seq, N_int, M_int));
        }

        let score_val = compute_score(grid_mut@.map(|i, row: Vec<i8>| row@.map(|j, x: i8| x as int)));
        results.push(score_val as i8);

        k = k + 1;
    }

    results
}
// </vc-code>


}

fn main() {}