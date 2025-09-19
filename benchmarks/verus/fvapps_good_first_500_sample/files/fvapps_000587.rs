// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_adjacent_cells(rows: nat, cols: nat, r: nat, c: nat) -> nat {
    let mut count: nat = 0;
    if r > 0 { count = count + 1; }
    if r + 1 < rows { count = count + 1; }
    if c > 0 { count = count + 1; }
    if c + 1 < cols { count = count + 1; }
    count
}

spec fn is_cell_stable(grid: Seq<Seq<nat>>, rows: nat, cols: nat, r: nat, c: nat) -> bool {
    r < rows && c < cols ==>
    count_adjacent_cells(rows, cols, r, c) > grid[r as int][c as int]
}

spec fn is_grid_stable(grid: Seq<Seq<nat>>, rows: nat, cols: nat) -> bool {
    forall|r: nat, c: nat| r < rows && c < cols ==> is_cell_stable(grid, rows, cols, r, c)
}

fn modify_list(xs: Vec<nat>, i: usize, v: nat) -> (result: Vec<nat>)
    requires i < xs.len(),
    ensures
        result.len() == xs.len(),
        result[i as int] == v,
        forall|j: int| 0 <= j < xs.len() && j != i ==> result[j] == xs[j]
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}

fn check_grid_stability(grid: Vec<Vec<nat>>, rows: usize, cols: usize) -> (result: String)
    requires 
        grid.len() == rows,
        rows >= 3 && cols >= 3,
        forall|i: int| 0 <= i < grid.len() ==> grid[i].len() == cols,
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> grid[i][j] <= 4,
    ensures
        equal(result@, "Stable".view()) || equal(result@, "Unstable".view())
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>

proof fn corner_cells_stability(n: nat)
    requires n >= 2,
    ensures
        ({
            let grid1 = Seq::<Seq<nat>>::new(n as nat, |_i: int| Seq::<nat>::new(n as nat, |_j: int| 0));
            let grid2 = grid1.update(0int, grid1[0int].update(0int, 2));
            let grid3 = grid1.update(0int, grid1[0int].update(0int, 1));
            !is_grid_stable(grid2, n, n) && is_grid_stable(grid3, n, n)
        })
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn center_cells_stability(n: nat)
    requires n >= 3,
    ensures
        ({
            let grid1 = Seq::<Seq<nat>>::new(n as nat, |_i: int| Seq::<nat>::new(n as nat, |_j: int| 0));
            let center = (n / 2) as int;
            let grid2 = grid1.update(center, grid1[center].update(center, 4));
            let grid3 = grid1.update(center, grid1[center].update(center, 3));
            !is_grid_stable(grid2, n, n) && is_grid_stable(grid3, n, n)
        })
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn arbitrary_grid_stability(grid: Seq<Seq<nat>>)
    requires
        grid.len() > 0,
        grid[0int].len() > 0,
        forall|i: int| 0 <= i < grid.len() ==> grid[i].len() == grid[0int].len(),
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> grid[i][j] <= 4,
    ensures
        ({
            let rows = grid.len() as nat;
            let cols = grid[0int].len() as nat;
            is_grid_stable(grid, rows, cols) || !is_grid_stable(grid, rows, cols)
        })
{
    assume(false); // TODO: Remove this line and implement the proof
}

}

fn main() {
    // let test1 = vec![vec![1, 2, 1], vec![2, 3, 2], vec![1, 2, 1]];
    // println!("{}", check_grid_stability(test1, 3, 3));
    
    // let test2 = vec![vec![0, 0, 0, 0], vec![0, 0, 0, 0], vec![0, 0, 4, 0]];
    // println!("{}", check_grid_stability(test2, 3, 4));
    
    // let test3 = vec![vec![1, 1, 1], vec![1, 4, 1], vec![1, 1, 1]];
    // println!("{}", check_grid_stability(test3, 3, 3));
}