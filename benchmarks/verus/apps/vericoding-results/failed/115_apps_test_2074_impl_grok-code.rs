// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_grid(grid: Seq<Seq<int>>) -> bool {
    grid.len() > 0 && forall|i: int| #![auto] 0 <= i < grid.len() ==> grid[i].len() > 0
}

spec fn seq_min(s: Seq<int>) -> int 
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { 
        s[0]
    } else {
        let tail_min = seq_min(s.drop_first());
        if s[0] <= tail_min { 
            s[0]
        } else { 
            tail_min
        }
    }
}

spec fn seq_max(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { 
        s[0]
    } else {
        let tail_max = seq_max(s.drop_first());
        if s[0] >= tail_max { 
            s[0]
        } else { 
            tail_max
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added helper functions for min and row_min */
pub fn min(a: i8, b: i8) -> i8 {
    if a < b {
        a
    } else {
        b
    }
}

fn row_min(row: &[i8]) -> (result: i8)
    requires row.len() > 0
    ensures result as int == seq_min(row@.map(|_: int, x: i8| x as int))
{
    let mut i = 1;
    let mut min_val = row[0];
    while i < row.len()
        invariant
            i > 0,
            i <= row.len(),
            min_val as int == seq_min(row@.take(i).map(|_: int, x: i8| x as int))
        decreases row.len() - i
    {
        min_val = min(min_val, row[i]);
        i = i + 1;
    }
    min_val
}
// </vc-helpers>

// <vc-spec>
fn solve(grid: Vec<Vec<i8>>) -> (result: i8)
    requires valid_grid(grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)))
    ensures ({
        let grid_spec = grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int));
        let row_mins = Seq::new(grid_spec.len(), |i: int| seq_min(grid_spec[i]));
        result as int == seq_max(row_mins)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Implemented loop to compute the maximum of row minimums */
    let first_row_min = row_min(&grid[0]);
    let mut current_max = first_row_min;
    let mut i = 1;
    let grid_len = grid.len();
    while i < grid_len
        invariant
            i > 0,
            i <= grid.len(),
            current_max as int == seq_max(Seq::new(i, |j: int| seq_min(grid@[j].map(|_: int, x: i8| x as int)))),
            valid_grid(grid@.map(|_: int, row: Vec<i8>| row@.map(|_: int, x: i8| x as int)))
        decreases grid_len - i
    {
        let row_min_val = row_min(&grid[i]);
        current_max = if current_max < row_min_val { row_min_val } else { current_max };
        i = i + 1;
    }
    current_max
}
// </vc-code>


}

fn main() {}