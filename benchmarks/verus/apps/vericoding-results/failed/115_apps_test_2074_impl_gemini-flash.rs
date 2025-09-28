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
/* helper modified by LLM (iteration 5): No changes to helpers - previous implementation is correct */
spec fn seq_min_i8(s: Seq<i8>) -> i8
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail_min = seq_min_i8(s.drop_first());
        if s[0] <= tail_min {
            s[0]
        } else {
            tail_min
        }
    }
}

spec fn seq_max_i8(s: Seq<i8>) -> i8
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail_max = seq_max_i8(s.drop_first());
        if s[0] >= tail_max {
            s[0]
        } else {
            tail_max
        }
    }
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
/* code modified by LLM (iteration 5): Fixed unclosed delimiter in proof block by adding a closing parenthesis */
{
    if grid.len() == 0 {
        unreachable!();
    }

    let mut max_of_mins: i8 = i8::MIN;
    let mut i: usize = 0;

    while i < grid.len()
        invariant
            0 <= i && i <= grid.len(),
            max_of_mins == seq_max_i8(Seq::new(i as nat, |j: nat| seq_min_i8(grid@[j as int]@))),
            forall|k: int| 0 <= k < grid.len() && ({ i >= 1 && (k as usize) < i }) ==> grid[k as usize].len() > 0 && max_of_mins >= seq_min_i8(grid@[k as int]@),
    {
        let row = &grid[i];
        proof {
            assert(valid_grid(grid@.map(|idx: int, r: Vec<i8>| r@.map(|jdx: int, x: i8| x as int)))); // Added closing parenthesis
            assert(grid.len() > 0);
            assert(i < grid.len());
        }

        if row.len() == 0 {
            unreachable!();
        }

        let mut min_in_row: i8 = i8::MAX;
        let mut j: usize = 0;

        while j < row.len()
            invariant
                0 <= j && j <= row.len(),
                min_in_row == seq_min_i8(row@.subsequence(0, j as int)),
                forall|k: int| 0 <= k < grid.len() ==> grid[k as usize].len() > 0,
        {
            min_in_row = if row[j] < min_in_row {
                row[j]
            } else {
                min_in_row
            };
            j = j + 1;
        }

        if min_in_row > max_of_mins {
            max_of_mins = min_in_row;
        }
        i = i + 1;
    }
    max_of_mins
}
// </vc-code>


}

fn main() {}