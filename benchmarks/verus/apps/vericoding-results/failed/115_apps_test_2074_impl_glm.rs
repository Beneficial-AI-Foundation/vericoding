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
/* helper modified by LLM (iteration 2): fixed invariant block syntax and added decreases clause */
fn vec_min(v: &Vec<i8>) -> (result: i8)
    requires v@.len() > 0
    ensures result as int == seq_min(v@.map(|i: int, x: i8| x as int))
{
    let mut min_val = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            min_val as int == seq_min(v@.subrange(0, i as int).map(|j: int, x: i8| x as int)),
        decreases v.len() - i
    {
        if v[i] < min_val {
            min_val = v[i];
        }
        i += 1;
    }
    min_val
}

/* helper modified by LLM (iteration 2): fixed invariant block syntax and added decreases clause */
fn vec_max(v: &Vec<i8>) -> (result: i8)
    requires v@.len() > 0
    ensures result as int == seq_max(v@.map(|i: int, x: i8| x as int))
{
    let mut max_val = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            max_val as int == seq_max(v@.subrange(0, i as int).map(|j: int, x: i8| x as int)),
        decreases v.len() - i
    {
        if v[i] > max_val {
            max_val = v[i];
        }
        i += 1;
    }
    max_val
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
    /* code modified by LLM (iteration 2): used fixed helper functions */
    let mut row_mins: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < grid.len()
        invariant 0 <= i <= grid.len()
        invariant row_mins@.len() == i
        invariant forall|j: int| 0 <= j < i ==> row_mins@[j] as int == seq_min(grid@[j]@.map(|k: int, x: i8| x as int))
    {
        let min_val = vec_min(&grid[i]);
        row_mins.push(min_val);
        i += 1;
    }
    let result = vec_max(&row_mins);
    result
}
// </vc-code>


}

fn main() {}