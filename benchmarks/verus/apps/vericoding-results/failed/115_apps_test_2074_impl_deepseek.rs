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
fn seq_min_helper(s: &Vec<i8>) -> (min_val: i8)
    requires s@.len() > 0
    ensures min_val as int == seq_min(s@.map(|j: int, x: i8| x as int)),
{
    if s@.len() == 1 {
        s[0]
    } else {
        let tail_min = seq_min_helper(&s[1..].to_vec());
        if s[0] <= tail_min {
            s[0]
        } else {
            tail_min
        }
    }
}

proof fn seq_min_helper_ensures(s: Seq<int>)
    requires s.len() > 0
    ensures seq_min(s) == {
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
    decreases s.len()
{
    if s.len() > 1 {
        seq_min_helper_ensures(s.drop_first());
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
{
    /* code modified by LLM (iteration 2): Fix type conversion and implement proper max-min computation */
    let row_count = grid.len();
    let mut max_min = i8::MIN;
    let mut i: usize = 0;
    
    while i < row_count
        invariant
            0 <= i <= row_count,
            exists|max_val: int| max_val == (if i > 0 { 
                seq_max(Seq::new(i, |k: int| seq_min(grid@[k]@.map(|j: int, x: i8| x as int)))) 
            } else { i8::MIN as int }),
            forall|k: int| 0 <= k < i ==> grid_spec[k] == grid@[k]@.map(|j: int, x: i8| x as int),
            max_min as int == (if i > 0 { 
                seq_max(Seq::new(i, |k: int| seq_min(grid@[k]@.map(|j: int, x: i8| x as int)))) 
            } else { i8::MIN as int }),
    {
        let row = &grid[i];
        let row_min = seq_min_helper(row);
        
        if i == 0 || row_min > max_min {
            max_min = row_min;
        }
        
        i += 1;
    }
    
    max_min
}
// </vc-code>


}

fn main() {}