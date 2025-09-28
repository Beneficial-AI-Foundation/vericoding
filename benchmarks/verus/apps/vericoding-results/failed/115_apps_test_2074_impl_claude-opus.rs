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
proof fn seq_min_in_range(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> seq_min(s) <= s[i]
    decreases s.len()
{
    if s.len() == 1 {
        assert(seq_min(s) == s[0]);
    } else {
        seq_min_in_range(s.drop_first());
        assert(seq_min(s) == if s[0] <= seq_min(s.drop_first()) { s[0] } else { seq_min(s.drop_first()) });
    }
}

proof fn seq_max_exists(s: Seq<int>)
    requires s.len() > 0
    ensures exists|i: int| 0 <= i < s.len() && s[i] == seq_max(s)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == seq_max(s));
    } else {
        seq_max_exists(s.drop_first());
        let tail_max = seq_max(s.drop_first());
        if s[0] >= tail_max {
            assert(s[0] == seq_max(s));
        }
    }
}

fn compute_min(v: &Vec<i8>) -> (result: i8)
    requires v.len() > 0
    ensures result as int == seq_min(v@.map(|j: int, x: i8| x as int))
{
    let mut min = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            min as int == seq_min(v@.map(|j: int, x: i8| x as int).take(i as int))
        decreases v.len() - i
    {
        proof {
            let s = v@.map(|j: int, x: i8| x as int);
            let s_prev = s.take(i as int);
            let s_curr = s.take((i + 1) as int);
            assert(s_curr == s_prev.push(s[i as int]));
            assert(seq_min(s_curr) == if s[i as int] < seq_min(s_prev) { s[i as int] } else { seq_min(s_prev) });
        }
        if v[i] < min {
            min = v[i];
        }
        i = i + 1;
    }
    proof {
        assert(v@.map(|j: int, x: i8| x as int).take(v.len() as int) == v@.map(|j: int, x: i8| x as int));
    }
    min
}

fn compute_max(v: &Vec<i8>) -> (result: i8)
    requires v.len() > 0
    ensures result as int == seq_max(v@.map(|j: int, x: i8| x as int))
{
    let mut max = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            max as int == seq_max(v@.map(|j: int, x: i8| x as int).take(i as int))
        decreases v.len() - i
    {
        proof {
            let s = v@.map(|j: int, x: i8| x as int);
            let s_prev = s.take(i as int);
            let s_curr = s.take((i + 1) as int);
            assert(s_curr == s_prev.push(s[i as int]));
            assert(seq_max(s_curr) == if s[i as int] > seq_max(s_prev) { s[i as int] } else { seq_max(s_prev) });
        }
        if v[i] > max {
            max = v[i];
        }
        i = i + 1;
    }
    proof {
        assert(v@.map(|j: int, x: i8| x as int).take(v.len() as int) == v@.map(|j: int, x: i8| x as int));
    }
    max
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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut row_mins = Vec::new();
    let mut i = 0;
    while i < grid.len()
        invariant
            0 <= i <= grid.len(),
            row_mins.len() == i,
            forall|j: int| 0 <= j < i ==> row_mins@[j] as int == seq_min(grid@[j]@.map(|k: int, x: i8| x as int))
        decreases grid.len() - i
    {
        let min = compute_min(&grid[i]);
        row_mins.push(min);
        i = i + 1;
    }
    proof {
        assert(row_mins@.map(|j: int, x: i8| x as int) == Seq::new(grid@.len(), |j: int| seq_min(grid@[j]@.map(|k: int, x: i8| x as int))));
    }
    compute_max(&row_mins)
}
// </vc-code>


}

fn main() {}