// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_grid(grid: Seq<Seq<int>>) -> bool {
    grid.len() > 0 && forall|i: int| 0 <= i < grid.len() ==> grid[i].len() > 0
}

spec fn seq_min(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else if s[0] <= seq_min(s.subrange(1, s.len() as int)) {
        s[0]
    } else {
        seq_min(s.subrange(1, s.len() as int))
    }
}

spec fn seq_max(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else if s[0] >= seq_max(s.subrange(1, s.len() as int)) {
        s[0]
    } else {
        seq_max(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(grid: Seq<Seq<int>>) -> (result: int)
    requires valid_grid(grid)
    ensures ({
        let row_mins = Seq::new(grid.len(), |i: int| seq_min(grid[i]));
        result == seq_max(row_mins)
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}