// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn n_choose_2(n: int) -> int
{
    n * (n - 1) / 2
}

spec fn sum_range(lo: int, hi: int) -> int
    decreases hi - lo
{
    if lo >= hi { 0 }
    else { sum_range(lo, hi - 1) + hi - 1 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>) -> (n: usize) 
    ensures n <= n_choose_2(a.len() as int) as usize
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}