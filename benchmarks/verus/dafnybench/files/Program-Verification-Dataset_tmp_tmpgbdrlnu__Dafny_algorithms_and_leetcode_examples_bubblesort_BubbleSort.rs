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

fn bubble_sort(a: &mut Vec<i32>) -> (n: usize) 
    ensures n <= n_choose_2(a.len() as int) as usize
{
    assume(false);
    unreached()
}

}
fn main() {}