// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
fn find_odd_index(v: &Vec<u64>, start: usize) -> (result: usize)
    requires
        start <= v.len(),
        exists |q: int| start <= q < v.len() && v[q] % 2 == 1,
    ensures
        result >= start,
        result < v.len(),
        v[result as int] % 2 == 1
    decreases (v.len() as int) - (start as int)
{
    if v[start] % 2 == 1 {
        start
    } else {
        find_odd_index(v, start + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)

    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,

    ensures
        odd_index < v.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): using recursive helper function to find the index of an odd element */
    find_odd_index(v, 0)
}
// </vc-code>

}
fn main() {}