// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)

    requires
        0 < lst.len() < u32::MAX,

    ensures
        sum == add_odd_evens(lst@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type error in take(i) */
    let mut i: usize = 1;
    let mut sum: u64 = 0;
    while i < lst.len()
        invariant 
            sum as int == add_odd_evens(lst@.take(i as int)),
        decreases 
            (lst.len() as int) - (i as int),
    {
        let value = lst[i];
        if value % 2 == 0 {
            sum = sum + value as u64;
        }
        i = i + 2;
    }
    sum
}
// </vc-code>

}
fn main() {}