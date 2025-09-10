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

fn add(lst: Vec<u32>) -> (sum: u64)

    requires
        0 < lst.len() < u32::MAX,

    ensures
        sum == add_odd_evens(lst@),
{
    assume(false);
    unreached()
}

}
fn main() {}