use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// pure-end

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    // pre-conditions-start
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
    // post-conditions-end
{
    assume(false);  // TODO: Replace with appropriate return value of type i128
}

} // verus!

fn main() {}