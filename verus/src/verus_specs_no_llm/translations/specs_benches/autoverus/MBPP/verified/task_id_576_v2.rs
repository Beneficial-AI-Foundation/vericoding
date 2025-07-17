/*This is a slightly simpler version of proof provided by Chris Hawblitzel*/
use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    return false;  // TODO: Remove this line and implement the function body
}

spec fn is_subrange_at(main: Seq<i32>, sub: Seq<i32>, i: int) -> bool {
    sub =~= main.subrange(i, i + sub.len())
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|k: int|
            0 <= k <= (main.len() - sub.len()) && is_subrange_at(main@, sub@, k)),
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!
