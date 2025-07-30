use vstd::prelude::*;

verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    // pre-conditions-start
    requires
        0 <= idx <= (main.len() - sub.len()),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

spec fn is_subrange_at(main: Seq<i32>, sub: Seq<i32>, i: int) -> (result: bool) {
    sub =~= main.subrange(i, i+sub.len())
}
// pure-end

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|k: int|
            0 <= k <= (main.len() - sub.len()) && is_subrange_at(main@, sub@, k)),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() { }
