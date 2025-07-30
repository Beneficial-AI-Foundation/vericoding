use vstd::prelude::*;

verus! {

fn is_sub_list_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    // pre-conditions-start
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    // pre-conditions-start
    requires
        sub.len() <= main.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}