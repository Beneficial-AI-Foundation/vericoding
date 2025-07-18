use vstd::prelude::*;

verus! {

//IMPL sub_array_at_index
fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // pre-conditions-start
    requires
        /* code modified by LLM (iteration 2): Fixed compilation error by moving requires clause inside function signature */
        idx <= main.len() && sub.len() <= main.len() && idx <= main.len() - sub.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len()) as int) =~= sub@),
    // post-conditions-end
{
    /* code modified by LLM (iteration 2): Implemented function logic to check if sub array matches at given index */
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            idx + i <= main.len(),
            forall|j: int| 0 <= j < i ==> main@[idx as int + j] == sub@[j],
    {
        if main[idx + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    true
}

spec fn is_subrange_at(main: Seq<i32>, sub: Seq<i32>, i: int) -> (result: bool) {
    sub =~= main.subrange(i, i+sub.len())
}

//IMPL is_sub_array
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // post-conditions-start
    ensures
        result == (exists|k: int|
            0 <= k <= (main.len() - sub.len()) && is_subrange_at(main@, sub@, k)),
    // post-conditions-end
{
    /* code modified by LLM (iteration 2): Implemented function logic to check if sub is a subarray of main */
    if sub.len() > main.len() {
        return false;
    }
    
    let mut idx = 0;
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < idx ==> !is_subrange_at(main@, sub@, k),
    {
        if sub_array_at_index(main, sub, idx) {
            return true;
        }
        idx += 1;
    }
    false
}

} // verus!

fn main() { }