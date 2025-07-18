use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 3): fixed requires/ensures placement inside function signature */
fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
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
    /* code modified by LLM (iteration 3): implemented function logic */
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            forall|j: int| 0 <= j < i ==> main@[idx + j] == sub@[j],
    {
        if main[idx + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    return true;
}

/* code modified by LLM (iteration 3): fixed requires/ensures placement inside function signature */
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
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
    /* code modified by LLM (iteration 3): implemented function logic */
    let mut idx = 0;
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < idx ==> main@.subrange(k, k + sub@.len()) !=~= sub@,
    {
        if sub_array_at_index(main, sub, idx) {
            return true;
        }
        idx += 1;
    }
    return false;
}

} // verus!

fn main() {}