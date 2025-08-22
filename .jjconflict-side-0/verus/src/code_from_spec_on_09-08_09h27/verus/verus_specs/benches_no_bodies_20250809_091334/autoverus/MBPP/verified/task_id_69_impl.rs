use vstd::prelude::*;

fn main() {
}

verus! {

fn is_sub_list_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            idx + i <= main.len(),
            forall|j: int| 0 <= j < i ==> main@[idx + j] == sub@[j],
        decreases sub.len() - i,
    {
        if main[idx + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    requires
        sub.len() <= main.len(),
    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
{
    let mut idx = 0;
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= main.len() - sub.len() + 1,
            /* code modified by LLM (iteration 1): removed trigger annotation to fix arithmetic/non-arithmetic position conflict */
            forall|k: int| 0 <= k < idx ==> main@.subrange(k, k + sub.len()) !== sub@,
        decreases main.len() - sub.len() + 1 - idx,
    {
        if is_sub_list_at_index(main, sub, idx) {
            return true;
        }
        idx += 1;
    }
    false
}

} // verus!