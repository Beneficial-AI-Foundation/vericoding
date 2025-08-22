use vstd::prelude::*;

verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
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
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            idx + i <= main.len(),
            forall|j: int| 0 <= j < i ==> main@[idx as int + j] == sub@[j],
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases sub.len() - i
    {
        if main[idx + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
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
    let mut idx = 0;
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= main.len() - sub.len() + 1,
            /* code modified by LLM (iteration 3): fixed trigger by using separate variable to avoid arithmetic/non-arithmetic position conflict */
            forall|k: int| 0 <= k < idx ==> {
                let end_pos = k + sub@.len();
                #[trigger] main@.subrange(k, end_pos) !== sub@
            },
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases main.len() - sub.len() + 1 - idx
    {
        if sub_array_at_index(main, sub, idx) {
            return true;
        }
        idx += 1;
    }
    false
}

} // verus!

fn main() {}