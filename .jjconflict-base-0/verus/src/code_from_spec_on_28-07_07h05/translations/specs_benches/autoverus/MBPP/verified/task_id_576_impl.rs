use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix termination verification */
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            forall|j: int| 0 <= j < i ==> main@[idx as int + j] == sub@[j],
        decreases sub.len() - i,
    {
        if main[idx + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j < sub@.len() ==> main@[idx as int + j] == sub@[j]);
    assert(main@.subrange(idx as int, (idx + sub@.len())) =~= sub@);
    
    return true;
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
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
    /* code modified by LLM (iteration 4): added explicit trigger annotation to fix quantifier trigger inference error */
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < idx ==> #[trigger] main@.subrange(k, k + sub@.len()) != sub@,
        decreases main.len() - sub.len() + 1 - idx,
    {
        if sub_array_at_index(main, sub, idx) {
            assert(main@.subrange(idx as int, idx as int + sub@.len()) =~= sub@);
            return true;
        }
        idx += 1;
    }
    
    assert(forall|k: int| 0 <= k <= (main.len() - sub.len()) ==> 
           main@.subrange(k, k + sub@.len()) != sub@);
    
    return false;
}

} // verus!