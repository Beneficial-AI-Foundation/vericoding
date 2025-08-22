/*This is a slightly simpler version of proof provided by Chris Hawblitzel*/
use vstd::prelude::*;

fn main() {
}

verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
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
    true
}

spec fn is_subrange_at(main: Seq<i32>, sub: Seq<i32>, i: int) -> bool {
    sub =~= main.subrange(i, i + sub.len())
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|k: int|
            0 <= k <= (main.len() - sub.len()) && is_subrange_at(main@, sub@, k)),
{
    if sub.len() > main.len() {
        return false;
    }
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i <= main.len() - sub.len()
        invariant
            0 <= i <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < i ==> !is_subrange_at(main@, sub@, k),
        decreases main.len() - sub.len() + 1 - i,
    {
        if sub_array_at_index(main, sub, i) {
            assert(is_subrange_at(main@, sub@, i as int));
            return true;
        }
        i += 1;
    }
    false
}

} // verus!