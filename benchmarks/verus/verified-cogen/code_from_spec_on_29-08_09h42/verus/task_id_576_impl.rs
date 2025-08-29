use vstd::prelude::*;

verus! {

// <vc-helpers>
fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    /* code modified by LLM (iteration 2): added decreases clause for loop termination */
    while i < sub.len()
        invariant
            0 <= idx <= (main.len() - sub.len()),
            0 <= i <= sub.len(),
            0 <= idx + i <= main.len(),
            forall|k: int| 0 <= k < i ==> main[idx + k] == sub[k],
        decreases sub.len() - i,
    {
        if main[idx + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    true
}

proof fn lemma_subrange_equality(main: &Vec<i32>, sub: &Vec<i32>, idx: usize, k: int)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
        0 <= k <= (main.len() - sub.len()),
        main@.subrange(k, k + sub@.len()) =~= sub@,
    ensures
        exists|i: int, j: int| 0 <= i <= (main.len() - sub.len()) && j == i + sub.len() && main@.subrange(i, j) =~= sub@,
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    if sub.len() == 0 {
        return true;
    }
    
    let mut idx = 0;
    /* code modified by LLM (iteration 5): added trigger annotation to fix quantifier trigger inference error */
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= (main.len() - sub.len()) + 1,
            sub.len() <= main.len(),
            forall|k: int| 0 <= k < idx ==> #[trigger] main@.subrange(k, k + sub@.len()) != sub@,
        decreases (main.len() - sub.len()) + 1 - idx,
    {
        if sub_array_at_index(main, sub, idx) {
            proof {
                lemma_subrange_equality(main, sub, idx, idx as int);
            }
            return true;
        }
        idx += 1;
    }
    false
}
// </vc-code>

} // verus!

fn main() {}