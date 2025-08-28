use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    // impl-start
    let mut i = 0;
    while i < sub.len()
        // invariants-start
        invariant
            0 <= idx <= (main.len() - sub.len()),
            0 <= i <= sub.len(),
            0 <= idx + i <= main.len(),
            forall|k: int| 0 <= k < i ==> main[idx + k] == sub[k],
            forall|k: int|
                0 <= k < i ==> (main@.subrange(idx as int, (idx + k)) =~= sub@.subrange(0, k)),
        // invariants-end
        decreases sub.len() - i
    {
        if (main[idx + i] != sub[i]) {
            // assert-start
            assert(exists|k: int| 0 <= k < i ==> main[idx + k] != sub[k]);
            assert(main@.subrange(idx as int, (idx + sub@.len())) != sub@);
            // assert-end
            return false;
        }
        i += 1;
    }
    // assert-start
    assert(main@.subrange(idx as int, (idx + sub@.len())) == sub@);
    // assert-end
    true
    // impl-end
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut idx = 0;
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= (main.len() - sub.len()) + 1,
            forall|k: int| 0 <= k < idx ==> main@.subrange(k, k + sub@.len() as int) != sub@,
        decreases (main.len() - sub.len()) + 1 - idx
    {
        if is_sub_list_at_index(main, sub, idx) {
            return true;
        }
        idx += 1;
    }
    false
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}