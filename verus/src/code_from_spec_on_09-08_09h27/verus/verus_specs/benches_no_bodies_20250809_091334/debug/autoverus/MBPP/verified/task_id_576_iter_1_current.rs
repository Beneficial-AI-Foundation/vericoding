use vstd::prelude::*;

fn main() {
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
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            idx + i <= main.len(),
            forall|j: int| 0 <= j < i ==> main@[idx + j] == sub@[j],
    {
        if main[idx + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    true
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
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= main.len() - sub.len() + 1,
            forall|k: int, l: int| 0 <= k < idx && l == k + sub.len() ==> main@.subrange(k, l) !=~= sub@,
    {
        if sub_array_at_index(main, sub, idx) {
            return true;
        }
        idx += 1;
    }
    false
}

} // verus!