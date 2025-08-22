use vstd::prelude::*;

verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    // pre-conditions-start
    requires
        0 <= idx <= (main.len() - sub.len()),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
    // post-conditions-end
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added bounds check invariant and fixed termination */
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            idx + sub.len() <= main.len(),
            forall|j: int| 0 <= j < i ==> main@[idx as int + j] == sub@[j],
        decreases sub.len() - i,
    {
        /* code modified by LLM (iteration 1): added bounds assertion */
        assert(idx + i < main.len());
        if main[idx + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): added proof that all elements match */
    assert(forall|j: int| 0 <= j < sub.len() ==> main@[idx as int + j] == sub@[j]);
    true
}

spec fn is_subrange_at(main: Seq<i32>, sub: Seq<i32>, i: int) -> (result: bool) {
    sub =~= main.subrange(i, i+sub.len())
}
// pure-end

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|k: int|
            0 <= k <= (main.len() - sub.len()) && is_subrange_at(main@, sub@, k)),
    // post-conditions-end
{
    /* code modified by LLM (iteration 2): handle empty sub array case with proper witness */
    if sub.len() == 0 {
        assert(is_subrange_at(main@, sub@, 0));
        assert(0 <= 0 <= main.len() - sub.len());
        return true;
    }
    
    if sub.len() > main.len() {
        return false;
    }
    
    let mut idx = 0;
    /* code modified by LLM (iteration 1): fixed bounds and added witness tracking */
    while idx <= main.len() - sub.len()
        invariant
            0 <= idx <= main.len() - sub.len() + 1,
            sub.len() <= main.len(),
            sub.len() > 0,
            forall|k: int| 0 <= k < idx ==> !is_subrange_at(main@, sub@, k),
        decreases main.len() - sub.len() + 1 - idx,
    {
        /* code modified by LLM (iteration 1): added bounds check before function call */
        assert(idx <= main.len() - sub.len());
        if sub_array_at_index(main, sub, idx) {
            /* code modified by LLM (iteration 1): prove witness exists */
            assert(is_subrange_at(main@, sub@, idx as int));
            return true;
        }
        idx += 1;
    }
    /* code modified by LLM (iteration 1): prove no valid subrange exists */
    assert(forall|k: int| 0 <= k <= main.len() - sub.len() ==> !is_subrange_at(main@, sub@, k));
    false
}

} // verus!

fn main() { }