// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed invariant bounds for start + i */
spec fn subarray_matches(main: &Vec<i32>, sub: &Vec<i32>, start: int) -> bool
{
    start + sub.len() <= main.len() &&
    main@.subrange(start, start + sub.len()) =~= sub@
}

fn check_subarray_at(main: &Vec<i32>, sub: &Vec<i32>, start: usize) -> (result: bool)
    requires
        start + sub.len() <= main.len(),
    ensures
        result == subarray_matches(main, sub, start as int),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            i <= sub.len(),
            start + sub.len() <= main.len(),
            start as int + i < main.len(),
            forall|j: int| 0 <= j < i ==> main@[start as int + j] == sub@[j],
        decreases sub.len() - i
    {
        if main[start + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(forall|j: int| 0 <= j < sub.len() ==> main@[start as int + j] == sub@[j]);
        assert(main@.subrange(start as int, start as int + sub.len()) =~= sub@);
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    requires
        sub.len() <= main.len(),

    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed bounds check for empty sub case */
{
    if sub.len() == 0 {
        proof {
            assert(main@.subrange(0, 0) =~= sub@);
            assert(exists|k: int, l: int| 0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && main@.subrange(k, l) =~= sub@);
        }
        return true;
    }
    
    if main.len() < sub.len() {
        proof {
            assert(forall|pos: int, l: int| 0 <= pos <= (main.len() - sub.len()) && l == pos + sub.len() ==> main@.subrange(pos, l) != sub@);
        }
        return false;
    }
    
    let mut k = 0;
    while k <= main.len() - sub.len()
        invariant
            k <= main.len() - sub.len() + 1,
            main.len() >= sub.len(),
            sub.len() > 0,
            forall|pos: int| 0 <= pos < k ==> !subarray_matches(main, sub, pos),
        decreases main.len() - sub.len() + 1 - k
    {
        if check_subarray_at(main, sub, k) {
            proof {
                assert(subarray_matches(main, sub, k as int));
                assert(main@.subrange(k as int, k as int + sub.len()) =~= sub@);
                assert(exists|pos: int, l: int| 0 <= pos <= (main.len() - sub.len()) && l == pos + sub.len() && main@.subrange(pos, l) =~= sub@);
            }
            return true;
        }
        k += 1;
    }
    proof {
        assert(forall|pos: int| 0 <= pos <= (main.len() - sub.len()) ==> !subarray_matches(main, sub, pos));
        assert(forall|pos: int, l: int| 0 <= pos <= (main.len() - sub.len()) && l == pos + sub.len() ==> main@.subrange(pos, l) != sub@);
    }
    false
}
// </vc-code>

}
fn main() {}