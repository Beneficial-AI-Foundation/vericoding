// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subrange_at(main: Seq<i32>, sub: Seq<i32>, i: int) -> (result: bool) {
    sub =~= main.subrange(i, i+sub.len())
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed precondition to handle empty sub */
spec fn matches_at(main: Seq<i32>, sub: Seq<i32>, start: int) -> bool {
    start >= 0 && start + sub.len() <= main.len() &&
    forall|j: int| 0 <= j < sub.len() ==> main[start + j] == sub[j]
}

fn check_match_at(main: &Vec<i32>, sub: &Vec<i32>, start: usize) -> (result: bool)
    requires
        start + sub.len() <= main.len(),
    ensures
        result == matches_at(main@, sub@, start as int),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            i <= sub.len(),
            start + sub.len() <= main.len(),
            forall|j: int| 0 <= j < i ==> main@[start as int + j] == sub@[j],
        decreases sub.len() - i
    {
        if main[start + i] != sub[i] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    ensures
        result == (exists|k: int|
            0 <= k <= (main.len() - sub.len()) && is_subrange_at(main@, sub@, k)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): handle empty sub array case */
    if sub.len() == 0 {
        proof {
            assert(is_subrange_at(main@, sub@, 0));
        }
        return true;
    }
    if sub.len() > main.len() {
        proof {
            assert(forall|k: int| 0 <= k <= (main.len() - sub.len()) ==> !is_subrange_at(main@, sub@, k));
        }
        return false;
    }
    
    let mut i = 0;
    while i <= main.len() - sub.len()
        invariant
            i <= main.len() - sub.len() + 1,
            sub.len() <= main.len(),
            forall|k: int| 0 <= k < i ==> !is_subrange_at(main@, sub@, k),
        decreases main.len() - sub.len() + 1 - i
    {
        if check_match_at(main, sub, i) {
            proof {
                assert(matches_at(main@, sub@, i as int));
                assert(is_subrange_at(main@, sub@, i as int));
            }
            return true;
        }
        proof {
            assert(!matches_at(main@, sub@, i as int));
            assert(!is_subrange_at(main@, sub@, i as int));
        }
        i += 1;
    }
    proof {
        assert(forall|k: int| 0 <= k <= (main.len() - sub.len()) ==> !is_subrange_at(main@, sub@, k));
    }
    false
}
// </vc-code>

}
fn main() {}