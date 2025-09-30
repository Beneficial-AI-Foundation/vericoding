// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): trivial helper kept for potential lemmas */
proof fn trivial_helper() {
}

// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): linear search maintaining no-occurrence before i and existence after i */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k && k < i as int ==> a[k] != e,
            exists|j: int| i as int <= j && j < a.len() as int && a[j] == e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    proof {
        assert(i == a.len());
        assert(exists|j: int| i as int <= j && j < a.len() as int && a[j] == e);
        assert(false);
    }
    0
}
// </vc-code>

}
fn main() {}