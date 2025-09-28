// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn linear_search_index_prop(a: Seq<i32>, p: spec_fn(i32) -> bool, i: int) -> (r: bool)
    requires 0 <= i < a.len()
    ensures r == p(a[i])
{
    p(a[i])
}
// </vc-helpers>

// <vc-spec>
fn linear_search3(a: &Vec<i32>, p: spec_fn(i32) -> bool) -> (result: usize)
    requires 
        exists|i: int| 0 <= i < a.len() && p(a[i]),
    ensures 
        result < a.len(),
        p(a[result as int]),
        forall|k: int| 0 <= k < result ==> !p(a[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replace view call with ghost view variable */
    let ghost_a = a.view();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> !p(ghost_a[k]),
        decreases a.len() - i
    {
        proof {
            let ghost_i = i as int;
            assert(linear_search_index_prop(ghost_a, p, ghost_i) == p(ghost_a[ghost_i]));
        };
        if p(a[i]) {
            return i;
        }
        i = i + 1;
    }
    proof {
        assert(forall|k: int| 0 <= k < a.len() ==> !p(ghost_a[k])) by {
            assert(forall|k: int| 0 <= k < a.len() ==> !p(ghost_a[k]));
        };
    };
    assert(false) by {
        assert(exists|i: int| 0 <= i < a.len() && p(ghost_a[i]));
    };
    unreached()
}
// </vc-code>

}
fn main() {}