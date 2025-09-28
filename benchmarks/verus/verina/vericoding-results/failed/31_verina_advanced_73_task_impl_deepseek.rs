// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn find_smallest_rec(l: Seq<nat>, start_index: int, current: nat) -> (result: nat)
    requires
        0 <= start_index <= l.len(),
        forall|i: int| 0 <= i < start_index ==> l[i] < current,
        forall|i: int| start_index <= i < l.len() ==> l[i] >= current
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate),
        result >= current
    decreases l.len() - start_index
{
    if start_index == l.len() {
        current
    } else {
        if l[start_index] == current {
            find_smallest_rec(l, start_index + 1, current + 1)
        } else {
            current
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_missing(l: Seq<nat>) -> (result: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed executable wrapper with proper nat conversion */
    proof {
        let result = find_smallest_rec(l, 0, 0);
        assert(result == find_smallest_rec(l, 0, 0));
    }
    find_smallest_rec(l, 0, 0) as nat
}
// </vc-code>

}
fn main() {}