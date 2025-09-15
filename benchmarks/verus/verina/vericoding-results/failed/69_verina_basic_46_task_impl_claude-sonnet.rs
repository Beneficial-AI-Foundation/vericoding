// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix parameter type mismatch */
proof fn lemma_invariant_preservation(arr: &Vec<i32>, elem: i32, i: usize, k: usize)
    requires 
        i > 0,
        i <= arr.len(),
        forall|j: int| (i as int) < j < arr.len() ==> arr[j] != elem,
        arr[(i - 1) as int] != elem,
        k == i - 1
    ensures arr[k as int] != elem
{
    assert(k as int == (i as int) - 1);
    assert(arr[k as int] != elem);
}
// </vc-helpers>

// <vc-spec>
fn last_position(arr: &Vec<i32>, elem: i32) -> (result: i32)
    requires forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> 
            0 <= result < arr.len() &&
            arr[result as int] == elem &&
            forall|k: int| result < k < arr.len() ==> arr[k] != elem) &&
        (result == -1 ==> forall|k: int| 0 <= k < arr.len() ==> arr[k] != elem),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type mismatch in lemma call */
    let mut i: usize = arr.len();
    while i > 0
        invariant
            i <= arr.len(),
            forall|k: int| (i as int) <= k < arr.len() ==> arr[k] != elem
        decreases i
    {
        i = i - 1;
        if arr[i] == elem {
            proof {
                assert(0 <= i < arr.len());
                assert(arr[i as int] == elem);
                assert(forall|k: int| (i as int) < k < arr.len() ==> arr[k] != elem);
            }
            return i as i32;
        }
        proof {
            lemma_invariant_preservation(arr, elem, i + 1, i);
        }
    }
    proof {
        assert(i == 0);
        assert(forall|k: int| 0 <= k < arr.len() ==> arr[k] != elem);
    }
    -1
}
// </vc-code>

}
fn main() {}