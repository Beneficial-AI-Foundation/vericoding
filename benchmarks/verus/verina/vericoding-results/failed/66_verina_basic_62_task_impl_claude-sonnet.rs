// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed postcondition proof and cast assertions */
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            proof {
                assert(0 <= i < a.len());
                assert(i < usize::MAX);
                assert(i <= i32::MAX as usize);
                assert(forall|j: int| 0 <= j < i ==> a[j] != key);
                assert(a[i as int] == key);
            }
            return i as i32;
        }
        i += 1;
    }
    proof {
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> a[j] != key);
    }
    -1
}
// </vc-code>

}
fn main() {}