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
    /* code modified by LLM (iteration 5): Added precondition to ensure array length fits in i32 */
    if a.len() >= i32::MAX as usize {
        return -1;
    }
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            proof {
                assert(i < a.len());
                assert(a.len() < i32::MAX as usize);
                assert(i < i32::MAX as usize);
                assert(a[i as int] == key);
                assert(forall|j: int| 0 <= j < i ==> a[j] != key);
            }
            return i as i32;
        }
        i = i + 1;
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