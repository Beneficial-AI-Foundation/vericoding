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
    /* code modified by LLM (iteration 5): removed invalid casts and assertions, proper bounds checking */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            assert(i < a.len());
            assert(i < 0x8000_0000);
            return i as i32;
        }
        i = i + 1;
    }
    -1
}
// </vc-code>

}
fn main() {}