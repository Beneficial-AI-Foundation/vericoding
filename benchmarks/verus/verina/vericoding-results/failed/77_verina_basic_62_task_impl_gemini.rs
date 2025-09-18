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
    /* code modified by LLM (iteration 3): use i32 for index to match return type and ensure safe casting */
    let mut i: i32 = 0;
    let len = a.len() as i32;
    while i < len
        invariant
            0 <= i <= len,
            forall|j: int| 0 <= j < i ==> a.view().index(j) != key,
            a.len() < i32::MAX as nat,
        decreases len - i
    {
        if a[i as usize] == key {
            return i;
        }
        i = i + 1;
    }
    -1
}
// </vc-code>

}
fn main() {}