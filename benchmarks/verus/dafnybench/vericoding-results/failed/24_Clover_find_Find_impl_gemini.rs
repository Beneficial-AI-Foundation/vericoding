// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find(a: &[i32], key: i32) -> (index: i32)
    ensures
        -1 <= index < a.len() as i32,
        index != -1 ==> a[index as int] == key && (forall|i: int| 0 <= i < index ==> a[i] != key),
        index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != key),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type error in invariant and removed a redundant check */
    let mut i: i32 = 0;
    while (i as usize) < a.len()
        invariant
            0 <= i,
            (i as usize) <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] != key,
        decreases (a.len() as i32) - i
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