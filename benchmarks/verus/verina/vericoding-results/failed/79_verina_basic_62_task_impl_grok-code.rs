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
    /* code modified by LLM (iteration 5): fixed type mismatches by changing loop index and len to nat for runtime Seq indexing, adjusted invariant to use nat */
    let len: nat = a.view().len();
    let mut i: nat = 0;
    while i < len
        invariant
            0 <= i <= len,
            forall|j: nat| 0 <= j < i ==> a.view()[j] != key,
        decreases len - i
    {
        if a.view()[i] == key {
            return i as i32;
        }
        i = i + 1;
    }
    return -1;
}
// </vc-code>

}
fn main() {}