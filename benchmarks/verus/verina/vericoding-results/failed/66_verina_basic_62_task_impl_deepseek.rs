// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type mismatch by using proper cast to i32 */
proof fn find_helper(a: Seq<i32>, key: i32, idx: i32) -> (result: i32)
    requires
        0 <= idx <= a.len() as i32,
    ensures
        result == -1 || (result >= 0 && result < a.len() as i32),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result as int ==> a[i] != key),
        result == -1 ==> forall|i: int| idx as int <= i < a.len() ==> a[i] != key,
    decreases (a.len() as i32) - idx
{
    if idx >= a.len() as i32 {
        -1i32
    } else {
        if a[idx as int] == key {
            idx
        } else {
            find_helper(a, key, idx + 1)
        }
    }
}
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
    /* code modified by LLM (iteration 5): Use proper type casting */
    let spec_result = find_helper(a.view(), key, 0i32);
    if spec_result == -1i32 {
        -1i32
    } else {
        spec_result
    }
}
// </vc-code>

}
fn main() {}