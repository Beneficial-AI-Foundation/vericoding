use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_half_less_than_n(n: int)
    requires
        0 < n,
    ensures
        0 <= n / 2 && n / 2 < n,
{
    assert(0 <= n / 2);
    if n == 1 {
        assert
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
proof fn lemma_half_less_than_n(n: int)
    requires
        0 < n,
    ensures
        0 <= n / 2 && n / 2 < n,
{
    assert(0 <= n / 2);
    if n == 1 {
        assert
// </vc-code>

fn main() {}
}