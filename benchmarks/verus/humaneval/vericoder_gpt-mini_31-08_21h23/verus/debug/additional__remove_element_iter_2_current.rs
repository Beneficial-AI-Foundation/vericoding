use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        0 <= pos < a.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len();
        invariant result.len() == (if i <= pos { i } else { i - 1 });
        invariant forall |k: int|
            0 <= k && k < (result.len() as int) ==>
                if k < (pos as int) {
                    result[k as usize] == a[k as usize]
                } else {
                    result[k as usize] == a[(k as usize) + 1]
                };
        decreases a.len() - i;
    {
        if i == pos {
            // skip the element at position pos
        } else {
            result.push(a[i]);
            if i < pos {
                assert(result.len() == i + 1);
                assert(result[i] == a[i]);
            } else {
                assert(result.len() == i);
                assert(result[i - 1] == a[i]);
            }
        }
        i = i + 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}