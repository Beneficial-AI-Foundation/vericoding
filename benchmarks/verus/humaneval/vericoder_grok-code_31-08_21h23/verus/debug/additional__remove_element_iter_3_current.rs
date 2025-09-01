use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// empty
// </vc-helpers>
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
    let mut result: Vec<i32> = Vec::new();

    let mut i: usize = 0;

    while i < a.len()
        // Add decreases clause to ensure termination
        decreases (a.len() as int - i as int)
        invariant
            0 <= i as int <= a.len() as int,
            result.len() == (if i as int <= pos as int { i as int } else { (i as int) - 1 }),
            forall|k: int| 0 <= k < result.len() && k <= a.len() as int - 1 ==>
                if k < pos as int {
                    result[k] == a[k]
                } else {
                    result[k] == a[k + 1]
                }
    {
        if i != pos {
            result.push(a[i]);
        }
        i += 1;
    }

    result
}
// </vc-code>

fn main() {}
}