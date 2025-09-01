use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helper code or proofs needed for this verification.
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
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            result@.len() == i - (if (pos as int) < i { 1int } else { 0int }),
            forall |k: int| 0 <= k < result@.len() ==> #[trigger] result@[k] == a@[k + (if k >= (pos as int) { 1int } else { 0int })],
    {
        if i != pos {
            result.push(a[i]);
        }
        i += 1;
    }
    proof {
        assert(result@.len() == a@.len() - 1);
        assert(forall |k: int| 0 <= k < result@.len() ==> result@[k] == a@[k + (if k >= (pos as int) { 1int } else { 0int })]);
    }
    result
}
// </vc-code>

fn main() {}
}