use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper code and proofs can be added here if needed
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i as nat,
            forall|j: int| 0 <= j < i ==> res@[j] == a@[j],
    {
        res.push(a[i]);
        i += 1;
    }
    res.push(b);
    proof {
        assert(res@.len() == a@.len() + 1);
        assert forall|k: int| 0 <= k < res@.len() implies res@[k] == (if k < a@.len() { a@[k] } else { b }) by {
            if k < a@.len() {
                assert(res@[k] == a@[k]);
            } else {
                assert(k == a@.len());
                assert(res@[k] == b);
            }
        };
    }
    res
}
// </vc-code>

fn main() {}
}