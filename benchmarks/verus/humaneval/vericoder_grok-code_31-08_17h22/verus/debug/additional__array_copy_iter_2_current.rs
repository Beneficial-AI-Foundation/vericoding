use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in HELPERS for this implementation
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<i32>::new();
    proof {
        assert(result@.len() == 0);
    }
    let mut i = 0;
    while i < a@.len()
        invariant
            result@.len() == i,
            0 <= i <= a@.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j]
    {
        assert(a@[i] == a@[i]);
        result.push(a[i]);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}