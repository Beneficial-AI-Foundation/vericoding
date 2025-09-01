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
    let mut i: u32 = 0;
    while (i as int) < a@.len()
        invariant
            result@.len() == i as int,
            0 <= i as int <= a@.len(),
            forall|j: int| 0 <= j < i as int ==> result@[j] == a@[j]
    {
        result.push(a[(i as int)]);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}