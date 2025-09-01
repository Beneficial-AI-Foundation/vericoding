use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    // impl-start
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    let alen: int = a.len() as int;
    while i < alen
        invariant 0 <= i && i <= alen
        invariant res.len() as int == i
        invariant forall|j: int| 0 <= j && j < i ==> #[trigger] (res[j] == a[j])
    {
        res.push(a[i]);
        // after push, res[i] equals the pushed element a[i]
        assert(res[i] == a[i]);
        i += 1;
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}