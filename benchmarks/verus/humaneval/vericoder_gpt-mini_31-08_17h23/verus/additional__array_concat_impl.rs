use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result: Vec<i32> = Vec::new();

    // copy a into result
    let mut i: nat = 0;
    while i < a.len()
        invariant i <= a.len();
        invariant result.len() == i;
        invariant forall |j: nat| j < i ==> result@[j] == a@[j];
    {
        result.push(a[i]);
        i = i + 1;
    }

    // copy b into result
    let mut k: nat = 0;
    while k < b.len()
        invariant k <= b.len();
        invariant result.len() == a.len() + k;
        invariant forall |j: nat| j < a.len() ==> result@[j] == a@[j];
        invariant forall |j: nat| j < k ==> result@[a.len() + j] == b@[j];
    {
        result.push(b[k]);
        k = k + 1;
    }

    result
    // impl-end
}
// </vc-code>

fn main() {}
}