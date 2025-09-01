use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let mut res = a;
    res.push(b);
    res
}
// </vc-code>

fn main() {}
}