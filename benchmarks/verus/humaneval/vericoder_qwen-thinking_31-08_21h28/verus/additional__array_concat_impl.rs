use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        decreases a.len() as int - i as int
        invariant
            (result.len() == i) &&
            (forall |j: int| #[verifier::trigger] 0 <= j < (i as int) ==> result[j] == a[j])
    {
        result.push(a[i]);
        i += 1;
    }
    let mut j: usize = 0;
    while j < b.len()
        decreases b.len() as int - j as int
        invariant
            (result.len() == a.len() + j) &&
            (forall |k: int| #[verifier::trigger] 0 <= k < (a.len() as int) ==> result[k] == a[k]) &&
            (forall |k: int| #[verifier::trigger] 0 <= k < (j as int) ==> result[(a.len() as int) + k] == b[k])
    {
        result.push(b[j]);
        j += 1;
    }
    result
}
// </vc-code>

fn main() {}
}