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
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result@.len() == a@.len() + b@.len(),
        forall|i: int| #![trigger] 0 <= i < a@.len() ==> result@[i] == a@[i],
        forall|i: int| #![trigger] 0 <= i < b@.len() ==> result@[i + a@.len()] == b@[i],
{
    let mut result = Vec::<i32>::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k] == a@[k],
            i <= a.len(),
        decreases
            a.len() as int - i as int,
    {
        result.push(a@[i as int]);
        i += 1;
    }
    let mut j = 0;
    while j < b.len()
        invariant
            result@.len() == a@.len() + j as int,
            forall|k: int| 0 <= k < a@.len() ==> result@[k] == a@[k],
            forall|k: int| 0 <= k < j as int ==> result@[(a@.len() + k)] == b@[k],
            j <= b.len(),
        decreases
            b.len() as int - j as int,
    {
        result.push(b@[j as int]);
        j += 1;
    }
    assert(forall|i: int| #![trigger] 0 <= i < b@.len() ==> result@[(i + a@.len())] == b@[i]);
    result
}
// </vc-code>

fn main() {}
}