use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = vec![];
    if a.len() == 0 {
        return result;
    }
    result.push(a[0]);
    proof {
        loop_invariant
            result@.len() >= 1,
            forall |x: usize, y: usize| x < y && y < result@.len() ==> result@[x] < result@[y] #![trigger result@[x], result@[y]]
    }
    for i in 1..a.len() {
        loop_invariant
            result@.len() >= 1,
            forall |x: usize, y: usize| x < y && y < result@.len() ==> result@[x] < result@[y] #![trigger result@[x], result@[y]]
        let last = *result.last().unwrap();
        if last < a[i] {
            result.push(a[i]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}