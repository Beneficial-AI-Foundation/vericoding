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
    let mut result = Vec::<i32>::new();
    if a.len() == 0 {
        return result;
    }
    result.push(a[0]);
    proof {
        assert(result@.len() >= 1);
        assert(forall|x: int, y: int| #![trigger result@[x], result@[y]] 0 <= x < y < result@.len() ==> result@[x] < result@[y]);
    }
    for i in 1..a.len()
        invariant 1 <= result@.len(),
        forall|x: int, y: int| #![trigger result@[x], result@[y]] 0 <= x < y < result@.len() ==> result@[x] < result@[y]
    {
        if let Some(last) = result.last() {
            if *last < a[i] {
                result.push(a[i]);
                proof {
                    assert(forall|x: int| #![trigger a@[x], a@[i]] x < i ==> a@[x] <= a@[i]);
                }
            }
        }
    }
    result
}
// </vc-code>

fn main() {}
}