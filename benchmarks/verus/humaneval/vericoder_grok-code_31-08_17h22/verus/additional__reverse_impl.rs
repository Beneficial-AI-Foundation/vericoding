use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = a.len();

    while i > 0
        invariant
            result.len() == a.len() - i,
            forall|j: int| 0 <= j && j < result.len() ==> result[j] == a[a.len() - 1 - j],
        decreases i
    {
        i = i - 1;
        result.push(a[i]);
        proof {
            assert(result[result.len() - 1] == a[a.len() - 1 - (a.len() - 1 - i)]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}