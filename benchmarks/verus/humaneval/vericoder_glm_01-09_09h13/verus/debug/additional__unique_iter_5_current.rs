use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper code needed for this implementation
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
    let mut result: Vec<i32> = Vec::new();
    if a.len() == 0 {
        return result;
    }
    result.push(a[0]);

    let mut j: usize = 1;
    while j < a.len()
        invariant
            1 <= j as int <= a.len() as int,
            0 < result.len() as int,
            result.len() as int <= j as int,
            forall|j1: int, j2: int| 0 <= j1 < j2 < result.len() as int ==> result@[j1] < result@[j2],
            result@[(result.len()-1) as int] <= a@[j as int],
        decreases (a.len() as int - j as int),
    {
        if a[j] > result[result.len()-1] {
            result.push(a[j]);
        }
        j += 1;
    }
    result
}
// </vc-code>

fn main() {}
}