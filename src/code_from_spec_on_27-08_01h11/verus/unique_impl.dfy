use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value(seq: Seq<i32>, value: i32) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == value
}

spec fn is_unique_sorted(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] < seq[j]
}

spec fn preserves_elements(original: Seq<i32>, result: Seq<i32>) -> bool {
    forall|value: i32| contains_value(original, value) <==> contains_value(result, value)
}
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
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result@[k] < result@[l],
            forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < i && a[j] == result@[k],
            forall|value: i32| (exists|j: int| 0 <= j < i && a[j] == value) <==> contains_value(result@, value),
    {
        if result.len() == 0 || result@[result.len() - 1] != a[i] {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}