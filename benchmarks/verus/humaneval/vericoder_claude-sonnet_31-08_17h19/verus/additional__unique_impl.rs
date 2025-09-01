use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sorted_implies_unique_strictly_increasing(a: &[i32], result: &Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
        forall|i: int|
            #![trigger result@[i]]
            0 <= i && i < result.len() ==> exists|j: int| 0 <= j && j < a.len() && result@[i] == a[j],
        forall|i: int, j: int|
            #![trigger result@[i], result@[j]]
            0 <= i && i < j && j < result.len() ==> result@[i] != result@[j],
    ensures
        forall|i: int, j: int|
            #![trigger result@[i], result@[j]]
            0 <= i && i < j && j < result.len() ==> result@[i] < result@[j],
{
    assert forall|i: int, j: int| 0 <= i && i < j && j < result.len() implies result@[i] < result@[j] by {
        let k1 = choose|k1: int| 0 <= k1 && k1 < a.len() && result@[i] == a[k1];
        let k2 = choose|k2: int| 0 <= k2 && k2 < a.len() && result@[j] == a[k2];
        
        assert(result@[i] != result@[j]);
        assert(result@[i] == a[k1]);
        assert(result@[j] == a[k2]);
        
        if k1 == k2 {
            assert(result@[i] == a[k1] && result@[j] == a[k2] && k1 == k2);
            assert(result@[i] == result@[j]);
        } else if k1 < k2 {
            assert(a[k1] <= a[k2]);
            assert(result@[i] <= result@[j]);
            assert(result@[i] < result@[j]);
        } else {
            assert(k1 > k2);
            assert(a[k2] <= a[k1]);
            assert(result@[j] <= result@[i]);
            assert(result@[j] < result@[i]);
        }
    };
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
            0 <= i && i <= a.len(),
            forall|k: int, l: int|
                #![trigger result@[k], result@[l]]
                0 <= k && k < l && l < result.len() ==> result@[k] < result@[l],
            forall|k: int|
                #![trigger result@[k]]
                0 <= k && k < result.len() ==> exists|j: int| 0 <= j && j < i && result@[k] == a[j],
            forall|k: int, l: int|
                #![trigger result@[k], result@[l]]
                0 <= k && k < l && l < result.len() ==> result@[k] != result@[l],
            forall|k: int|
                #![trigger result@[k]]
                0 <= k && k < result.len() ==> exists|j: int| 0 <= j && j < a.len() && result@[k] == a[j],
        decreases a.len() - i
    {
        if result.len() == 0 || result[result.len() - 1] != a[i] {
            result.push(a[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}