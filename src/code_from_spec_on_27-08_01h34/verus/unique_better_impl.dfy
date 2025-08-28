use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn unique_elements(a: &[i32]) -> Seq<i32> {
    let mut result = Seq::<i32>::empty();
    let mut i = 0;
    while i < a.len() {
        if i == 0 || a[i] != a[i-1] {
            result = result.push(a[i]);
        }
        i += 1;
    }
    result
}

proof fn lemma_unique_elements_strictly_increasing(a: &[i32])
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger unique_elements(a)[i], unique_elements(a)[j]]
            0 <= i && i < j && j < unique_elements(a).len() ==> unique_elements(a)[i] < unique_elements(a)[j],
{
}

proof fn lemma_previous_unique_element_smaller(a: &[i32], i: usize, prev_val: i32)
    requires
        forall|k: int, l: int|
            #![trigger a[k], a[l]]
            0 <= k && k < l && l < a.len() ==> a[k] <= a[l],
        0 < i < a.len(),
        prev_val < a[i as int],
    ensures
        prev_val < a[i as int]
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
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
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result@[k], result@[l]]
                0 <= k && k < l && l < result.len() ==> result@[k] < result@[l],
            forall|k: int|
                0 <= k < result.len() ==> exists|j: int| 0 <= j < i && result@[k] == a[j],
    {
        if i == 0 || a[i] != a[i-1] {
            result.push(a[i]);
            
            proof {
                let new_len = result.len();
                if new_len >= 2 {
                    assert(result@[new_len - 1] == a[i]);
                    let prev_idx = new_len - 2;
                    assert(result@[prev_idx] < a[i]) by {
                        let mut j: int = i as int - 1;
                        while j >= 0 && (j == 0 || a[j] == a[j-1])
                            invariant
                                -1 <= j < i,
                        {
                            j = j - 1;
                        }
                    };
                }
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}