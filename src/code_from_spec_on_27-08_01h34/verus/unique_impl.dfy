use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value(seq: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == val
}

spec fn is_strictly_sorted(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] < seq[j]
}

spec fn all_elements_from_original(result: Seq<i32>, original: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> contains_value(original, result[i])
}

spec fn unique_elements_invariant(a: Seq<i32>, result: Seq<i32>, i: int) -> bool {
    forall|j: int, k: int| 0 <= j < i && 0 <= k < result.len() && a[j] == result[k] ==>
        forall|l: int| j < l < i ==> a[l] != a[j]
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            is_strictly_sorted(result@),
            all_elements_from_original(result@, a@),
            forall|k: int| 
                #![trigger result@[k]]
                0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < i && a[j] == result@[k],
            unique_elements_invariant(a@, result@, i as int)
        decreases a.len() - i
    {
        let current = a[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found == exists|k: int| 0 <= k < j && result@[k] == current,
                is_strictly_sorted(result@),
                all_elements_from_original(result@, a@)
            decreases result.len() - j
        {
            if result[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            result.push(current);
            proof {
                assert(unique_elements_invariant(a@, result@, (i + 1) as int));
            }
        } else {
            proof {
                assert(unique_elements_invariant(a@, result@, (i + 1) as int));
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}