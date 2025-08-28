use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value(seq: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == val
}

spec fn all_from_original(original: Seq<i32>, result: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> contains_value(original, result[i])
}

spec fn all_original_represented(original: Seq<i32>, result: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < original.len() ==> contains_value(result, original[i])
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result@[k], result@[l]]
                0 <= k < l < result.len() ==> result@[k] < result@[l],
            all_from_original(a@, result@),
            forall|j: int| 0 <= j < i ==> contains_value(result@, a@[j]),
        decreases a.len() - i
    {
        if result.len() == 0 || result[result.len() - 1] != a[i] {
            result.push(a[i]);
            
            proof {
                if result.len() > 1 {
                    let last_idx = (result.len() - 1) as int;
                    let prev_idx = (result.len() - 2) as int;
                    
                    assert(result@[last_idx] == a@[i as int]);
                    assert(result@[prev_idx] == result@[prev_idx]);
                    
                    if i > 0 {
                        let mut k = 0;
                        while k < i
                            invariant
                                0 <= k <= i,
                                forall|m: int| 0 <= m < k ==> a@[m] <= a@[i as int],
                            decreases i - k
                        {
                            assert(a@[k as int] <= a@[i as int]);
                            k += 1;
                        }
                        
                        if result@[prev_idx] == a@[i as int] {
                            assert(false);
                        } else {
                            assert(contains_value(a@, result@[prev_idx]));
                            
                            let mut found_idx = 0;
                            while found_idx < i && a[found_idx] != result@[prev_idx]
                                invariant 0 <= found_idx <= i
                                decreases i - found_idx
                            {
                                found_idx += 1;
                            }
                            
                            if found_idx < i {
                                assert(a@[found_idx as int] == result@[prev_idx]);
                                assert(found_idx < i);
                                assert(a@[found_idx as int] <= a@[i as int]);
                                assert(result@[prev_idx] <= a@[i as int]);
                                
                                if result@[prev_idx] == a@[i as int] {
                                    assert(false);
                                } else {
                                    assert(result@[prev_idx] < a@[i as int]);
                                }
                            }
                        }
                    }
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