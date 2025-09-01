use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// Helper lemma to prove that if an element is in the result, it's in the original array
proof fn lemma_in_result_in_array(a: Seq<i32>, result: Seq<i32>, k: int)
    requires
        0 <= k < result.len(),
        forall|i: int| 0 <= i < result.len() ==> in_array(a, result[i]),
    ensures
        in_array(a, result[k]),
{
    assert(0 <= k < result.len());
    assert(in_array(a, result[k]));
}

// Helper to check if a value is already in a sequence up to a certain index
spec fn in_seq_up_to(s: Seq<i32>, x: i32, up_to: int) -> bool {
    exists|j: int| 0 <= j < up_to && j < s.len() && s[j] == x
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| #![trigger result@[k]] 0 <= k < result.len() ==> in_array(a@, result@[k]),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result@[k] != result@[l],
        decreases a.len() - i,
    {
        let current = a[i];
        let mut found = false;
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                j <= result.len(),
                found ==> exists|k: int| 0 <= k < j && result@[k] == current,
                !found ==> forall|k: int| 0 <= k < j ==> result@[k] != current,
            decreases result.len() - j,
        {
            if result[j] == current {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if !found {
            assert(forall|k: int| 0 <= k < result.len() ==> result@[k] != current);
            result.push(current);
            
            assert(result@[result.len() - 1] == current);
            assert(a@[i as int] == current);
            assert(exists|m: int| 0 <= m < a@.len() && a@[m] == current);
            assert(in_array(a@, current));
            
            assert forall|k: int| #![trigger result@[k]] 0 <= k < result.len() implies in_array(a@, result@[k]) by {
                if k == result.len() - 1 {
                    assert(result@[k] == current);
                    assert(in_array(a@, current));
                } else {
                    assert(0 <= k < result.len() - 1);
                }
            }
            
            assert forall|k: int, l: int| 0 <= k < l < result.len() implies result@[k] != result@[l] by {
                if l == result.len() - 1 {
                    assert(result@[l] == current);
                    assert(k < result.len() - 1);
                    assert(forall|m: int| 0 <= m < result.len() - 1 ==> result@[m] != current);
                    assert(result@[k] != current);
                    assert(result@[k] != result@[l]);
                }
            }
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}