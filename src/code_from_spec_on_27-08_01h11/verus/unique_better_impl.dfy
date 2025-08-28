use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_unique(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] != s[j]
}

spec fn is_strictly_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] < s[j]
}

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] <= s[j]
}

proof fn unique_and_sorted_implies_strictly_sorted(s: Seq<i32>)
    requires 
        is_unique(s),
        is_sorted(s),
    ensures 
        is_strictly_sorted(s),
{
    assert forall|i: int, j: int| 0 <= i && i < j && j < s.len() implies s[i] < s[j] by {
        if 0 <= i && i < j && j < s.len() {
            assert(s[i] <= s[j]);
            if s[i] == s[j] {
                assert(s[i] == s[j] && i != j);
                assert(false);
            }
        }
    }
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
    let mut i = 0usize;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result@[k], result@[l]]
                0 <= k && k < l && l < result.len() ==> result@[k] < result@[l],
            forall|k: int| 0 <= k && k < result.len() ==> 
                exists|j: int| 0 <= j && j < i && a[j] == result@[k],
            forall|k: int| 0 <= k && k < result.len() ==> 
                forall|j: int| 0 <= j && j < result.len() && j != k ==> result@[j] != result@[k],
            forall|j: int| 0 <= j && j < i ==> 
                (exists|k: int| 0 <= k && k < result.len() && result@[k] == a[j]) ||
                (exists|k: int| 0 <= k && k < j && a[k] == a[j]),
    {
        let mut found = false;
        let mut j = 0usize;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found == exists|k: int| 0 <= k && k < j && result@[k] == a[i as int],
                forall|k: int, l: int|
                    #![trigger result@[k], result@[l]]
                    0 <= k && k < l && l < result.len() ==> result@[k] < result@[l],
        {
            if result[j] == a[i] {
                found = true;
            }
            j += 1usize;
        }
        
        if !found {
            result.push(a[i]);
            proof {
                let old_result = result@.drop_last();
                assert(result@.len() == old_result.len() + 1);
                assert(result@[result@.len() - 1] == a[i as int]);
                
                assert forall|k: int, l: int|
                    #![trigger result@[k], result@[l]]
                    0 <= k && k < l && l < result.len() implies result@[k] < result@[l] by {
                    if 0 <= k && k < l && l < result.len() {
                        if l < result@.len() - 1 {
                            assert(result@[k] < result@[l]);
                        } else if k < result@.len() - 1 {
                            assert(l == result@.len() - 1);
                            assert(result@[l] == a[i as int]);
                            assert(result@[k] == old_result[k]);
                            
                            assert(exists|n: int| 0 <= n && n < i && a[n] == result@[k]);
                            assert(forall|n: int| 0 <= n && n < i ==> a[n] <= a[i as int]);
                            assert(result@[k] <= a[i as int]);
                            assert(result@[k] < result@[l]);
                        }
                    }
                }
            }
        }
        
        i += 1usize;
    }
    
    result
}
// </vc-code>

fn main() {}
}