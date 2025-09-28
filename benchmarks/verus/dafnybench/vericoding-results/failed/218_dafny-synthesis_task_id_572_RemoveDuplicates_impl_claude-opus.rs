use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if a sequence contains an element up to a given index
spec fn contains_up_to(s: Seq<i32>, x: i32, up_to: int) -> bool {
    exists|j: int| 0 <= j < up_to && s[j] == x
}

// Helper lemma to prove that if an element exists in the original array,
// and we've processed it, then it's in the result
proof fn lemma_contains_preservation(a: &[i32], result: &Vec<i32>, i: int)
    requires
        0 <= i <= a.len(),
        forall|x: i32| #[trigger] result@.contains(x) <==> contains_up_to(a@, x, i),
        forall|j: int, k: int| 0 <= j < k < result.len() ==> result@[j] != result@[k],
    ensures
        forall|x: i32| result@.contains(x) <==> exists|j: int| 0 <= j < i && a[j] == x,
{
    assert forall|x: i32| result@.contains(x) <==> exists|j: int| 0 <= j < i && a[j] == x by {
        if result@.contains(x) {
            // If x is in result, then by our invariant, it's in a[0..i)
            assert(contains_up_to(a@, x, i));
        }
        if exists|j: int| 0 <= j < i && a[j] == x {
            // If x is in a[0..i), then by our invariant, it's in result
            assert(contains_up_to(a@, x, i));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: i32| #[trigger] result@.contains(x) <==> contains_up_to(a@, x, i as int),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result@[j] != result@[k],
        decreases a.len() - i
    {
        let current = a[i];
        
        // Check if current element is already in result
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found <==> exists|k: int| 0 <= k < j && result@[k] == current,
            decreases result.len() - j
        {
            if result[j] == current {
                found = true;
                assert(result@[j as int] == current);
            }
            j = j + 1;
        }
        
        if !found {
            let ghost old_result_view = result@;
            result.push(current);
            
            // Prove the invariants are maintained after push
            assert forall|x: i32| #[trigger] result@.contains(x) <==> contains_up_to(a@, x, (i + 1) as int) by {
                if x == current {
                    assert(result@.last() == current);
                    assert(result@.contains(x));
                    assert(a@[i as int] == current);
                    assert(contains_up_to(a@, x, (i + 1) as int));
                } else {
                    if result@.contains(x) {
                        // x is in the new result
                        assert(result@ == old_result_view.push(current));
                        if old_result_view.contains(x) {
                            // x was in the old result, so it was seen up to i
                            assert(contains_up_to(a@, x, i as int));
                            assert(contains_up_to(a@, x, (i + 1) as int));
                        } else {
                            // x wasn't in old result but is in new result
                            // This can only happen if x == current, but we already handled that
                            assert(x == result@.last());
                            assert(x == current);
                            assert(false); // contradiction
                        }
                    }
                    if contains_up_to(a@, x, (i + 1) as int) {
                        if contains_up_to(a@, x, i as int) {
                            // x was seen up to i, so it's in old_result_view
                            assert(old_result_view.contains(x));
                            assert(result@.contains(x));
                        } else {
                            // x is only at position i
                            assert(exists|k: int| i <= k < (i + 1) && a@[k] == x);
                            assert(a@[i as int] == x);
                            assert(x == current);
                            // But we're in the case where x != current, contradiction
                            assert(false);
                        }
                    }
                }
            }
            
            // Prove uniqueness is maintained
            assert forall|j: int, k: int| 0 <= j < k < result.len() implies result@[j] != result@[k] by {
                if j < old_result_view.len() && k < old_result_view.len() {
                    // Both indices in old result
                    assert(result@[j] == old_result_view[j]);
                    assert(result@[k] == old_result_view[k]);
                    assert(result@[j] != result@[k]);
                } else if j < old_result_view.len() && k == old_result_view.len() {
                    // j in old result, k is the new element
                    assert(result@[k] == current);
                    assert(result@[j] == old_result_view[j]);
                    assert(!found);
                    assert(!old_result_view.contains(current));
                    assert(result@[j] != current);
                    assert(result@[j] != result@[k]);
                }
            }
        } else {
            // Current element already exists, just prove invariant is maintained
            assert forall|x: i32| #[trigger] result@.contains(x) <==> contains_up_to(a@, x, (i + 1) as int) by {
                if result@.contains(x) {
                    assert(contains_up_to(a@, x, i as int));
                    assert(contains_up_to(a@, x, (i + 1) as int));
                }
                if contains_up_to(a@, x, (i + 1) as int) {
                    if x == current {
                        assert(found);
                        assert(result@.contains(current));
                        assert(result@.contains(x));
                    } else {
                        if contains_up_to(a@, x, i as int) {
                            assert(result@.contains(x));
                        } else {
                            assert(exists|k: int| i <= k < (i + 1) && a@[k] == x);
                            assert(a@[i as int] == x);
                            assert(x == current);
                            // But we're in the case where x != current, contradiction
                            assert(false);
                        }
                    }
                }
            }
        }
        
        i = i + 1;
    }
    
    // Final proof that postconditions are satisfied
    proof {
        lemma_contains_preservation(a, &result, a.len() as int);
    }
    
    result
}
// </vc-code>

fn main() {
}

}