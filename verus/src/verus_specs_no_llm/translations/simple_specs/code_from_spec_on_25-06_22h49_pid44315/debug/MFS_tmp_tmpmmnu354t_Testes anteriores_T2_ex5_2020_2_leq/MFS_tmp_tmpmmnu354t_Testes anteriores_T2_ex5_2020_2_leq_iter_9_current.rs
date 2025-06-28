use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to compare slices
spec fn slices_equal(a: Vec<int>, b: Vec<int>, end: int) -> bool {
    end >= 0 && end <= a.len() && end <= b.len() &&
    forall|j: int| 0 <= j < end ==> a[j] == b[j]
}

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures
        result <==> (a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)) || (exists|k| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k])
{
    let mut i = 0;
    
    while i < a.len() && i < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= i <= b.len(),
            forall|j: int| 0 <= j < i ==> a[j] == b[j],
    {
        if a[i] < b[i] {
            // Found position where a[i] < b[i]
            assert(exists|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k]) by {
                assert(0 <= i < a.len() && i < b.len());
                assert(a[i] < b[i]);
                
                // Prove that subarrays up to i are equal
                assert(a@.subrange(0, i as int) =~= b@.subrange(0, i as int)) by {
                    assert(forall|j: int| 0 <= j < i ==> a@.subrange(0, i as int)[j] == a@[j]);
                    assert(forall|j: int| 0 <= j < i ==> b@.subrange(0, i as int)[j] == b@[j]);
                    assert(forall|j: int| 0 <= j < i ==> a@.subrange(0, i as int)[j] == b@.subrange(0, i as int)[j]);
                }
            }
            return true;
        } else if a[i] > b[i] {
            // Found position where a[i] > b[i], so leq is false
            proof {
                // No k can satisfy the condition since we found a[i] > b[i]
                assert(forall|k: int| 0 <= k < i ==> a[k] == b[k]);
                assert(a[i] > b[i]);
                
                // First part of disjunction is false
                if a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int) {
                    assert(a@[i as int] == b@.subrange(0, a.len() as int)[i as int]);
                    assert(a@[i as int] == b@[i as int]);
                    assert(a[i] == b[i]);
                    assert(false);
                }
                
                // Second part is false
                if exists|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k] {
                    let witness = choose|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k];
                    if witness < i {
                        assert(a[witness] == b[witness]);
                        assert(a[witness] < b[witness]);
                        assert(false);
                    } else if witness == i {
                        assert(a[i] < b[i]);
                        assert(a[i] > b[i]);
                        assert(false);
                    } else {
                        // witness > i, but we know elements 0..i are equal and a[i] > b[i]
                        assert(!(a@.subrange(0, witness) == b@.subrange(0, witness))) by {
                            assert(a@.subrange(0, witness)[i as int] == a@[i as int]);
                            assert(b@.subrange(0, witness)[i as int] == b@[i as int]);
                            assert(a@[i as int] > b@[i as int]);
                        }
                        assert(false);
                    }
                }
            }
            return false;
        }
        i += 1;
    }
    
    // If we reach here, all compared elements are equal
    let result = a.len() <= b.len();
    
    if result {
        // a.len() <= b.len() and a is a prefix of b
        assert(a.len() <= b.len());
        
        proof {
            assert(i >= a.len() || i >= b.len());
            assert(a.len() <= b.len());
            assert(i >= a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> a[j] == b[j]);
            
            assert(a@ =~= b@.subrange(0, a.len() as int)) by {
                assert(a@.len() == a.len());
                assert(b@.subrange(0, a.len() as int).len() == a.len());
                assert(forall|j: int| 0 <= j < a.len() ==> a@[j] == a[j as usize]);
                assert(forall|j: int| 0 <= j < a.len() ==> b@.subrange(0, a.len() as int)[j] == b@[j]);
                assert(forall|j: int| 0 <= j < a.len() ==> a@[j] == b@.subrange(0, a.len() as int)[j]);
            }
        }
    } else {
        // a.len() > b.len()
        proof {
            assert(a.len() > b.len());
            assert(i >= b.len());
            
            // First part of disjunction is false
            assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)));
            
            // Second part is false because no such k exists
            assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k])) by {
                // We compared all elements up to b.len() and found them equal
                assert(forall|j: int| 0 <= j < b.len() ==> a[j] == b[j]);
                
                if exists|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k] {
                    let witness = choose|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k];
                    assert(0 <= witness < b.len());
                    assert(a[witness] == b[witness]);
                    assert(a[witness] < b[witness]);
                    assert(false);
                }
            }
        }
    }
    
    result
}

}