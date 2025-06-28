use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool) 
    ensures 
        result <==> (
            (a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)) || 
            (exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])
        )
{
    let mut i: usize = 0;
    
    while i < a.len() && i < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= i <= b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i
    {
        if a[i] < b[i] {
            // Found first differing position where a[i] < b[i]
            
            // Prove subrange equality up to position i
            assert(a@.subrange(0, i as int) =~= b@.subrange(0, i as int)) by {
                let k = i as int;
                assert(a@.subrange(0, k).len() == k);
                assert(b@.subrange(0, k).len() == k);
                assert(forall|j: int| 0 <= j < k ==> {
                    &&& j < i
                    &&& a@.subrange(0, k)[j] == a@[j]
                    &&& b@.subrange(0, k)[j] == b@[j]
                    &&& a@[j] == b@[j]
                });
            };
            
            // This satisfies the exists clause
            assert(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k]) by {
                let k = i as int;
                assert({
                    &&& 0 <= k < a.len()
                    &&& k < b.len()
                    &&& a@.subrange(0, k) == b@.subrange(0, k)
                    &&& a@[k] < b@[k]
                });
            };
            
            return true;
            
        } else if a[i] > b[i] {
            // Found first differing position where a[i] > b[i], so leq is false
            
            // Neither condition in the postcondition can be true
            assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int))) by {
                if a.len() <= b.len() {
                    let idx = i as int;
                    assert(idx < a.len());
                    assert(a@[idx] != b@[idx]);
                    assert(b@.subrange(0, a.len() as int)[idx] == b@[idx]);
                    assert(a@[idx] != b@.subrange(0, a.len() as int)[idx]);
                    assert(a@ != b@.subrange(0, a.len() as int));
                }
            };
            
            assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
                assert(forall|k: int| (0 <= k < a.len() && k < b.len()) ==> {
                    if k < i {
                        // Elements before i are equal
                        !(a@[k] < b@[k])
                    } else if k == i {
                        // At position i, a[i] > b[i]
                        !(a@[k] < b@[k])
                    } else { // k > i
                        // Subranges up to k can't be equal because they differ at position i
                        assert(k > i);
                        assert(a@.subrange(0, k)[i as int] == a@[i as int]);
                        assert(b@.subrange(0, k)[i as int] == b@[i as int]);
                        assert(a@[i as int] != b@[i as int]);
                        !(a@.subrange(0, k) == b@.subrange(0, k))
                    }
                });
            };
            
            return false;
        }
        i += 1;
    }
    
    // Exited loop: either i == a.len() or i == b.len() (or both)
    // All compared elements were equal
    
    if i == a.len() {
        // We've processed all of a
        if a.len() <= b.len() {
            // a is a prefix of b (or they're equal)
            
            // Prove a@ == b@.subrange(0, a.len())
            assert(a@ =~= b@.subrange(0, a.len() as int)) by {
                let alen = a.len() as int;
                assert(a@.len() == alen);
                assert(b@.subrange(0, alen).len() == alen);
                assert(forall|j: int| 0 <= j < alen ==> {
                    &&& j < i  // because i == a.len()
                    &&& a@[j] == b@[j]
                    &&& b@.subrange(0, alen)[j] == b@[j]
                });
            };
            
            return true;
        } else {
            // a.len() > b.len(), so a cannot be lexicographically <= b
            assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)));
            
            // Second condition also fails because we've compared all elements up to b.len()
            // and they were equal, so no position where a[k] < b[k]
            assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
                assert(forall|k: int| (0 <= k < a.len() && k < b.len()) ==> {
                    // k < b.len() and i == b.len(), so k < i
                    assert(k < i);
                    assert(a@[k] == b@[k]);
                    !(a@[k] < b@[k])
                });
            };
            
            return false;
        }
    } else {
        // i == b.len() and i < a.len()
        // This means b is shorter than a, and all compared elements were equal
        // So a cannot be <= b
        assert(i == b.len());
        assert(i < a.len());
        assert(a.len() > b.len());
        
        // First condition fails
        assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)));
        
        // Second condition fails because all compared elements were equal
        assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
            a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
            assert(forall|k: int| (0 <= k < a.len() && k < b.len()) ==> {
                // k < b.len() and i == b.len(), so k < i
                assert(k < i);
                assert(a@[k] == b@[k]);
                !(a@[k] < b@[k])
            });
        };
        
        return false;
    }
}

fn test_leq() -> (result: int)
    ensures result == 0
{
    // Test cases to verify the function works correctly
    let a1: Vec<int> = Vec::new();
    let b1: Vec<int> = Vec::new();
    let result1 = leq(a1, b1);
    assert(result1); // empty vectors are equal
    
    0
}

}