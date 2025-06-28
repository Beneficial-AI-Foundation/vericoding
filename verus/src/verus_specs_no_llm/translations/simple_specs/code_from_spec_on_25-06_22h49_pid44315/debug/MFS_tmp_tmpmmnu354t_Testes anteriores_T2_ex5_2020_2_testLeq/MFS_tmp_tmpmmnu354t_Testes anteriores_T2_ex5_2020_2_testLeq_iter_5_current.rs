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
    {
        if a[i] < b[i] {
            // Found first differing position where a[i] < b[i]
            assert(0 <= i < a.len() && i < b.len());
            assert(a@[i as int] < b@[i as int]);
            
            // Prove subrange equality up to position i
            assert(a@.subrange(0, i as int) == b@.subrange(0, i as int)) by {
                assert(a@.subrange(0, i as int).len() == i);
                assert(b@.subrange(0, i as int).len() == i);
                assert(forall|j: int| 0 <= j < i ==> {
                    a@.subrange(0, i as int)[j] == a@[j] == b@[j] == b@.subrange(0, i as int)[j]
                });
            };
            
            // This satisfies the exists clause
            assert(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k]) by {
                assert(0 <= i < a.len() && i < b.len() && 
                    a@.subrange(0, i as int) == b@.subrange(0, i as int) && a@[i as int] < b@[i as int]);
            };
            
            return true;
            
        } else if a[i] > b[i] {
            // Found first differing position where a[i] > b[i], so leq is false
            assert(a@[i as int] > b@[i as int]);
            
            // Neither condition in the postcondition can be true
            assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int))) by {
                assert(a@[i as int] != b@[i as int]);
                if a.len() <= b.len() {
                    assert(i < a.len());
                    assert(b@.subrange(0, a.len() as int)[i as int] == b@[i as int]);
                    assert(a@[i as int] != b@.subrange(0, a.len() as int)[i as int]);
                }
            };
            
            assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
                assert(forall|k: int| (0 <= k < a.len() && k < b.len()) ==> {
                    if k < i {
                        assert(a@[k] == b@[k]);
                        !(a@[k] < b@[k])
                    } else if k == i {
                        assert(a@[k] > b@[k]);
                        !(a@[k] < b@[k])
                    } else { // k > i
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
    
    if i == a.len() && a.len() <= b.len() {
        // a is a prefix of b (or they're equal)
        
        // Prove a@ == b@.subrange(0, a.len())
        assert(a@ == b@.subrange(0, a.len() as int)) by {
            assert(a@.len() == a.len());
            assert(b@.subrange(0, a.len() as int).len() == a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> {
                assert(j < i);
                assert(a@[j] == b@[j]);
                assert(b@.subrange(0, a.len() as int)[j] == b@[j]);
                a@[j] == b@.subrange(0, a.len() as int)[j]
            });
        };
        
        // First condition is satisfied
        true
        
    } else {
        // Either a.len() > b.len() or we found no difference but a is not a prefix
        
        // First condition fails
        assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)));
        
        // Second condition fails 
        assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
            a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
            assert(forall|k: int| (0 <= k < a.len() && k < b.len()) ==> {
                assert(k < i);
                assert(a@[k] == b@[k]);
                !(a@[k] < b@[k])
            });
        };
        
        false
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