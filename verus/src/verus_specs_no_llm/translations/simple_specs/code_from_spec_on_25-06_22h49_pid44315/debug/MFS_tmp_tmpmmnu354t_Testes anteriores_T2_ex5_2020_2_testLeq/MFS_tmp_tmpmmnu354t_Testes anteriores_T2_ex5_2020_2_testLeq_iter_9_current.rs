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
            // Found first position where a[i] < b[i]
            assert(a@.subrange(0, i as int) == b@.subrange(0, i as int)) by {
                assert(a@.subrange(0, i as int).len() == i);
                assert(b@.subrange(0, i as int).len() == i);
                assert(forall|j: int| 0 <= j < i ==> {
                    a@.subrange(0, i as int)[j] == a@[j] &&
                    b@.subrange(0, i as int)[j] == b@[j] &&
                    a@[j] == b@[j]
                });
            }
            
            assert(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k]) by {
                assert(0 <= i < a.len());
                assert(i < b.len());
                assert(a@.subrange(0, i as int) == b@.subrange(0, i as int));
                assert(a@[i as int] < b@[i as int]);
            }
            
            return true;
            
        } else if a[i] > b[i] {
            // Found first position where a[i] > b[i]
            assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int))) by {
                if a.len() <= b.len() {
                    assert(i < a.len());
                    assert(a@[i as int] > b@[i as int]);
                    assert(b@.subrange(0, a.len() as int)[i as int] == b@[i as int]);
                    assert(a@[i as int] != b@.subrange(0, a.len() as int)[i as int]);
                }
            }
            
            assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
                assert(forall|k: int| 0 <= k < a.len() && k < b.len() ==> {
                    if k < i {
                        a@[k] == b@[k]
                    } else if k == i {
                        a@[k] > b@[k]
                    } else {
                        // k > i, so subranges can't be equal since they differ at position i
                        assert(i < k);
                        assert(a@.subrange(0, k)[i as int] == a@[i as int]);
                        assert(b@.subrange(0, k)[i as int] == b@[i as int]);
                        assert(a@[i as int] != b@[i as int]);
                        a@.subrange(0, k) != b@.subrange(0, k)
                    }
                });
            }
            
            return false;
        }
        i = i + 1;
    }
    
    // Loop ended: all compared elements are equal
    if i == a.len() {
        // Processed all elements of a
        if a.len() <= b.len() {
            // a is prefix of b or they're equal
            assert(a@ == b@.subrange(0, a.len() as int)) by {
                assert(a@.len() == a.len());
                assert(b@.subrange(0, a.len() as int).len() == a.len());
                assert(forall|j: int| 0 <= j < a.len() ==> {
                    j < i && // since i == a.len()
                    a@[j] == b@[j] &&
                    b@.subrange(0, a.len() as int)[j] == b@[j]
                });
            }
            return true;
        } else {
            // a.len() > b.len(), so a cannot be <= b
            assert(a.len() > b.len());
            assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)));
            
            assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
                assert(forall|k: int| 0 <= k < a.len() && k < b.len() ==> {
                    k < b.len() &&
                    k < i && // since i == b.len() when we exit the loop
                    a@[k] == b@[k]
                });
            }
            return false;
        }
    } else {
        // i == b.len() and i < a.len()
        assert(i == b.len());
        assert(i < a.len());
        assert(a.len() > b.len());
        
        assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)));
        
        assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
            a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
            assert(forall|k: int| 0 <= k < a.len() && k < b.len() ==> {
                k < b.len() &&
                k < i && // since i == b.len()
                a@[k] == b@[k]
            });
        }
        
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