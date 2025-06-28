use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Is2Pow(n: int) -> bool {
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && Is2Pow(n / 2)
    }
}

// Helper lemma to prove properties about powers of 2
proof fn lemma_2pow_div(n: int)
    requires Is2Pow(n + 1), n > 0
    ensures Is2Pow(n / 2 + 1)
{
    if n == 1 {
        assert(n / 2 + 1 == 1);
        assert(Is2Pow(1));
    } else {
        assert((n + 1) % 2 == 0);
        assert(Is2Pow((n + 1) / 2));
        
        // For n > 1 and n + 1 being a power of 2, n + 1 must be even
        // This means n is odd, so n / 2 (integer division) = (n - 1) / 2
        // We need to show that n / 2 + 1 = (n + 1) / 2
        assert(n % 2 == 1); // n is odd since n + 1 is even
        assert(n / 2 + 1 == (n + 1) / 2);
        assert(Is2Pow(n / 2 + 1));
    }
}

fn Search2PowRecursive(a: Vec<int>, i: int, n: int, x: int) -> (k: int)
    requires
        0 <= i <= i + n <= a.len(),
        forall|p: int, q: int| i <= p < q < i + n ==> a.spec_index(p) <= a.spec_index(q),
        Is2Pow(n + 1)
    ensures
        i <= k <= i + n,
        forall|r: int| i <= r < k ==> a.spec_index(r) < x,
        forall|r: int| k <= r < i + n ==> a.spec_index(r) >= x
    decreases n
{
    if n == 0 {
        return i;
    }
    
    let mid = i + n / 2;
    
    proof {
        lemma_2pow_div(n);
        assert(Is2Pow(n / 2 + 1));
        assert(0 <= i <= i + n / 2 <= a.len());
        assert(0 <= mid <= mid + n / 2 <= a.len());
        assert(mid == i + n / 2);
        assert(mid + n / 2 == i + n);
    }
    
    if a[mid as usize] < x {
        // Search in the right half
        let result = Search2PowRecursive(a, mid, n / 2, x);
        
        proof {
            // Prove that all elements from i to result are < x
            assert(forall|r: int| i <= r < mid ==> a.spec_index(r) < x) by {
                assert(forall|r: int| i <= r < mid ==> a.spec_index(r) <= a.spec_index(mid)) by {
                    assert(forall|p: int, q: int| i <= p < q < i + n ==> a.spec_index(p) <= a.spec_index(q));
                }
                assert(a.spec_index(mid) < x);
            }
            
            assert(forall|r: int| mid <= r < result ==> a.spec_index(r) < x);
            
            assert(forall|r: int| i <= r < result ==> a.spec_index(r) < x) by {
                assert(forall|r: int| i <= r < mid ==> a.spec_index(r) < x);
                assert(forall|r: int| mid <= r < result ==> a.spec_index(r) < x);
            }
            
            assert(forall|r: int| result <= r < i + n ==> a.spec_index(r) >= x) by {
                assert(forall|r: int| result <= r < mid + n / 2 ==> a.spec_index(r) >= x);
                assert(mid + n / 2 == i + n);
            }
        }
        
        result
    } else {
        // Search in the left half
        let result = Search2PowRecursive(a, i, n / 2, x);
        
        proof {
            assert(forall|r: int| i <= r < result ==> a.spec_index(r) < x);
            
            assert(forall|r: int| result <= r < i + n ==> a.spec_index(r) >= x) by {
                assert(forall|r: int| result <= r < i + n / 2 ==> a.spec_index(r) >= x);
                
                assert(forall|r: int| i + n / 2 <= r < i + n ==> a.spec_index(r) >= x) by {
                    assert(forall|r: int| mid <= r < i + n ==> a.spec_index(r) >= a.spec_index(mid)) by {
                        assert(forall|p: int, q: int| i <= p < q < i + n ==> a.spec_index(p) <= a.spec_index(q));
                    }
                    assert(a.spec_index(mid) >= x);
                    assert(mid == i + n / 2);
                }
                
                assert(forall|r: int| result <= r < i + n ==> a.spec_index(r) >= x) by {
                    assert(result <= i + n / 2);
                }
            }
        }
        
        result
    }
}

}