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

// Helper lemma for bounds
proof fn lemma_bounds(i: int, n: int, len: int)
    requires 0 <= i, i + n <= len, n > 0
    ensures 
        0 <= i + n / 2 < len,
        i <= i + n / 2 <= i + n,
        0 <= i <= i + n / 2 <= len
{
    assert(n / 2 >= 0);
    assert(i + n / 2 <= i + n);
    assert(i + n / 2 < i + n) by {
        if n == 1 {
            assert(n / 2 == 0);
            assert(i + n / 2 == i);
            assert(i < i + 1);
        } else {
            assert(n >= 2);
            assert(n / 2 >= 1);
            assert(n / 2 < n);
            assert(i + n / 2 < i + n);
        }
    };
}

// Helper lemma for sortedness preservation
proof fn lemma_sortedness_subarray(a: Vec<int>, i: int, n: int, start: int, len: int)
    requires 
        forall|p: int, q: int| i <= p < q < i + n ==> a.spec_index(p) <= a.spec_index(q),
        i <= start,
        start + len <= i + n
    ensures
        forall|p: int, q: int| start <= p < q < start + len ==> a.spec_index(p) <= a.spec_index(q)
{
    // The proof follows directly from the transitivity of the ordering
}

fn Search2PowRecursive(a: Vec<int>, i: int, n: int, x: int) -> (k: int)
    requires
        0 <= i <= i + n <= a.len(),
        forall|p: int, q: int| i <= p < q < i + n ==> a.spec_index(p) <= a.spec_index(q),
        Is2Pow(n + 1),
        n >= 0
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
        lemma_bounds(i, n, a.len() as int);
        lemma_sortedness_subarray(a, i, n, i, n / 2);
        lemma_sortedness_subarray(a, i, n, mid, n / 2);
        
        assert(Is2Pow(n / 2 + 1));
        assert(0 <= i <= i + n / 2 <= a.len());
        assert(0 <= mid <= mid + n / 2 <= a.len());
        assert(mid == i + n / 2);
        assert(mid + n / 2 == i + n);
        assert(n / 2 >= 0);
    }
    
    if a[mid as usize] < x {
        // Search in the right half
        let result = Search2PowRecursive(a, mid, n / 2, x);
        
        proof {
            // Prove that all elements from i to mid are < x
            assert(forall|r: int| i <= r < mid ==> a.spec_index(r) < x) by {
                if exists|r: int| i <= r < mid && !(a.spec_index(r) < x) {
                    let r = choose|r: int| i <= r < mid && !(a.spec_index(r) < x);
                    assert(a.spec_index(r) >= x);
                    assert(a.spec_index(r) <= a.spec_index(mid));
                    assert(a.spec_index(mid) < x);
                    assert(false);
                }
            };
            
            // From postcondition of recursive call: mid <= result <= mid + n/2
            assert(mid <= result <= mid + n / 2);
            assert(forall|r: int| mid <= r < result ==> a.spec_index(r) < x);
            
            // Combine the two ranges
            assert(forall|r: int| i <= r < result ==> a.spec_index(r) < x) by {
                if exists|r: int| i <= r < result && !(a.spec_index(r) < x) {
                    let r = choose|r: int| i <= r < result && !(a.spec_index(r) < x);
                    if i <= r < mid {
                        assert(a.spec_index(r) < x);
                        assert(false);
                    } else {
                        assert(mid <= r < result);
                        assert(a.spec_index(r) < x);
                        assert(false);
                    }
                }
            };
            
            // Elements from result onwards are >= x
            assert(forall|r: int| result <= r < i + n ==> a.spec_index(r) >= x) by {
                if exists|r: int| result <= r < i + n && !(a.spec_index(r) >= x) {
                    let r = choose|r: int| result <= r < i + n && !(a.spec_index(r) >= x);
                    assert(result <= r < mid + n / 2);
                    assert(a.spec_index(r) >= x); // from recursive call postcondition
                    assert(false);
                }
            };
        }
        
        result
    } else {
        // Search in the left half
        let result = Search2PowRecursive(a, i, n / 2, x);
        
        proof {
            // From postcondition of recursive call
            assert(i <= result <= i + n / 2);
            assert(forall|r: int| i <= r < result ==> a.spec_index(r) < x);
            
            // Prove elements from mid onwards are >= x
            assert(forall|r: int| mid <= r < i + n ==> a.spec_index(r) >= x) by {
                if exists|r: int| mid <= r < i + n && !(a.spec_index(r) >= x) {
                    let r = choose|r: int| mid <= r < i + n && !(a.spec_index(r) >= x);
                    assert(a.spec_index(r) < x);
                    assert(a.spec_index(mid) <= a.spec_index(r));
                    assert(a.spec_index(mid) >= x);
                    assert(false);
                }
            };
            
            // Combine to show elements from result onwards are >= x
            assert(forall|r: int| result <= r < i + n ==> a.spec_index(r) >= x) by {
                if exists|r: int| result <= r < i + n && !(a.spec_index(r) >= x) {
                    let r = choose|r: int| result <= r < i + n && !(a.spec_index(r) >= x);
                    if result <= r < i + n / 2 {
                        // This contradicts the postcondition of the recursive call
                        assert(a.spec_index(r) >= x);
                        assert(false);
                    } else {
                        assert(i + n / 2 <= r < i + n);
                        assert(mid <= r < i + n);
                        assert(a.spec_index(r) >= x);
                        assert(false);
                    }
                }
            };
        }
        
        result
    }
}

}