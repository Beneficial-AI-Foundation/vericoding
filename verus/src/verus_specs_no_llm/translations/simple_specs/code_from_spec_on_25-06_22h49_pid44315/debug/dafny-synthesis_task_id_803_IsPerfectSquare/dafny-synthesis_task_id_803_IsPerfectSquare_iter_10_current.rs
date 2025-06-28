use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsPerfectSquare(n: int) -> (result: bool)
    requires
        n >= 0
    ensures
        result == true ==> (exists i: int :: 0 <= i <= n && i * i == n),
        result == false ==> (forall a: int :: 0 <= a && a * a == n ==> false)
{
    if n == 0 {
        return true;
    }
    
    let mut i = 1;
    while i * i <= n
        invariant
            1 <= i,
            forall j: int :: 1 <= j < i ==> j * j < n,
            n > 0
    {
        if i * i == n {
            return true;
        }
        i = i + 1;
    }
    
    // At this point: i * i > n and no j in [1, i) has j * j == n
    // We need to prove no perfect square exists for n
    
    assert(i * i > n);
    assert(forall j: int :: 1 <= j < i ==> j * j < n);
    
    // Prove the postcondition directly
    assert(forall a: int :: 0 <= a && a * a == n ==> false) by {
        // We'll prove this by contradiction for any arbitrary a
        // Case analysis on a
        
        // If a == 0, then a * a == 0, but n > 0
        assert(forall a: int :: a == 0 && a * a == n ==> false) by {
            // If a == 0, then a * a == 0, but n > 0, so contradiction
            assert(n > 0);
        };
        
        // If 1 <= a < i, then from invariant a * a < n, but we need a * a == n
        assert(forall a: int :: 1 <= a < i && a * a == n ==> false) by {
            // From invariant, any j in [1, i) has j * j < n
            // So if a is in [1, i) and a * a == n, we have a * a < n and a * a == n
        };
        
        // If a >= i, then a * a >= i * i > n, but we need a * a == n
        assert(forall a: int :: a >= i && a * a == n ==> false) by {
            assert(i * i > n);
            // For any a >= i >= 1, we have a * a >= i * i
            assert(forall a: int :: a >= i && i >= 1 ==> a * a >= i * i) by {
                // This follows from the fact that multiplication preserves order for non-negative integers
            };
            // So a * a >= i * i > n, contradicting a * a == n
        };
        
        // The only remaining case is a < 0, but our precondition says a >= 0
        // So we've covered all cases where 0 <= a
    };
    
    false
}

}