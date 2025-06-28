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
            0 * 0 != n  // Since n > 0, and we know 0 * 0 = 0
    {
        if i * i == n {
            return true;
        }
        i = i + 1;
    }
    
    // At this point: i * i > n and no j in [1, i) has j * j == n
    // We need to prove no perfect square exists for n
    
    assert(forall a: int :: 0 <= a && a * a == n ==> false) by {
        // For any a >= 0 where a * a == n
        assert(forall a: int :: 0 <= a && a * a == n ==> {
            // Case 1: a == 0
            if a == 0 {
                // Then a * a == 0, but n > 0 (since we handled n == 0 case)
                0 == n && n > 0  // Contradiction
            }
            // Case 2: a >= 1 
            else {
                // We know a >= 1, so either a < i or a >= i
                if a < i {
                    // From invariant: all j in [1, i) have j * j < n
                    // But a is in [1, i) and a * a == n, contradiction
                    a * a < n && a * a == n  // Contradiction
                } else {
                    // a >= i, and we know i * i > n (loop exit condition)
                    // So a * a >= i * i > n, but a * a == n, contradiction
                    a * a >= i * i && i * i > n && a * a == n  // Contradiction
                }
            }
        });
    };
    
    return false;
}

}