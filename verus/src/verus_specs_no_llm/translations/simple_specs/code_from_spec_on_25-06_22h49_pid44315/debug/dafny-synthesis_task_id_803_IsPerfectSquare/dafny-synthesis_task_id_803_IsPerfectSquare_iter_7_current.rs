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
    
    proof {
        assert forall |a: int| 0 <= a && a * a == n implies false by {
            if a == 0 {
                // Then a * a == 0, but n > 0
                assert(a * a == 0);
                assert(n > 0);
            } else if a >= 1 && a < i {
                // From invariant: all j in [1, i) have j * j < n
                // But a is in [1, i) and a * a == n, contradiction
                assert(a * a < n);  // from invariant
                assert(a * a == n);  // from assumption
            } else if a >= i {
                // a >= i, and we know i * i > n (loop exit condition)
                if a == i {
                    assert(a * a == i * i);
                    assert(i * i > n);
                    assert(a * a > n);
                    assert(a * a == n);
                } else {
                    // a > i >= 1
                    assert(a > i);
                    assert(a >= i + 1);
                    
                    // Prove that a * a > i * i for positive integers when a > i
                    assert(a * a > i * i) by {
                        assert(a >= i + 1);
                        assert(i >= 1);
                        // Since multiplication preserves order for positive numbers
                        // and a >= i + 1, we have a * a >= (i + 1) * (i + 1)
                        assert(a * a >= (i + 1) * (i + 1));
                        assert((i + 1) * (i + 1) == i * i + 2 * i + 1);
                        assert(2 * i + 1 >= 3);  // since i >= 1
                        assert((i + 1) * (i + 1) > i * i);
                    }
                    
                    assert(i * i > n);  // from loop exit condition
                    assert(a * a > i * i);  // proven above
                    assert(a * a > n);  // transitivity
                    assert(a * a == n);  // from assumption
                }
            }
            // All cases lead to contradiction
        }
    }
    
    return false;
}

}