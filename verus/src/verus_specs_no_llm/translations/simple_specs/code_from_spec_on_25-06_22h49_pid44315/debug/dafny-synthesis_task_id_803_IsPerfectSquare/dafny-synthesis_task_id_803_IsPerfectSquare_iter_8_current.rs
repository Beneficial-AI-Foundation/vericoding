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
    
    assert(forall a: int :: 0 <= a && a * a == n ==> false) by {
        let a = choose |a: int| 0 <= a && a * a == n;
        if a == 0 {
            // Then a * a == 0, but n > 0, contradiction
            assert(a * a == 0);
            assert(n > 0);
            assert(false);
        } else if 1 <= a && a < i {
            // From invariant: all j in [1, i) have j * j < n
            // But a is in [1, i) and a * a == n, contradiction
            assert(a * a < n);  // from invariant
            assert(a * a == n);  // from assumption
            assert(false);
        } else if a >= i {
            // a >= i, and we know i * i > n
            // Since a >= i and both are positive, a * a >= i * i > n
            assert(a >= i);
            assert(i >= 1);
            assert(a >= 1);
            
            // For positive integers, if a >= i then a * a >= i * i
            assert(a * a >= i * i) by {
                if a == i {
                    assert(a * a == i * i);
                } else {
                    assert(a > i);
                    // Since a and i are positive and a > i, we have a * a > i * i
                    assert(a >= i + 1);
                    // Use the fact that for positive x, y: x >= y + 1 ==> x * x >= (y + 1) * (y + 1) > y * y
                    assert(a * a >= (i + 1) * (i + 1));
                    assert((i + 1) * (i + 1) == i * i + 2 * i + 1);
                    assert(2 * i + 1 >= 3);  // since i >= 1
                    assert((i + 1) * (i + 1) >= i * i + 3);
                    assert((i + 1) * (i + 1) > i * i);
                    assert(a * a > i * i);
                }
            };
            
            assert(i * i > n);  // from loop exit condition
            assert(a * a >= i * i);  // proven above
            assert(a * a > n);  // since a * a >= i * i > n
            assert(a * a == n);  // from assumption
            assert(false);
        } else {
            // This case is a < 1 and a != 0, but a >= 0, so impossible
            assert(a < 1);
            assert(a != 0);
            assert(a >= 0);
            assert(false);
        }
    };
    
    return false;
}

}