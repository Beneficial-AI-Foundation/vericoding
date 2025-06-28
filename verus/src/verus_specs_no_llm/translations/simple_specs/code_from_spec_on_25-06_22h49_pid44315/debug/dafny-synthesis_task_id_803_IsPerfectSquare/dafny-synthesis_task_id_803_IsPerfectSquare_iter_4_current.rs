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
    
    assert(forall a: int :: 0 <= a && a * a == n ==> false) by {
        assert(forall a: int :: 0 <= a && a * a == n ==> {
            if a == 0 {
                // Then a * a == 0, but n > 0 (from invariant)
                assert(a * a == 0);
                assert(n > 0);
                false
            } else if a >= 1 && a < i {
                // From invariant: all j in [1, i) have j * j < n
                // But a is in [1, i) and a * a == n, contradiction
                assert(a * a < n);  // from invariant
                assert(a * a == n);  // from assumption
                false
            } else {
                // a >= i, and we know i * i > n (loop exit condition)
                // So a * a >= i * i > n, but a * a == n, contradiction
                assert(a >= i);
                assert(a * a >= i * i);
                assert(i * i > n);
                assert(a * a == n);
                false
            }
        });
    };
    
    return false;
}

}