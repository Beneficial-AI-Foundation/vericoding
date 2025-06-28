// Translated from Dafny
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
        result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
{
    if n == 0 {
        return true;
    }
    
    let mut i = 1;
    while i * i <= n
        invariant
            1 <= i,
            forall j: int :: 1 <= j < i ==> j * j < n
    {
        if i * i == n {
            return true;
        }
        i = i + 1;
    }
    
    assert(i * i > n);
    assert(forall j: int :: 1 <= j < i ==> j * j < n);
    assert(forall a: int :: 0 < a*a < n ==> a*a != n) by {
        assert(forall a: int :: a >= 1 && a*a < n ==> a < i);
        assert(forall a: int :: a >= 1 && a*a < n ==> a*a != n);
    };
    
    return false;
}

}