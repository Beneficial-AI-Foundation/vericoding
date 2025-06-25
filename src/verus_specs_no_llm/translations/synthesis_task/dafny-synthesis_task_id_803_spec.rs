// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsPerfectSquare(n: int) -> (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n and i * i == n),
            result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
{
}

}