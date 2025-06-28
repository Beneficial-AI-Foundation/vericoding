// Translated from Dafny
use builtin::*;
use builtin_macros::*;

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
    return false;
}

}