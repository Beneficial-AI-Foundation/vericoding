// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsNonPrime(n: int) -> (result: bool)
    requires
        n >= 2
    ensures
        result <==> (exists k :: 2 <= k < n && n % k == 0)
{
    return false;
}

}