// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Gauss(n: int) -> (sum: int)
    requires
        n >= 0
    ensures
        sum == n*(n+1)/2     //
{
    return 0;
}

}