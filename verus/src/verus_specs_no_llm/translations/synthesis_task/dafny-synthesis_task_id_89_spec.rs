// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn ClosestSmaller(n: int) -> (m: int)
    requires
        n > 0
    ensures
        m + 1 == n
{
    return 0;
}

}