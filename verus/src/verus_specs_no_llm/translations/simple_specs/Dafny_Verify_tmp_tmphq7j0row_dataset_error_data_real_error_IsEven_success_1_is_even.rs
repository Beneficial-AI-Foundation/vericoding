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

fn is_even(n: int) -> (r: bool)
    requires
        n >= 0
    ensures
        r <==> even(n)
{
    return false;
}

}