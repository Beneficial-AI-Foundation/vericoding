// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn LastDigit(n: int) -> (d: int)
    requires n >= 0
    ensures 0 <= d < 10,
            n % 10 == d
{
}

}