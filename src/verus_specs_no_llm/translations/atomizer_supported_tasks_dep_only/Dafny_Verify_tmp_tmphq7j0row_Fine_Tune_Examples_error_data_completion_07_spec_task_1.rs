// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main(n: int) -> a: int, b: int
    requires n >= 0
    ensures a + b == 3 * n
{
}

}