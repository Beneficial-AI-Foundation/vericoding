// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn StarNumber(n: int) -> (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
}

}