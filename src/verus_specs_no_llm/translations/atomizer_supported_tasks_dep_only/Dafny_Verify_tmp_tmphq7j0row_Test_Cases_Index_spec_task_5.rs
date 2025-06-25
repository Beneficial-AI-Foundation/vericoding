// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MaxSum(x: int, y: int) -> s: int, m: int
    ensures s == x + y,
            m == if x >= y then x else y
{
}

}