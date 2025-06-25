// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ComputeIsEven(x: int) -> (is_even: bool)
    ensures (x % 2 == 0)==is_even
{
}

}