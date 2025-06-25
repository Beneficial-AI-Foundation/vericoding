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

fn HasOppositeSign(a: int, b: int) -> (result: bool)
    ensures
        result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
    return false;
}

}