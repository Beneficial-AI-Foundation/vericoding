// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Quotient(a: int, b: int) -> (result: int)
    requires b != 0
    ensures result == a / b
{
}

}