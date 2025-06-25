// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn TestDouble(val: int) -> (val2: int)
    ensures val2 == Double(val)
{
}

}