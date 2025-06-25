// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Index(n: int) -> (i: int)
    requires 1 <= n
    ensures 0 <= i < n
{
}

}